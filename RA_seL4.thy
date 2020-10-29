theory RA_seL4
imports Main
begin

datatype PC = P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8 | P9 | P10 | P11 | P12 | P13 | P14 | Idle
datatype PC_SETUP = L1 | L2 | L3 | L4
type_synonym Time = nat
type_synonym Process = nat
type_synonym MRange = "nat \<times> nat"
type_synonym Mac = nat

datatype Cap = 
 CSCap Process  | VSCap Process  | TCBCap Process 
 | TCap | KeyCap  | EPCap | GrantCap | IQCap  | NetCap  | SendCap  | ReceiveCap | BadgeCap Process

datatype Object = P Process | INITTIME | KEY | IRQ | NONCE | MEM
datatype Predicate = Read | Write | Grant | Control | AsyncSend | Receive 
consts Policy :: "(Process \<times> Predicate \<times> Object) set"


consts P\<^sub>A :: Process
consts P\<^sub>1 :: Process
consts P\<^sub>N :: Process

definition "P_distinct \<equiv> P\<^sub>A \<noteq> P\<^sub>1 \<and>  P\<^sub>A \<noteq> P\<^sub>N \<and>  P\<^sub>N \<noteq> P\<^sub>1"


datatype Message =
           Req Time Mac MRange Process
         | Res Time Mac Mac
         | Empty

fun isReq :: "Message \<Rightarrow> bool" where
  "isReq (Req _ _ _ _) = True"
| "isReq _ = False"


fun isRes :: "Message \<Rightarrow> bool" where
    "isRes (Res _ _ _) = True"
  | "isRes _ = False"

fun getMTime :: "Message \<Rightarrow> Time " where
    "getMTime (Req t  _ _ _) =  t"
  | "getMTime (Res t  _ _) =  t"
  | "getMTime _ = 0 "

fun getMProcess :: "Message \<Rightarrow> Process option" where
    "getMProcess (Req _ _ _ p) = Some p"
  | "getMProcess (Res _ _ _) = None"
  | "getMProcess _ = None "

fun getMRange :: "Message \<Rightarrow> MRange option" where
    "getMRange (Req _ _ r _) = Some r"
   | "getMRange (Res _ _ _) = None"
   | "getMRange _ = None "
 
fun getFMac :: "Message \<Rightarrow> Mac " where
     "getFMac (Req _ fm _ _) =  fm"
   | "getFMac (Res _ fm _) =  fm"
   | "getFMac _ = 0 "

fun getSMac :: "Message \<Rightarrow> Mac option" where
    "getSMac (Req _ _ _ _) = None"
  | "getSMac (Res _ _ sm) = Some sm"
  | "getSMac _ = None "

record Message_req =
  time_req :: Time (*Treq, Tres, ...*)
  mac_req :: nat
  mrang_req :: MRange (*a'b'*)
  proc_req :: Process (*Pa, P1, ...*)

record Message_resp =
  time_resp :: Time (*Treq, Tres, ...*)
  (*proc_resp :: Process Pa, P1, ...*)
  mac1_resp :: nat
  mac2_resp :: nat

record CSpace_rec =
  Caps :: "Cap set"
  EP :: Message

record TCB_rec =
  VSpace :: nat
  CSpace :: CSpace_rec

record Proc_rec =
  TCB :: TCB_rec
  Mem :: MRange
  Priority :: nat
  Time :: nat
  Parent :: nat

record State =
 Procs :: "Process set"
 ProcRec :: "Process \<Rightarrow> Proc_rec"
 TInit :: nat
 Key :: nat
 Nonce :: nat
 irq :: bool
 pc :: PC
 policy :: "(Process \<times> Predicate \<times> Object) set"
(*Local*)
 rval :: "Message"
 l_time :: nat
 l_mac1 :: nat
 l_mac2 :: nat
 ep :: Message


definition "P_attest_prop s \<equiv> 
               P\<^sub>A\<in>Procs s 
             \<and> Priority ((ProcRec s) P\<^sub>A)  = 0
             \<and> Time ((ProcRec s) P\<^sub>A)  = TInit s
             \<and> Parent ((ProcRec s) P\<^sub>A)  = 0 
             \<and> Caps (CSpace (TCB ((ProcRec s) P\<^sub>A))) = 
                  {VSCap P\<^sub>A, CSCap P\<^sub>A, TCBCap P\<^sub>A, TCap, KeyCap , EPCap, GrantCap, IQCap, SendCap,BadgeCap P\<^sub>A, BadgeCap P\<^sub>N}"


definition "Spawned_prop p s \<equiv> 
            p \<noteq> P\<^sub>A \<and> p \<in> Procs s 
          \<and> Priority ((ProcRec s) p) > 0
          \<and> Time ((ProcRec s) p) > TInit s
          \<and> Caps (CSpace (TCB ((ProcRec s) p))) = {VSCap p, CSCap p, TCBCap p}"

definition "Net_prop p s \<equiv> 
            p \<noteq> P\<^sub>A \<and> p \<in> Procs s 
          \<and> Priority ((ProcRec s) p) > 0
          \<and> Time ((ProcRec s) p) > TInit s
          \<and> Caps (CSpace (TCB ((ProcRec s) p))) = {VSCap p, CSCap p, TCBCap p, NetCap, ReceiveCap, BadgeCap P\<^sub>N, BadgeCap P\<^sub>A}"

record SetupState = 
   ss_pc :: PC_SETUP

definition "CreateProcess tcb mem  pri t par\<equiv> 
             \<lparr>
              TCB = tcb,
              Mem = mem,
              Priority = pri,
              Time = t,
              Parent = par
             \<rparr>"


definition "CreateProcessTCB vs cs\<equiv> 
             \<lparr>
              VSpace = vs,
              CSpace = cs
             \<rparr>"


definition "CreateProcessCSpace caps \<equiv> 
             \<lparr>
                Caps = caps,
                EP = Empty
             \<rparr>"

  
definition "MAC data::nat \<equiv> SOME n. 1 \<le> n \<and> n \<le> data * data * data"

definition "getTime now \<equiv> SOME t . t > now"

definition update_pc :: "PC \<Rightarrow> State \<Rightarrow> State" ("`pc := _" [200])
  where 
  "update_pc v \<equiv> \<lambda> s. s \<lparr>pc := v\<rparr>"


definition update_local_ep :: "Message \<Rightarrow> State \<Rightarrow> State" ("`ep := _" [200])
  where 
  "update_local_ep v \<equiv> \<lambda> s. s \<lparr>ep := v\<rparr>"


definition update_irq :: "bool \<Rightarrow> State \<Rightarrow> State" ("`irq := _" [200])
  where 
  "update_irq v \<equiv> \<lambda> s. s \<lparr>irq := v\<rparr>"

definition update_rval :: "Message  \<Rightarrow> State \<Rightarrow> State" ("`rval := _" [200])
  where 
  "update_rval v \<equiv> \<lambda> s. s \<lparr>rval := v\<rparr>"

(*definition update_badge :: "bool \<Rightarrow> Proc_rec \<Rightarrow> Proc_rec" ("`badge := _" [100])
  where 
  "update_badge v \<equiv> \<lambda> s. s \<lparr>Badge := v\<rparr>"*)

definition update_time :: "Time \<Rightarrow> State \<Rightarrow> State" ("`time := _" [100])
  where 
  "update_time v \<equiv> \<lambda> s. s \<lparr>l_time := v\<rparr>"

definition update_mac1 :: "nat \<Rightarrow> State \<Rightarrow> State" ("`mac1 := _" [200])
  where 
  "update_mac1 v \<equiv> \<lambda> s. s \<lparr>l_mac1 := v\<rparr>"

definition update_mac2 :: "nat \<Rightarrow> State \<Rightarrow> State" ("`mac2 := _" [200])
  where 
  "update_mac2 v \<equiv> \<lambda> s. s \<lparr>l_mac2 := v\<rparr>"

definition update_nonce :: "nat \<Rightarrow> State \<Rightarrow> State" ("`nonce := _" [200])
  where 
  "update_nonce v \<equiv> \<lambda> s. s \<lparr>Nonce := v\<rparr>"

definition Setup :: "SetupState \<Rightarrow> State \<Rightarrow> SetupState \<Rightarrow> State \<Rightarrow> bool" where
   "Setup ss s ss' s'  \<equiv>
             (case (ss_pc ss) of
                L1 \<Rightarrow>  let csp = CreateProcessCSpace {VSCap P\<^sub>A, CSCap P\<^sub>A, TCBCap P\<^sub>A, TCap, KeyCap , EPCap, GrantCap, IQCap, SendCap, BadgeCap P\<^sub>A, BadgeCap P\<^sub>N};
                           tcb = CreateProcessTCB 0 csp;
                           pr = CreateProcess tcb (0,1) 0  (TInit s) 0  in
                        s' = s\<lparr>Procs := Procs s \<union> {P\<^sub>A}, ProcRec := (ProcRec s)(P\<^sub>A := pr), policy := policy s \<union> {(P\<^sub>A, Read, KEY),(P\<^sub>A, Read, INITTIME), (P\<^sub>A, Control,P P\<^sub>A),(P\<^sub>A, Control, IRQ), (P\<^sub>A, Control, NONCE), (P\<^sub>A, Control, MEM)}\<rparr>
                 \<and>  (ss_pc ss' = L2)
              | L2 \<Rightarrow>  let csp = CreateProcessCSpace {VSCap P\<^sub>1, CSCap P\<^sub>1, TCBCap P\<^sub>1};
                           tcb = CreateProcessTCB 0 csp;
                           pr = CreateProcess tcb (1,2) 1  (TInit s) 1  in
                        s' = s\<lparr>Procs := Procs s \<union> {P\<^sub>1}, ProcRec := (ProcRec s)(P\<^sub>1 := pr),policy := policy s \<union> {(P\<^sub>1, Control,P P\<^sub>1) , (P\<^sub>A, Control,P P\<^sub>1)}\<rparr>
                 \<and>  (ss_pc ss' = L3) 
              | L3 \<Rightarrow>  let csp = CreateProcessCSpace {VSCap P\<^sub>N, CSCap P\<^sub>N, TCBCap P\<^sub>N};
                           tcb = CreateProcessTCB 0 csp;
                           pr = CreateProcess tcb (2,3) 1  (TInit s) 0  in
                        s' = s\<lparr>Procs := Procs s \<union> {P\<^sub>N}, ProcRec := (ProcRec s)(P\<^sub>N := pr), policy := policy s \<union> {(P\<^sub>N, Control,P P\<^sub>N) , (P\<^sub>A, Control,P P\<^sub>N)}\<rparr>
                 \<and>  (ss_pc ss' = L4) 
              | L4 \<Rightarrow> False
              )
             "

definition "getEP s p \<equiv>  (EP (CSpace (TCB (ProcRec s p))))"


lemmas simps [simp] = update_nonce_def update_mac2_def update_mac1_def update_time_def (*update_badge_def*)
update_rval_def update_irq_def update_pc_def  MAC_def update_local_ep_def Let_def

definition Prover :: "State \<Rightarrow>  State  \<Rightarrow> bool"
  where
    "Prover s s' \<equiv> 
      (case (pc s) of
          P0 \<Rightarrow> if  BadgeCap P\<^sub>A \<in> (Caps (CSpace (TCB ((ProcRec s) P\<^sub>N)))) then s' = (`pc := P1) s else s' = s
        | P1 \<Rightarrow> s' = (`pc := P2  \<circ> `irq := False) s
        | P2 \<Rightarrow> let ep = (EP(CSpace (TCB ((ProcRec s) P\<^sub>N)))) in if isReq ep then 
                 s' = (`pc := P3 \<circ> `ep := ep \<circ> (\<lambda> s . s \<lparr>ProcRec := (ProcRec s)(P\<^sub>A := (ProcRec s P\<^sub>A)\<lparr>
                     TCB := (TCB (ProcRec s P\<^sub>A))\<lparr>CSpace := ((CSpace (TCB (ProcRec s P\<^sub>A)))\<lparr>EP := ep\<rparr>)\<rparr>\<rparr>)\<rparr>)) s else s' = s
        | P3 \<Rightarrow> (if(TInit s > (getMTime (ep s)))
                then (s'= (`pc := Idle \<circ> `rval := Empty) s )
                else (s' = (`pc := P4) s))
        | P4 \<Rightarrow> (if  ((getFMac (ep s)) \<noteq> (MAC ((getMTime (ep s)) * fst (Mem ((ProcRec s) P\<^sub>A))  *  snd (Mem ((ProcRec s) P\<^sub>A)) * (P\<^sub>A))))
                then (s' = (`pc := Idle \<circ> `rval := Empty) s) 
                else (s' = (`pc := P5) s))
        | P5 \<Rightarrow> s' = (`pc := P6 \<circ> `nonce := (TInit s + (getMTime (ep s)))) s
                                                         
        | P6 \<Rightarrow> s' = (`pc := P7  \<circ> `time := (getTime ((getMTime (ep s))))) s

        | P7 \<Rightarrow> s' = (`pc := P8  \<circ> `mac1 := (MAC (fst (Mem ((ProcRec s) P\<^sub>A)) * snd (Mem ((ProcRec s) P\<^sub>A))))) s

        | P8 \<Rightarrow> s' = (`pc := P9  \<circ> `mac2 := (MAC ((l_time s) * (P\<^sub>A) * (l_mac1 s)))) s

        | P9 \<Rightarrow> s' = (`pc := P10  \<circ> `rval := ((Res (l_time s) (l_mac1 s) (l_mac2 s)))) s

        | P10 \<Rightarrow> s' = (`pc := P11  \<circ> (\<lambda> s . s \<lparr>ProcRec := (ProcRec s)(P\<^sub>A := (ProcRec s P\<^sub>A)
                      \<lparr>TCB := (TCB (ProcRec s P\<^sub>A))\<lparr>CSpace := ((CSpace (TCB (ProcRec s P\<^sub>A)))\<lparr>EP := rval s\<rparr>)\<rparr>\<rparr>)\<rparr>)) s
               
        | P11 \<Rightarrow> s' = (`pc := Idle  \<circ> `irq := True) s

        | Idle \<Rightarrow> False
        | _ \<Rightarrow> False)"


definition Network :: "State   \<Rightarrow> Message  \<Rightarrow>  State  \<Rightarrow> bool"
  where
    "Network s m s'  \<equiv> 
       case (pc s) of
        P0 \<Rightarrow> s' = (`pc := P1 \<circ> `ep := m \<circ> (\<lambda> s . s \<lparr>ProcRec := (ProcRec s)(P\<^sub>N := (ProcRec s P\<^sub>N)\<lparr>
                     TCB := (TCB (ProcRec s P\<^sub>N))\<lparr>CSpace := ((CSpace (TCB (ProcRec s P\<^sub>N)))\<lparr>EP := m\<rparr>)\<rparr>\<rparr>)\<rparr>)) s
        | P1 \<Rightarrow> if BadgeCap P\<^sub>N \<in> (Caps (CSpace (TCB ((ProcRec s) P\<^sub>A)))) then s' = (`pc := P2) s else s' = s
        
        | P2 \<Rightarrow> let ep = (EP(CSpace (TCB ((ProcRec s) P\<^sub>A)))) in
                 s' = (`pc := P3 \<circ> (\<lambda> s . s \<lparr>ProcRec := (ProcRec s)(P\<^sub>N := (ProcRec s P\<^sub>N)\<lparr>
                     TCB := (TCB (ProcRec s P\<^sub>N))\<lparr>CSpace := ((CSpace (TCB (ProcRec s P\<^sub>N)))\<lparr>EP := ep\<rparr>)\<rparr>\<rparr>)\<rparr>)) s
        | _ \<Rightarrow> False"

(* -----------------------------------------------------P\<^sub>A Related Lemmas-------------------------------------------------*)

lemma Setup_P\<^sub>A: "ss_pc ss = L1 \<Longrightarrow> Setup ss s ss' s' \<Longrightarrow> P_attest_prop s'"
  apply(simp add: Setup_def P_attest_prop_def CreateProcessCSpace_def
                                    CreateProcessTCB_def CreateProcess_def)
  done

lemma Setup_P\<^sub>1: "P_distinct \<Longrightarrow> ss_pc ss = L2 \<Longrightarrow> P_attest_prop s \<Longrightarrow> Setup ss s ss' s' \<Longrightarrow> P_attest_prop s'"
  by(simp add:P_distinct_def Setup_def P_attest_prop_def CreateProcessCSpace_def
                                    CreateProcessTCB_def CreateProcess_def)
lemma Setup_P\<^sub>N: "P_distinct \<Longrightarrow> ss_pc ss = L3 \<Longrightarrow> P_attest_prop s \<Longrightarrow> Setup ss s ss' s' \<Longrightarrow> P_attest_prop s'"
  by(simp add:P_distinct_def Setup_def P_attest_prop_def CreateProcessCSpace_def
                                    CreateProcessTCB_def CreateProcess_def)

lemma Network_P\<^sub>A: "P_attest_prop s \<Longrightarrow> Network s m s' \<Longrightarrow> P_attest_prop s'"
   apply(simp add: Setup_def Prover_def Network_def P_distinct_def Setup_P\<^sub>A P_attest_prop_def CreateProcessCSpace_def
                                    CreateProcessTCB_def CreateProcess_def)
  apply(cases "pc s", simp_all)
   apply clarsimp
  apply clarsimp
  done


lemma Prover_P\<^sub>A: "P_attest_prop s \<Longrightarrow> Prover s s' \<Longrightarrow> P_attest_prop s'"
   apply(simp add: Setup_def Prover_def P_distinct_def Setup_P\<^sub>A P_attest_prop_def CreateProcessCSpace_def
                                    CreateProcessTCB_def CreateProcess_def)
  apply(cases " pc s", simp_all)
        apply (case_tac "BadgeCap P\<^sub>A \<in> Caps (CSpace (TCB (ProcRec s P\<^sub>N)))", simp_all)
       apply(case_tac "isReq (EP (CSpace (TCB (ProcRec s P\<^sub>N))))", simp_all)
      apply(case_tac "getMTime (ep s) < TInit s", simp_all)
  apply(case_tac "getFMac (ep s) \<noteq>
       (SOME n.
           Suc 0 \<le> n \<and>
           n \<le> getMTime (ep s) * fst (Mem (ProcRec s P\<^sub>A)) * snd (Mem (ProcRec s P\<^sub>A)) * P\<^sub>A *
                (getMTime (ep s) * fst (Mem (ProcRec s P\<^sub>A)) * snd (Mem (ProcRec s P\<^sub>A)) *
                 P\<^sub>A) *
                (getMTime (ep s) * fst (Mem (ProcRec s P\<^sub>A)) * snd (Mem (ProcRec s P\<^sub>A)) * P\<^sub>A))", simp_all)
  done

(* -----------------------------------------------------P\<^sub>N Related Lemmas-------------------------------------------------*)


lemma Network_P\<^sub>N: "P_distinct \<Longrightarrow> pc s = P3 \<Longrightarrow> Net_prop P\<^sub>N  s \<Longrightarrow> Prover s s' \<Longrightarrow> Net_prop P\<^sub>N s'"
  apply(simp add:Prover_def P_distinct_def Setup_def P_attest_prop_def Net_prop_def CreateProcessCSpace_def
                                    CreateProcessTCB_def CreateProcess_def)
  apply(case_tac "getMTime (ep s) < TInit s", simp_all)
  done

lemma Prover_P\<^sub>N: "P_distinct \<Longrightarrow> pc s = P4 \<Longrightarrow> Net_prop P\<^sub>N s \<Longrightarrow> Network s m s' \<Longrightarrow> Net_prop P\<^sub>N s'"
  by(simp add:Network_def Prover_def P_distinct_def Setup_def P_attest_prop_def Net_prop_def CreateProcessCSpace_def
                                    CreateProcessTCB_def CreateProcess_def)



(* ***********************************        Confidentiality Through AC          *****************************************     *)

definition "KeyConf s \<equiv> \<forall>p. (p, Read, KEY)\<in>policy s \<longrightarrow> p =  P\<^sub>A"
definition "MemConf s \<equiv> \<forall>p. (p, Read, MEM)\<in>policy s \<longrightarrow> p =  P\<^sub>A"
definition "IrqAC s \<equiv> \<forall>p. (p, Control, IRQ)\<in>policy s \<longrightarrow> p =  P\<^sub>A"
definition "TimeConf s \<equiv> \<forall>p. (p, Read, INITTIME)\<in>policy s \<longrightarrow> p =  P\<^sub>A"
definition "NONCE_AC s \<equiv> \<forall>p. (p, Control, NONCE)\<in>policy s \<longrightarrow> p =  P\<^sub>A"
definition "Super s \<equiv>  \<forall>p. p\<in> Procs s \<longrightarrow>  (P\<^sub>A, Control, P p)\<in>policy s"
definition "no_grant s \<equiv> \<forall> p p' .p \<in> Procs s \<and> p'\<in>Procs s \<and>  p \<noteq> P\<^sub>A \<and> p'\<noteq>P\<^sub>A 
                                          \<and> (p, Control, P p')\<in>policy s \<longrightarrow> p = p'"


definition "Evolution s ss \<equiv> (ss_pc ss = L1  \<longrightarrow> Procs s = {}) \<and>( ss_pc ss = L2  \<longrightarrow> Procs s = {P\<^sub>A})
                          \<and> ( ss_pc ss = L3  \<longrightarrow> Procs s = {P\<^sub>A , P\<^sub>1}) \<and> 
                            ( ss_pc ss = L4  \<longrightarrow> Procs s = {P\<^sub>A , P\<^sub>1 , P\<^sub>N})"

definition "Evolution_Policy s ss \<equiv> (ss_pc ss = L1 \<longrightarrow> policy s = {}) \<and>(ss_pc ss = L2  \<longrightarrow> policy s = {(P\<^sub>A, Read, KEY),(P\<^sub>A, Read, INITTIME), (P\<^sub>A, Control,P P\<^sub>A),(P\<^sub>A, Control, IRQ), (P\<^sub>A, Control, NONCE), (P\<^sub>A, Control, MEM)})
                          \<and> (ss_pc ss = L3  \<longrightarrow> policy s = {(P\<^sub>1, Control,P P\<^sub>1) , (P\<^sub>A, Control,P P\<^sub>1)}) \<and> 
                            (ss_pc ss = L4  \<longrightarrow> policy s = {(P\<^sub>N, Control,P P\<^sub>N) , (P\<^sub>A, Control,P P\<^sub>N)})"

definition "Reflect s \<equiv> \<forall>p. p\<in> Procs s \<longrightarrow> (p, Control,P p)\<in>policy s"

lemma Setup_no_Control : "Evolution_Policy s ss \<Longrightarrow> Reflect s \<Longrightarrow> Evolution s ss \<Longrightarrow> P_distinct \<Longrightarrow> no_grant s \<Longrightarrow> Setup ss s ss' s' \<Longrightarrow> no_grant s'"
  apply(simp add: Setup_def  del:simps)
  apply (cases "ss_pc ss", simp_all)
  apply safe
    apply(simp add: Reflect_def Evolution_def Evolution_Policy_def no_grant_def)
  apply(simp add: Reflect_def Evolution_def Evolution_Policy_def no_grant_def)

   apply blast
  
  by (simp add: Evolution_Policy_def Evolution_def P_distinct_def Reflect_def)

lemma Prover_no_Control:
  assumes "Prover s s'"
  and "no_grant s"
shows "no_grant  s'"
  using assms
 apply(simp add: Setup_def Prover_def Evolution_def Evolution_Policy_def P_distinct_def Reflect_def P_attest_prop_def CreateProcess_def CSpace_def
                                   CreateProcessTCB_def no_grant_def)
  apply(cases "pc s", simp_all)
     apply(case_tac "BadgeCap P\<^sub>A \<in> Caps (CSpace (TCB (ProcRec s P\<^sub>N)))", simp_all)
  apply(case_tac " isReq
        (EP (CSpace
              (TCB (ProcRec s
    P\<^sub>N))))", simp_all)
   apply(case_tac "getMTime (ep s) < TInit s", simp_all)
  apply(case_tac "getFMac (ep s) \<noteq>
       (SOME n.
           Suc 0 \<le> n \<and>
           n \<le> getMTime (ep s) *
                fst
(Mem (ProcRec s P\<^sub>A)) *
                snd
(Mem (ProcRec s P\<^sub>A)) *
                P\<^sub>A *
                (getMTime
 (ep s) *
fst (Mem (ProcRec s P\<^sub>A)) *
snd (Mem (ProcRec s P\<^sub>A)) *
P\<^sub>A) *
                (getMTime
 (ep s) *
fst (Mem (ProcRec s P\<^sub>A)) *
snd (Mem (ProcRec s P\<^sub>A)) *
P\<^sub>A))", simp_all)
  done


lemma Setup_Key_conf : "P_distinct \<Longrightarrow> KeyConf s \<Longrightarrow> Setup ss s ss' s' \<Longrightarrow> KeyConf s'"
  apply(simp add: KeyConf_def Setup_def CreateProcessCSpace_def
                                   CreateProcessTCB_def CreateProcess_def)
  apply(cases "ss_pc ss", simp_all)
  done
lemma Prover_Key_conf : "KeyConf s \<Longrightarrow> Prover s s' \<Longrightarrow> KeyConf s'"
 apply(simp add: KeyConf_def Setup_def Prover_def CreateProcessCSpace_def
                                   CreateProcessTCB_def CreateProcess_def P_distinct_def)
  apply(cases "pc s", simp_all)
     apply(case_tac "BadgeCap P\<^sub>A \<in> Caps (CSpace (TCB (ProcRec s P\<^sub>N)))", simp_all)
  apply(case_tac "isReq
        (EP (CSpace
              (TCB (ProcRec s
    P\<^sub>N))))", simp_all)
   apply(case_tac "getMTime (ep s) < TInit s
    ", simp_all)
      apply(case_tac "getFMac (ep s) \<noteq>
       (SOME n.
           Suc 0 \<le> n \<and>
           n \<le> getMTime (ep s) *
                fst
(Mem (ProcRec s P\<^sub>A)) *
                snd
(Mem (ProcRec s P\<^sub>A)) *
                P\<^sub>A *
                (getMTime
 (ep s) *
fst (Mem (ProcRec s P\<^sub>A)) *
snd (Mem (ProcRec s P\<^sub>A)) *
P\<^sub>A) *
                (getMTime
 (ep s) *
fst (Mem (ProcRec s P\<^sub>A)) *
snd (Mem (ProcRec s P\<^sub>A)) *
P\<^sub>A))", simp_all)
  done
  

 lemma Setup_Time_conf : "TimeConf s \<Longrightarrow> Setup ss s ss' s' \<Longrightarrow> TimeConf s'"
 apply(simp add: TimeConf_def Setup_def CreateProcessCSpace_def
                                   CreateProcessTCB_def CreateProcess_def)
  apply(cases "ss_pc ss", simp_all)
  done

 lemma Prover_Time_conf : "TimeConf s \<Longrightarrow> Prover s s' \<Longrightarrow> TimeConf s'"
 apply(simp add: TimeConf_def Prover_def Setup_def CreateProcessCSpace_def
                                   CreateProcessTCB_def CreateProcess_def)
   apply(cases "pc s", simp_all)
      apply(case_tac "BadgeCap P\<^sub>A \<in> Caps (CSpace (TCB (ProcRec s P\<^sub>N)))", simp_all)
   apply(case_tac "isReq
        (EP (CSpace
              (TCB (ProcRec s
    P\<^sub>N))))", simp_all)
   apply(case_tac "getMTime (ep s) < TInit s", simp_all)
   apply(case_tac "getFMac (ep s) \<noteq>
       (SOME n.
           Suc 0 \<le> n \<and>
           n \<le> getMTime (ep s) *
                fst
(Mem (ProcRec s P\<^sub>A)) *
                snd
(Mem (ProcRec s P\<^sub>A)) *
                P\<^sub>A *
                (getMTime
 (ep s) *
fst (Mem (ProcRec s P\<^sub>A)) *
snd (Mem (ProcRec s P\<^sub>A)) *
P\<^sub>A) *
                (getMTime
 (ep s) *
fst (Mem (ProcRec s P\<^sub>A)) *
snd (Mem (ProcRec s P\<^sub>A)) *
P\<^sub>A))", simp_all)
   done


lemma Superiority_Setup : "P_distinct \<Longrightarrow> Super s \<Longrightarrow> Setup ss s ss' s' \<Longrightarrow> Super s'"
apply(simp add: Super_def Setup_def CreateProcessCSpace_def P_distinct_def
                                   CreateProcessTCB_def CreateProcess_def)
  apply(intro allI impI)
  apply(cases "ss_pc ss", simp_all)
    apply auto[1]
   apply blast
  by auto



lemma Superiority_Prover : "P_distinct \<Longrightarrow> Super s \<Longrightarrow> Prover s s' \<Longrightarrow> Super s'"
apply(simp add: Super_def Setup_def Prover_def CreateProcessCSpace_def P_distinct_def
                                   CreateProcessTCB_def CreateProcess_def Network_def)

  apply(cases "pc s", simp_all)
  apply(case_tac "BadgeCap P\<^sub>A \<in> Caps (CSpace (TCB (ProcRec s P\<^sub>N)))", simp_all)
  apply(case_tac "\<forall>p. p \<in> Procs s \<longrightarrow>
        (P\<^sub>A, Control, P p)
        \<in> policy s ", simp_all)
  apply(case_tac "isReq
        (EP (CSpace
              (TCB (ProcRec s
    P\<^sub>N))))", simp_all)
   apply(case_tac "getMTime (ep s) < TInit s", simp_all)
  apply(case_tac "getFMac (ep s) \<noteq>
       (SOME n.
           Suc 0 \<le> n \<and>
           n \<le> getMTime (ep s) *
                fst (Mem
  (ProcRec s P\<^sub>A)) *
                snd (Mem
  (ProcRec s P\<^sub>A)) *
                P\<^sub>A *
                (getMTime (ep s) *
                 fst (Mem
   (ProcRec s P\<^sub>A)) *
                 snd (Mem
   (ProcRec s P\<^sub>A)) *
                 P\<^sub>A) *
                (getMTime (ep s) *
                 fst (Mem
   (ProcRec s P\<^sub>A)) *
                 snd (Mem
   (ProcRec s P\<^sub>A)) *
                 P\<^sub>A))", simp_all)
  done

lemma Setup_Mem_conf : "MemConf s \<Longrightarrow> Setup ss s ss' s' \<Longrightarrow> MemConf s'"
apply(simp add: MemConf_def Setup_def CreateProcessCSpace_def
                                   CreateProcessTCB_def CreateProcess_def)
  apply(cases "ss_pc ss", simp_all)
  done

lemma Prover_Mem_conf : "MemConf s \<Longrightarrow> Prover s s' \<Longrightarrow> MemConf s'"
apply(simp add: MemConf_def Setup_def Prover_def CreateProcessCSpace_def
                                   CreateProcessTCB_def CreateProcess_def)
  apply(case_tac "\<forall>p. (p, Read, MEM) \<in> policy s \<longrightarrow>
        p = P\<^sub>A",simp_all)    
  apply(cases "pc s", simp_all)
     apply(case_tac "BadgeCap P\<^sub>A \<in> Caps (CSpace (TCB (ProcRec s P\<^sub>N)))", simp_all)
  apply(case_tac "isReq
        (EP (CSpace
              (TCB (ProcRec s
    P\<^sub>N))))", simp_all)
   apply(case_tac "getMTime (ep s) < TInit s", simp_all)
  apply(case_tac "getFMac (ep s) \<noteq>
       (SOME n.
           Suc 0 \<le> n \<and>
           n \<le> getMTime (ep s) *
                fst (Mem
  (ProcRec s P\<^sub>A)) *
                snd (Mem
  (ProcRec s P\<^sub>A)) *
                P\<^sub>A *
                (getMTime (ep s) *
                 fst (Mem
   (ProcRec s P\<^sub>A)) *
                 snd (Mem
   (ProcRec s P\<^sub>A)) *
                 P\<^sub>A) *
                (getMTime (ep s) *
                 fst (Mem
   (ProcRec s P\<^sub>A)) *
                 snd (Mem
   (ProcRec s P\<^sub>A)) *
                 P\<^sub>A))", simp_all)
  done


lemma Prover_IRQ_AC : "IrqAC s \<Longrightarrow> Prover s s' \<Longrightarrow> IrqAC s'"
apply(simp add: Setup_def Prover_def CreateProcessCSpace_def P_distinct_def
                                   CreateProcessTCB_def CreateProcess_def Network_def IrqAC_def)
  apply(cases "pc s", simp_all)
  apply(case_tac "\<forall>p. (p, Control, IRQ)
        \<in> policy s \<longrightarrow>
        p = P\<^sub>A", simp_all)
     apply(case_tac "BadgeCap P\<^sub>A \<in> Caps (CSpace (TCB (ProcRec s P\<^sub>N)))", simp_all)
  apply(case_tac "isReq
        (EP (CSpace
              (TCB (ProcRec s
    P\<^sub>N))))", simp_all)
   apply(case_tac "getMTime (ep s) < TInit s", simp_all)
  apply(case_tac "getFMac (ep s) \<noteq>
       (SOME n.
           Suc 0 \<le> n \<and>
           n \<le> getMTime (ep s) *
                fst (Mem
  (ProcRec s P\<^sub>A)) *
                snd (Mem
  (ProcRec s P\<^sub>A)) *
                P\<^sub>A *
                (getMTime (ep s) *
                 fst (Mem
   (ProcRec s P\<^sub>A)) *
                 snd (Mem
   (ProcRec s P\<^sub>A)) *
                 P\<^sub>A) *
                (getMTime (ep s) *
                 fst (Mem
   (ProcRec s P\<^sub>A)) *
                 snd (Mem
   (ProcRec s P\<^sub>A)) *
                 P\<^sub>A))", simp_all)

  done


lemma Prover_Nonce_AC : "NONCE_AC s \<Longrightarrow> Prover s s' \<Longrightarrow> NONCE_AC s'"
apply(simp add: NONCE_AC_def Setup_def Prover_def CreateProcessCSpace_def
                                   CreateProcessTCB_def CreateProcess_def)
  apply(case_tac "\<forall>p. (p, Control, NONCE)
        \<in> policy s \<longrightarrow>
        p = P\<^sub>A ", simp_all)
  apply(cases "pc s", simp_all)
     apply(case_tac "BadgeCap P\<^sub>A \<in> Caps (CSpace (TCB (ProcRec s P\<^sub>N)))",simp_all)
  apply(case_tac "isReq
        (EP (CSpace
              (TCB (ProcRec s
    P\<^sub>N))))", simp_all)
   apply(case_tac "getMTime (ep s) < TInit s",simp_all)
apply(case_tac "getFMac (ep s) \<noteq>
       (SOME n.
           Suc 0 \<le> n \<and>
           n \<le> getMTime (ep s) *
                fst (Mem
  (ProcRec s P\<^sub>A)) *
                snd (Mem
  (ProcRec s P\<^sub>A)) *
                P\<^sub>A *
                (getMTime (ep s) *
                 fst (Mem
   (ProcRec s P\<^sub>A)) *
                 snd (Mem
   (ProcRec s P\<^sub>A)) *
                 P\<^sub>A) *
                (getMTime (ep s) *
                 fst (Mem
   (ProcRec s P\<^sub>A)) *
                 snd (Mem
   (ProcRec s P\<^sub>A)) *
                 P\<^sub>A))",simp_all)
  done


(* ***********************************        Information Flow         *****************************************     *)

definition "inv_rval s \<equiv> pc s \<in> {P10, P11} \<longrightarrow> isRes (rval s) "
definition "inv_req s \<equiv> pc s = P3 \<longrightarrow> isReq (ep s)"

lemma P\<^sub>A_to_P\<^sub>N:
  assumes "Prover s s'"
    and "inv_rval s"
  shows "inv_rval s'"
  using assms
  apply(simp add: Prover_def inv_rval_def)
  apply(cases "pc s", simp_all)
     apply(case_tac "BadgeCap P\<^sub>A \<in> Caps (CSpace (TCB (ProcRec s P\<^sub>N)))", simp_all)
  apply(case_tac "isReq
        (EP (CSpace
              (TCB (ProcRec s
    P\<^sub>N))))", simp_all)
  apply(case_tac "getMTime (ep s) < TInit s", simp_all)
  apply(case_tac "getFMac (ep s) \<noteq>
       (SOME n.
           Suc 0 \<le> n \<and>
           n \<le> getMTime (ep s) *
                fst (Mem (ProcRec s P\<^sub>A)) *
                snd (Mem (ProcRec s P\<^sub>A)) *
                P\<^sub>A *
                (getMTime (ep s) *
                 fst (Mem (ProcRec s P\<^sub>A)) *
                 snd (Mem (ProcRec s P\<^sub>A)) *
                 P\<^sub>A) *
                (getMTime (ep s) *
                 fst (Mem (ProcRec s P\<^sub>A)) *
                 snd (Mem (ProcRec s P\<^sub>A)) *
                 P\<^sub>A))", simp_all)
done

lemma P\<^sub>N_to_P\<^sub>A:
  assumes "Prover s s'"
    and "inv_req s"
  shows "inv_req s'"
using assms
  apply(simp add: P_distinct_def Setup_def Prover_def inv_req_def inv_rval_def CreateProcessCSpace_def
                                   CreateProcessTCB_def CreateProcess_def)
  apply(cases "pc s", simp_all)
   apply(case_tac "BadgeCap P\<^sub>A \<in> Caps (CSpace (TCB (ProcRec s P\<^sub>N)))", simp_all)
   apply(case_tac "isReq
        (EP (CSpace
              (TCB (ProcRec s
    P\<^sub>N))))", simp_all)
  apply(case_tac "getMTime (ep s) < TInit s", simp_all)
  apply(case_tac "getFMac (ep s) \<noteq>
       (SOME n.
           Suc 0 \<le> n \<and>
           n \<le> getMTime (ep s) *
                fst
(Mem (ProcRec s P\<^sub>A)) *
                snd
(Mem (ProcRec s P\<^sub>A)) *
                P\<^sub>A *
                (getMTime
 (ep s) *
fst (Mem (ProcRec s P\<^sub>A)) *
snd (Mem (ProcRec s P\<^sub>A)) *
P\<^sub>A) *
                (getMTime
 (ep s) *
fst (Mem (ProcRec s P\<^sub>A)) *
snd (Mem (ProcRec s P\<^sub>A)) *
P\<^sub>A))", simp_all)
  done
  

lemma Info_Flow_1: "inv_rval s \<Longrightarrow> pc s = P12 \<Longrightarrow> Badge ((ProcRec s) P\<^sub>A) \<Longrightarrow> Prover s s' \<Longrightarrow>
         isRes (EP(CSpace (TCB ((ProcRec s') P\<^sub>A)))) "
  apply(simp add: Prover_def inv_rval_def)
  done

  
(* ***********************************        Integrity         *****************************************            *)


definition "Key_AC \<equiv> \<forall>p. (p, Read, KEY)\<in>Policy \<longrightarrow> p =  P\<^sub>A"
definition "Mem_AC \<equiv> \<forall>p. (p, Control, MEM)\<in>Policy \<longrightarrow> p =  P\<^sub>A"

lemma Res_Integrity: "pc s\<in> {P2, P3, P4, P5} \<Longrightarrow> Badge ((ProcRec s) P\<^sub>A) \<Longrightarrow> isReq m \<Longrightarrow>  Network s m s' \<Longrightarrow> pc s' = P5 \<Longrightarrow>
         (EP(CSpace (TCB ((ProcRec s') P\<^sub>A)))) = (EP(CSpace (TCB ((ProcRec s') P\<^sub>N)))) "
  apply(simp add: Network_def)
  apply(case_tac "pc s = P1", simp_all)
  apply(case_tac "pc s = P2", simp_all)
  by auto

lemma EP_Integrity_Prover: "pc s = P2 \<Longrightarrow> BadgeCap P\<^sub>A \<in> (Caps (CSpace (TCB ((ProcRec s) P\<^sub>N)))) \<Longrightarrow> Prover s s' \<Longrightarrow> pc s' = P4 \<Longrightarrow>
         (EP(CSpace (TCB ((ProcRec s') P\<^sub>A)))) = (EP(CSpace (TCB ((ProcRec s') P\<^sub>N)))) "
  apply(simp add: Prover_def)
  apply (case_tac "isReq
        (EP (CSpace
              (TCB (ProcRec s
    P\<^sub>N))))", simp_all)
  done
  
lemma TInit_Integrity: 
  assumes "Prover s  s'"
  and "P_attest_prop s"
  shows "TInit s' = TInit s"
  using assms
  apply(simp add: Prover_def Key_AC_def P_attest_prop_def)
  apply(case_tac "pc s")
  apply simp_all
  apply(case_tac "BadgeCap P\<^sub>A \<in> Caps (CSpace (TCB (ProcRec s P\<^sub>N)))")
      apply simp_all
    apply(case_tac "getMTime (ep s) < TInit s")
  apply(case_tac "isReq
        (EP (CSpace
              (TCB (ProcRec s
    P\<^sub>N))))", simp_all)
  apply(case_tac "isReq
        (EP (CSpace
              (TCB (ProcRec s
    P\<^sub>N))))", simp_all)
  apply(case_tac "getMTime (ep s) < TInit s",simp_all) 
   apply(case_tac "getFMac (ep s) \<noteq>
       (SOME n.
           Suc 0 \<le> n \<and>
           n \<le> getMTime (ep s) *
                fst (Mem (ProcRec s P\<^sub>A)) *
                snd (Mem (ProcRec s P\<^sub>A)) *
                P\<^sub>A *
                (getMTime (ep s) *
                 fst (Mem (ProcRec s P\<^sub>A)) *
                 snd (Mem (ProcRec s P\<^sub>A)) *
                 P\<^sub>A) *
                (getMTime (ep s) *
                 fst (Mem (ProcRec s P\<^sub>A)) *
                 snd (Mem (ProcRec s P\<^sub>A)) *
                 P\<^sub>A))")
  apply simp_all
  done


lemma Key_Integrity:
  assumes "Prover s  s'"
  and "P_attest_prop s"
  shows "Key s' = Key s"
  using assms
  apply(simp add: Prover_def Key_AC_def P_attest_prop_def)
  apply(cases "pc s", simp_all)
    apply(case_tac " BadgeCap P\<^sub>A \<in> Caps (CSpace (TCB (ProcRec s P\<^sub>N)))")
     apply simp_all
    apply(case_tac " getMTime (ep s) < TInit s")
  apply(case_tac "isReq
        (EP (CSpace
              (TCB (ProcRec s
    P\<^sub>N))))", simp_all)
  apply(case_tac "isReq
        (EP (CSpace
              (TCB (ProcRec s
    P\<^sub>N))))", simp_all)
  apply(case_tac "getMTime (ep s) < TInit s", simp_all)
  apply(case_tac "getFMac (ep s) \<noteq>
       (SOME n.
           Suc 0 \<le> n \<and>
           n \<le> getMTime (ep s) *
                fst (Mem (ProcRec s P\<^sub>A)) *
                snd (Mem (ProcRec s P\<^sub>A)) *
                P\<^sub>A *
                (getMTime (ep s) *
                 fst (Mem (ProcRec s P\<^sub>A)) *
                 snd (Mem (ProcRec s P\<^sub>A)) *
                 P\<^sub>A) *
                (getMTime (ep s) *
                 fst (Mem (ProcRec s P\<^sub>A)) *
                 snd (Mem (ProcRec s P\<^sub>A)) *
                 P\<^sub>A))")
   apply simp_all
  done


lemma Mem_Integrity_Prover:
  assumes "Prover s s'"
  and "P_attest_prop s"
  shows "Mem ((ProcRec s') P\<^sub>A) = Mem ((ProcRec s) P\<^sub>A)"
  using assms
  apply(simp add: Prover_def Key_AC_def P_attest_prop_def)
  apply(cases "pc s", simp_all)
     apply(case_tac " BadgeCap P\<^sub>A \<in> Caps (CSpace (TCB (ProcRec s P\<^sub>N)))", simp_all)
  apply (case_tac "isReq
        (EP (CSpace
              (TCB (ProcRec s
    P\<^sub>N))))", simp_all)
   apply(case_tac "getMTime (ep s) < TInit s", simp_all)
  apply(case_tac "getFMac (ep s) \<noteq>
       (SOME n.
           Suc 0 \<le> n \<and>
           n \<le> getMTime (ep s) *
                fst (Mem (ProcRec s P\<^sub>A)) *
                snd (Mem (ProcRec s P\<^sub>A)) *
                P\<^sub>A *
                (getMTime (ep s) *
                 fst (Mem (ProcRec s P\<^sub>A)) *
                 snd (Mem (ProcRec s P\<^sub>A)) *
                 P\<^sub>A) *
                (getMTime (ep s) *
                 fst (Mem (ProcRec s P\<^sub>A)) *
                 snd (Mem (ProcRec s P\<^sub>A)) *
                 P\<^sub>A))", simp_all)
  done

lemma Mem_Integrity_Network:
  assumes "Network s m s'"
 shows "Mem ((ProcRec s') P\<^sub>A) = Mem ((ProcRec s) P\<^sub>A)"
  using assms
  apply(simp add: Setup_def P_attest_prop_def Prover_def Network_def Mem_AC_def)
  apply(case_tac "pc s", simp_all)
  apply(case_tac "BadgeCap P\<^sub>N \<in> Caps (CSpace (TCB (ProcRec s P\<^sub>A)))", simp_all)
  done

end
