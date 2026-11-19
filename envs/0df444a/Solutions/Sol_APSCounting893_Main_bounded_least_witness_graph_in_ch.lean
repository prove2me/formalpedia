-- Prove2me | solution 1 for APSCounting893.Main.bounded_least_witness_graph_in_ch
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T22:13:08.485189+00:00
-- url     : https://prove2.me/submissions/bf7bca78-6402-43cb-bc20-6cd6218975bd

import Definitions.Def_APSCounting893_Main_BinaryOracleArithmetic
import Definitions.Def_APSCounting893_Main_BoundedLeastArithmetic
import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_APSCounting893_Main_ImplicitCountingArithmetic
import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Frame_Basic
import Mathlib.Data.Nat.Find
import Theorems.Thm_APSCounting893_Main_bounded_majority_oracle_pp
import Theorems.Thm_APSCounting893_Main_bounded_quantification_oracle_pp
import Theorems.Thm_APSCounting893_Main_native_polynomial_oracle_preimage
import Theorems.Thm_APSCounting893_Main_stack_program_polynomial_simulation
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime Cslib.BitString
lemma boundedLeastValue_lt (A : Language) (a b : ℕ) (x : Word) :
    boundedLeastValue A a b x < 2^polyBound a b x.length := by
  classical
  unfold boundedLeastValue
  split_ifs with h
  · exact (Nat.find_spec h).1
  · positivity

lemma lt_boundedLeastValue_iff (A : Language) (a b : ℕ) (x : Word) (u : ℕ) :
    u < boundedLeastValue A a b x ↔
      u < 2^polyBound a b x.length ∧
      (∃ n : ℕ,n < 2^polyBound a b x.length ∧ A (Turing.MultiTapeTM.frame x++n.bits)) ∧
      ∀ n,n ≤ u → ¬A (Turing.MultiTapeTM.frame x++n.bits) := by
  classical
  by_cases h : ∃ n : ℕ,n < 2^polyBound a b x.length ∧ A (Turing.MultiTapeTM.frame x++n.bits)
  · simp only [boundedLeastValue,dif_pos h]
    constructor
    · intro hu
      refine ⟨hu.trans (Nat.find_spec h).1,h,?_⟩
      intro n hnu hA
      exact (Nat.not_lt_of_ge (Nat.find_min' h ⟨hnu.trans_lt (hu.trans (Nat.find_spec h).1),hA⟩)) (hnu.trans_lt hu)
    · rintro ⟨hu,hex,hall⟩
      by_contra hn
      exact hall (Nat.find h) (by omega) (Nat.find_spec h).2
  · simp [boundedLeastValue,h]
end APSCounting893.Main
end Component_0

section Component_1

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
namespace APSCounting893.Main

noncomputable def haltMachine (b : Bool) : OracleMachine where
  states := 1
  alphabet := 0
  tapes := 4
  inputTape := 0
  randomTape := 1
  queryTape := 2
  outputTape := 3
  distinctTapes := by decide
  initial := 0
  transition := fun _ _ => .halt b

lemma haltMachine_answer_one (b : Bool) (A : Language) (x w : Word) :
    (machineRun (haltMachine b) A x w 1).answer = some b := rfl

lemma constant_inOracleP (A : Language) (b : Bool) : InOracleP A (fun _ => b = true) := by
  refine ⟨haltMachine b, 1, 0, ?_⟩
  intro x
  exact ⟨b, haltMachine_answer_one b A x [], Iff.rfl⟩

lemma constant_inOraclePP (A : Language) (b : Bool) : InOraclePP A (fun _ => b = true) := by
  refine ⟨haltMachine b, 1, 0, 0, 0, ?_, ?_⟩
  · intro x w hw
    rw [show polyBound 1 0 x.length = 1 by simp [polyBound], haltMachine_answer_one]
    rfl
  · intro x
    simp only [polyBound, pow_zero, mul_one, zero_mul, pow_zero, haltMachine_answer_one]
    cases b <;> simp

lemma constant_inCountingHierarchy (b : Bool) : InCountingHierarchy (fun _ => b = true) := by
  exact ⟨0, constant_inOracleP (fun _ => False) b⟩

lemma constant_atCHLevel (j : ℕ) (b : Bool) : AtCHLevel j (fun _ => b = true) := by
  induction j with
  | zero => exact constant_inOracleP _ b
  | succ j ih => exact ⟨fun _ => b = true, ih, constant_inOraclePP _ b⟩

lemma machineStep_halted (M : OracleMachine) (A : Language) (cfg : MachineConfig M)
    (h : cfg.answer.isSome) : machineStep M A cfg = cfg := by
  simp only [machineStep, if_pos h]

lemma machineRun_succ (M : OracleMachine) (A : Language) (x w : Word) (t : ℕ) :
    machineRun M A x w (t + 1) = machineStep M A (machineRun M A x w t) := by
  exact Function.iterate_succ_apply' _ _ _

lemma machineRun_halted_persistent (M : OracleMachine) (A : Language) (x w : Word)
    (t s : ℕ) (h : (machineRun M A x w t).answer.isSome) :
    machineRun M A x w (t + s) = machineRun M A x w t := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Nat.add_succ]
      rw [machineRun_succ]
      rw [ih, machineStep_halted M A _ h]

end APSCounting893.Main
end Component_1

section Component_2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

noncomputable def negateMachine (M : OracleMachine) : OracleMachine :=
  { M with transition := fun q symbols => match M.transition q symbols with
    | .step q write move => .step q write move
    | .query yes no => .query yes no
    | .halt b => .halt (!b) }

def negateConfig (M : OracleMachine) (cfg : MachineConfig M) : MachineConfig (negateMachine M) where
  state := cfg.state
  tapes := cfg.tapes
  answer := cfg.answer.map Bool.not

lemma negateMachine_step (M : OracleMachine) (A : Language) (cfg : MachineConfig M) :
    machineStep (negateMachine M) A (negateConfig M cfg) = negateConfig M (machineStep M A cfg) := by
  classical
  rcases cfg with ⟨q, tapes, answer⟩
  cases answer with
  | some b => rfl
  | none =>
      cases h : M.transition q (fun j => (tapes j).read (tapes j).head) with
      | step q' write move => simp [machineStep, negateMachine, negateConfig, h]
      | query yes no => simp [machineStep, negateMachine, negateConfig, h]
      | halt b => simp [machineStep, negateMachine, negateConfig, h]

lemma negateMachine_initial (M : OracleMachine) (x w : Word) :
    initialConfig (negateMachine M) x w = negateConfig M (initialConfig M x w) := rfl

lemma negateMachine_run (M : OracleMachine) (A : Language) (x w : Word) (t : ℕ) :
    machineRun (negateMachine M) A x w t = negateConfig M (machineRun M A x w t) := by
  induction t with
  | zero => exact negateMachine_initial M x w
  | succ t ih =>
      rw [machineRun_succ, machineRun_succ, ih, negateMachine_step]

lemma InOracleP.compl {A L : Language} (hL : InOracleP A L) : InOracleP A (fun x => ¬ L x) := by
  obtain ⟨M, c, d, hM⟩ := hL
  refine ⟨negateMachine M, c, d, ?_⟩
  intro x
  obtain ⟨b, hb, hbx⟩ := hM x
  refine ⟨!b, ?_, ?_⟩
  · rw [negateMachine_run]
    change (machineRun M A x [] (polyBound c d x.length)).answer.map Bool.not = some (!b)
    rw [hb]
    rfl
  · cases b <;> simp_all

lemma InOracleP.inOraclePP {A L : Language} (hL : InOracleP A L) : InOraclePP A L := by
  obtain ⟨M, c, d, hM⟩ := hL
  refine ⟨M, c, d, 0, 0, ?_, ?_⟩
  · intro x w hw
    have hw0 : w = [] := List.length_eq_zero_iff.mp (by simpa [polyBound] using hw)
    subst w
    obtain ⟨b, hb, _⟩ := hM x
    rw [hb]
    rfl
  · intro x
    obtain ⟨b, hb, hbx⟩ := hM x
    have hset : {w : Word | w.length = polyBound 0 0 x.length ∧
        (machineRun M A x w (polyBound c d x.length)).answer = some true} =
        if b then {[]} else ∅ := by
      ext w
      simp only [polyBound, zero_mul, List.length_eq_zero_iff, Set.mem_setOf_eq]
      by_cases hw : w = []
      · subst w
        dsimp [polyBound] at hb
        cases b <;> simp [hb]
      · simp [hw]
    rw [hset]
    cases b <;> simp_all [polyBound]

end APSCounting893.Main
end Component_2

section Component_3
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main

def taggedOracle (A : Language) : Language
  | false::false::rest => A rest
  | false::true::rest => ¬ A rest
  | true::b::_ => b=true
  | _ => False

def taggedOracleProgram : StackProgram (Fin 7) 0 where
  initial:=0
  transition:=fun q =>
    if q=0 then .pop 0 1 2 6
    else if q=1 then .pop 0 3 4 6
    else if q=2 then .pop 0 6 5 6
    else if q=3 then .query 0 5 6
    else if q=4 then .query 0 6 5
    else .halt (decide (q=5))

lemma taggedOracleProgram_answer (A : Language) (x : Word) :
    (taggedOracleProgram.run A x [] 4).answer=
      some (@decide (taggedOracle A x) (Classical.propDecidable _)) := by
  classical
  cases x with
  | nil => simp [taggedOracle,taggedOracleProgram,StackProgram.run,StackProgram.step,
      StackProgram.initialConfig,Function.iterate_succ_apply']
  | cons b rest =>
    cases b with
    | false =>
      cases rest with
      | nil => simp [taggedOracle,taggedOracleProgram,StackProgram.run,StackProgram.step,
          StackProgram.initialConfig,Function.iterate_succ_apply']
      | cons mode rest =>
        cases mode <;> by_cases ha : A rest <;>
          simp [taggedOracle,taggedOracleProgram,StackProgram.run,StackProgram.step,
            StackProgram.initialConfig,Function.iterate_succ_apply',ha]
    | true =>
      cases rest with
      | nil => simp [taggedOracle,taggedOracleProgram,StackProgram.run,StackProgram.step,
          StackProgram.initialConfig,Function.iterate_succ_apply']
      | cons b rest => cases b <;>
          simp [taggedOracle,taggedOracleProgram,StackProgram.run,StackProgram.step,
            StackProgram.initialConfig,Function.iterate_succ_apply']

lemma taggedOracle_inOracleP (A : Language) : InOracleP A (taggedOracle A) := by
  apply stack_program_polynomial_simulation taggedOracleProgram A (taggedOracle A) 4 0
  intro x
  refine ⟨@decide (taggedOracle A x) (Classical.propDecidable _),?_,by simp⟩
  simpa only [polyBound,pow_zero,mul_one] using taggedOracleProgram_answer A x

lemma AtCHLevel.tagged {j : ℕ} {A : Language} (hA : AtCHLevel j A) :
    AtCHLevel (j+1) (taggedOracle A) := ⟨A,hA,(taggedOracle_inOracleP A).inOraclePP⟩

end APSCounting893.Main
end Component_3

section Component_4
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace APSCounting893.Main

lemma AtCHLevel.native_tagged_preimage {j : ℕ} {A : Language} (hA : AtCHLevel j A)
    (f : Word → Word)
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits) :
    AtCHLevel (j+2) (fun x => taggedOracle A (f x)) := by
  exact ⟨taggedOracle A,hA.tagged,(native_polynomial_oracle_preimage f hf (taggedOracle A)).inOraclePP⟩

lemma AtCHLevel.native_tagged_majority {j : ℕ} {A : Language} (hA : AtCHLevel j A)
    (f : Word → Word)
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
    (a b : ℕ) :
    AtCHLevel (j+3) (fun x => 2^polyBound a b x.length <
      2*Set.ncard {w : Word | w.length=polyBound a b x.length ∧ taggedOracle A (f (pairWord x w))}) := by
  exact ⟨fun z => taggedOracle A (f z),hA.native_tagged_preimage f hf,
    bounded_majority_oracle_pp _ a b⟩

end APSCounting893.Main
end Component_4

section Component_5
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace APSCounting893.Main

lemma AtCHLevel.native_tagged_exists {j : ℕ} {A : Language} (hA : AtCHLevel j A)
    (f : Word → Word)
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
    (a b : ℕ) (ha : 0 < a) :
    AtCHLevel (j+3) (fun x => ∃ w : Word,w.length=polyBound a b x.length ∧
      taggedOracle A (f (pairWord x w))) := by
  have hp := hA.native_tagged_preimage f hf
  exact ⟨_,hp,(bounded_quantification_oracle_pp _ a b ha).1⟩

lemma AtCHLevel.native_tagged_forall {j : ℕ} {A : Language} (hA : AtCHLevel j A)
    (f : Word → Word)
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
    (a b : ℕ) (ha : 0 < a) :
    AtCHLevel (j+3) (fun x => ∀ w : Word,w.length=polyBound a b x.length →
      taggedOracle A (f (pairWord x w))) := by
  have hp := hA.native_tagged_preimage f hf
  exact ⟨_,hp,(bounded_quantification_oracle_pp _ a b ha).2⟩

end APSCounting893.Main
end Component_5

section Component_6

end Component_6

section Component_7
set_option autoImplicit false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
lemma native_polyBound_unary (a b : ℕ) : ComputableTidilyInPolyTime
    (polyBound a b) encUnary encUnary := by
  have hi := id' (encIn:=encUnary)
  have hplus := unary_add.comp (hi.prod (const 1))
  have hp := (unary_pow b).comp hplus
  have hh := unary_mul.comp ((const a).prod hp)
  exact hh.of_enc_eq (fun n => rfl)
end APSCounting893.Main
end Component_7

section Component_8
set_option autoImplicit false
namespace APSCounting893.Main
lemma unframe_pairWord (x y : Word) : Turing.MultiTapeTM.unframe (pairWord x y)=x :=
  Turing.MultiTapeTM.unframe_frame_append x y
lemma dropFrame_pairWord (x y : Word) : Turing.MultiTapeTM.dropFrame (pairWord x y)=y :=
  Turing.MultiTapeTM.dropFrame_frame_append x y
end APSCounting893.Main
end Component_8

section Component_9
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime Cslib.BitString
lemma native_leastValueQuery (a b : ℕ) : ComputableTidilyInPolyTime
    (leastValueQuery a b) encBits encBits := by
  have h1 := ComputableTidilyInPolyTime.unframe
  have h2 := ComputableTidilyInPolyTime.unframe.comp h1
  have hr := ComputableTidilyInPolyTime.unframe.comp h2
  have hx := ComputableTidilyInPolyTime.unframe.comp hr
  have hu := bitsToNat.comp (ComputableTidilyInPolyTime.dropFrame.comp hr)
  have hn := bitsToNat.comp (ComputableTidilyInPolyTime.dropFrame.comp h2)
  have hm := bitsToNat.comp (ComputableTidilyInPolyTime.dropFrame.comp h1)
  have hwidth := (native_polyBound_unary a b).comp (length_bits.comp hx)
  have hbound := binary_two_pow.comp hwidth
  have hguard := decide_and (binary_lt' hu hbound) (binary_lt' hn hbound)
  have hhead := (headD (encA:=encBool) (encL:=encBits) false).comp ComputableTidilyInPolyTime.dropFrame
  have hf := (bitsFrame encBits).comp hx
  have hpos := bitsAppend (const [false,false]) (bitsAppend hf (natBits.comp hn))
  have hneg := bitsAppend (const [false,true]) (bitsAppend hf (natBits.comp hm))
  have hright := ite_decide (binary_le' hm hu) hneg (const [true,true])
  have hbody := hhead.cond hright hpos
  have hh := ite_decide hguard hbody (const [true,false])
  exact hh.of_enc_eq (fun z => rfl)

lemma leastValueQuery_semantics (A : Language) (a b : ℕ) (root w v : Word) (mode : Bool) :
    taggedOracle A (leastValueQuery a b (pairWord (pairWord (pairWord root w) v) [mode])) ↔
      (ofBits (Turing.MultiTapeTM.dropFrame root) < leastValueBound a b root ∧
        ofBits w < leastValueBound a b root) ∧
      (if mode then ofBits v ≤ ofBits (Turing.MultiTapeTM.dropFrame root) →
          ¬A (Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe root)++(ofBits v).bits)
        else A (Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe root)++(ofBits w).bits)) := by
  simp only [leastValueQuery,leastValueRoot,leastValueWitness,leastValueCandidate,
    unframe_pairWord,dropFrame_pairWord,List.headD_cons]
  by_cases hg : ofBits (Turing.MultiTapeTM.dropFrame root) < leastValueBound a b root ∧
      ofBits w < leastValueBound a b root
  · rw [if_pos hg]
    cases mode <;> by_cases hm : ofBits v ≤ ofBits (Turing.MultiTapeTM.dropFrame root) <;>
      simp [hm,hg,taggedOracle,List.append_assoc]
  · rw [if_neg hg]
    simp [hg,taggedOracle]
end APSCounting893.Main
end Component_9

section Component_10
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency.types false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def graphFromLessQuery (z : Word) : Word :=
  let whole := Turing.MultiTapeTM.unframe z
  let v := ofBits (Turing.MultiTapeTM.dropFrame whole)
  if (Turing.MultiTapeTM.dropFrame z).headD false then [false,true]++whole
  else if v=0 then [true,true]
  else [false,false]++Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe whole)++(v-1).bits

lemma native_graphFromLessQuery : ComputableTidilyInPolyTime graphFromLessQuery encBits encBits := by
  have hwhole := ComputableTidilyInPolyTime.unframe
  have hv := bitsToNat.comp (ComputableTidilyInPolyTime.dropFrame.comp hwhole)
  have hhead := (headD (encA:=encBool) (encL:=encBits) false).comp ComputableTidilyInPolyTime.dropFrame
  have hupper := bitsAppend (const [false,true]) hwhole
  have hlowerWord := bitsAppend ((bitsFrame encBits).comp (ComputableTidilyInPolyTime.unframe.comp hwhole))
    (natBits.comp (binary_sub' hv (const 1)))
  have hlower := ite_decide (decide_eq' hv (const 0)) (const [true,true])
    (bitsAppend (const [false,false]) hlowerWord)
  have hh := hhead.cond hupper hlower
  exact hh.of_enc_eq (fun z => rfl)

lemma graphFromLessQuery_semantics (F : Word → ℕ) (z : Word) (b : Bool) :
    taggedOracle (NaturalLessLanguage F) (graphFromLessQuery (pairWord z [b])) ↔
      if b then ¬ ofBits (Turing.MultiTapeTM.dropFrame z)<F (Turing.MultiTapeTM.unframe z)
      else ofBits (Turing.MultiTapeTM.dropFrame z)=0 ∨
        ofBits (Turing.MultiTapeTM.dropFrame z)-1<F (Turing.MultiTapeTM.unframe z) := by
  have he : pairWord z [b]=Turing.MultiTapeTM.frame z++[b] := rfl
  rw [he]
  simp only [graphFromLessQuery,unframe_frame_append,dropFrame_frame_append,List.headD_cons]
  cases b with
  | true => simp [taggedOracle,NaturalLessLanguage]
  | false =>
    by_cases hv : ofBits (Turing.MultiTapeTM.dropFrame z)=0
    · simp [hv,taggedOracle]
    · have hbits (n : ℕ) : ofBits n.bits=n := Nat.foldr_bit_bits n
      simp [hv,taggedOracle,NaturalLessLanguage,unframe_frame_append,dropFrame_frame_append,
        hbits,List.append_assoc]

lemma forall_one_bit_word (P : Word → Prop) :
    (∀ w : Word,w.length=1 → P w) ↔ P [false] ∧ P [true] := by
  constructor
  · intro h;exact ⟨h [false] rfl,h [true] rfl⟩
  · rintro ⟨hf,ht⟩ w hw
    cases w with
    | nil => simp at hw
    | cons b w =>
      have hnil : w=[] := List.length_eq_zero_iff.mp (by simpa using hw)
      subst w
      cases b <;> assumption

lemma AtCHLevel.graph_from_less {F : Word → ℕ} {j : ℕ}
    (hless : AtCHLevel j (NaturalLessLanguage F)) :
    AtCHLevel (j+3) (NaturalGraphLanguage F) := by
  have hh := hless.native_tagged_forall graphFromLessQuery
    native_graphFromLessQuery.computableInPolyTime 1 0 (by decide)
  have he : (fun z => ∀ w : Word,w.length=polyBound 1 0 z.length →
      taggedOracle (NaturalLessLanguage F) (graphFromLessQuery (pairWord z w)))=NaturalGraphLanguage F := by
    funext z
    apply propext
    simp only [polyBound,pow_zero,mul_one,forall_one_bit_word,graphFromLessQuery_semantics,
      Bool.false_eq_true,ite_false,ite_true]
    change (ofBits (Turing.MultiTapeTM.dropFrame z)=0 ∨
      ofBits (Turing.MultiTapeTM.dropFrame z)-1<F (Turing.MultiTapeTM.unframe z)) ∧
      ¬ ofBits (Turing.MultiTapeTM.dropFrame z)<F (Turing.MultiTapeTM.unframe z) ↔
      F (Turing.MultiTapeTM.unframe z)=ofBits (Turing.MultiTapeTM.dropFrame z)
    omega
  rw [he] at hh
  exact hh

end APSCounting893.Main
end Component_10

section Component_11
set_option autoImplicit false
namespace APSCounting893.Main
open Turing.MultiTapeTM Cslib.BitString
lemma ofBits_eq_lsbValue (w : Word) : ofBits w=lsbValue w := by
  exact (lsbValue_eq_foldr_bit w).symm
end APSCounting893.Main
end Component_11

section Component_12
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.constructorNameAsVariable false
namespace APSCounting893.Main
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime Cslib.BitString
attribute [local irreducible] leastValueQuery
def leastValueLessLanguage (A : Language) (a b : ℕ) : Language := fun root =>
  ∃ w : Word,w.length=leastValueClock a b root ∧
    ∀ v : Word,v.length=leastValueClock a b (pairWord root w) →
      ∀ sel : Word,sel.length=1 →
        taggedOracle A (leastValueQuery a b (pairWord (pairWord (pairWord root w) v) sel))

lemma leastValueClock_bound (a b : ℕ) (root : Word) :
    polyBound a b (Turing.MultiTapeTM.unframe root).length ≤ leastValueClock a b root := by
  have hlen := length_unframe_add_dropFrame_le root
  have hp : ((Turing.MultiTapeTM.unframe root).length+1)^b ≤ (root.length+1)^(b+1) :=
    (Nat.pow_le_pow_left (by omega) b).trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ b))
  exact (Nat.mul_le_mul_left a hp).trans (Nat.mul_le_mul_right _ (Nat.le_succ a))

lemma leastValueClock_mono (a b : ℕ) (z w : Word) :
    leastValueClock a b z ≤ leastValueClock a b (pairWord z w) := by
  have hlen := length_unframe_add_dropFrame_le (pairWord z w)
  rw [unframe_pairWord] at hlen
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : z.length+1 ≤ (pairWord z w).length+1) (b+1))

lemma leastValueQuery_allSelectors (A : Language) (a b : ℕ) (root w v : Word) :
    (∀ sel : Word,sel.length=1 →
      taggedOracle A (leastValueQuery a b (pairWord (pairWord (pairWord root w) v) sel))) ↔
      (ofBits (Turing.MultiTapeTM.dropFrame root) < leastValueBound a b root ∧
        ofBits w < leastValueBound a b root) ∧
      A (Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe root)++(ofBits w).bits) ∧
      (ofBits v ≤ ofBits (Turing.MultiTapeTM.dropFrame root) →
        ¬A (Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe root)++(ofBits v).bits)) := by
  rw [forall_one_bit_word]
  simp only [leastValueQuery_semantics,Bool.false_eq_true,ite_false,ite_true]
  tauto

lemma leastValueLessLanguage_eq (A : Language) (a b : ℕ) :
    leastValueLessLanguage A a b=NaturalLessLanguage (boundedLeastValue A a b) := by
  funext root
  apply propext
  change leastValueLessLanguage A a b root ↔
    ofBits (Turing.MultiTapeTM.dropFrame root) < boundedLeastValue A a b (Turing.MultiTapeTM.unframe root)
  rw [lt_boundedLeastValue_iff]
  let u := ofBits (Turing.MultiTapeTM.dropFrame root)
  let x := Turing.MultiTapeTM.unframe root
  let r := polyBound a b x.length
  have hr := leastValueClock_bound a b root
  constructor
  · rintro ⟨w,hw,hall⟩
    let v0 := List.replicate (leastValueClock a b (pairWord root w)) false
    have h0 := (leastValueQuery_allSelectors A a b root w v0).mp (hall v0 (by simp [v0]))
    refine ⟨h0.1.1,⟨ofBits w,h0.1.2,h0.2.1⟩,?_⟩
    intro n hnu
    have hn : n < 2^leastValueClock a b (pairWord root w) :=
      (hnu.trans_lt h0.1.1).trans_le (Nat.pow_le_pow_right (by decide)
        (hr.trans (leastValueClock_mono a b root w)))
    let v := lowBits (leastValueClock a b (pairWord root w)) n
    have hv : ofBits v=n := by simpa only [ofBits_eq_lsbValue] using lsbValue_lowBits hn
    have hmat := (leastValueQuery_allSelectors A a b root w v).mp (hall v (length_lowBits _ _))
    simpa only [hv] using hmat.2.2 (by simpa only [hv] using hnu)
  · rintro ⟨hu,⟨n,hn,hA⟩,hall⟩
    have hnW : n < 2^leastValueClock a b root :=
      hn.trans_le (Nat.pow_le_pow_right (by decide) hr)
    let w := lowBits (leastValueClock a b root) n
    have hw : ofBits w=n := by simpa only [ofBits_eq_lsbValue] using lsbValue_lowBits hnW
    refine ⟨w,length_lowBits _ _,?_⟩
    intro v hv
    apply (leastValueQuery_allSelectors A a b root w v).mpr
    rw [hw]
    exact ⟨⟨hu,hn⟩,hA,hall (ofBits v)⟩

lemma AtCHLevel.bounded_least_graph {A : Language} {j : ℕ} (hA : AtCHLevel j A) (a b : ℕ) :
    AtCHLevel (j+8) (NaturalGraphLanguage (boundedLeastValue A a b)) := by
  have h0 := hA.native_tagged_preimage (leastValueQuery a b) (native_leastValueQuery a b).computableInPolyTime
  have h1 : AtCHLevel (j+3) (fun z => ∀ sel : Word,sel.length=polyBound 1 0 z.length →
      taggedOracle A (leastValueQuery a b (pairWord z sel))) :=
    ⟨_,h0,(bounded_quantification_oracle_pp _ 1 0 (by decide)).2⟩
  have h2 : AtCHLevel (j+4) (fun z => ∀ v : Word,v.length=polyBound (a+1) (b+1) z.length →
      ∀ sel : Word,sel.length=polyBound 1 0 (pairWord z v).length →
        taggedOracle A (leastValueQuery a b (pairWord (pairWord z v) sel))) :=
    ⟨_,h1,(bounded_quantification_oracle_pp _ (a+1) (b+1) (by positivity)).2⟩
  have h3 : AtCHLevel (j+5) (fun root => ∃ w : Word,w.length=polyBound (a+1) (b+1) root.length ∧
      ∀ v : Word,v.length=polyBound (a+1) (b+1) (pairWord root w).length →
        ∀ sel : Word,sel.length=polyBound 1 0 (pairWord (pairWord root w) v).length →
          taggedOracle A (leastValueQuery a b (pairWord (pairWord (pairWord root w) v) sel))) :=
    ⟨_,h2,(bounded_quantification_oracle_pp _ (a+1) (b+1) (by positivity)).1⟩
  have hL : AtCHLevel (j+5) (leastValueLessLanguage A a b) := by
    unfold leastValueLessLanguage leastValueClock
    simpa only [polyBound,pow_zero,mul_one] using h3
  rw [leastValueLessLanguage_eq] at hL
  simpa only [Nat.add_assoc] using hL.graph_from_less
end APSCounting893.Main
end Component_12

open APSCounting893.Main
theorem solution (A : Language) (j a b : ℕ)
    (hA : AtCHLevel j A) :
    AtCHLevel (j+8) (NaturalGraphLanguage (boundedLeastValue A a b)) := by
  exact hA.bounded_least_graph a b
