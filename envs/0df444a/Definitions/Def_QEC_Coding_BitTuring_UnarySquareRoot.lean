-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnarySquareRoot
-- name    : QEC_Coding_BitTuring_UnarySquareRoot
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:10:43.828584+00:00
-- url     : https://prove2.me/theorems/eb521576-f20c-4ff1-9ec2-1833f01f520b
-- title:
--   Unary Square Root
-- statement:
--   Definitions and structural lemmas for Unary Square Root, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnarySquareRoot.lean

import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRootTrial
import Definitions.Def_QEC_Coding_BitTuring_FlagLoop
import Mathlib.Data.Nat.Find
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_SquareRootTrial_input_ne_output
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_prefixInput_dropWhile
import Theorems.Thm_QEC_Coding_BitTuring_UnaryOutputEquality_prefixInput_takeWhile

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.SquareRoot
open Turing StateTransition
def readNat (w : List Bool) : ℕ := (w.takeWhile id).length
def afterNat (w : List Bool) : List Bool := (w.dropWhile id).tail
theorem readNat_prefix (n : ℕ) (w : List Bool) :
    readNat (UnaryOutputEquality.prefixInput n w)=n := by
  simp [readNat,UnaryOutputEquality.prefixInput_takeWhile,unary_length]
theorem afterNat_prefix (n : ℕ) (w : List Bool) :
    afterNat (UnaryOutputEquality.prefixInput n w)=w := by
  simp [afterNat,UnaryOutputEquality.prefixInput_dropWhile]
theorem readNat_unary (n : ℕ) : readNat (unary n)=n := by
  simp [readNat,unary]
theorem record_eq (r a q : ℕ) : SquareRootAdvance.record r a q=
    UnaryOutputEquality.prefixInput r
      (UnaryOutputEquality.prefixInput a (UnaryOutputEquality.prefixInput a (unary q))) := by rfl
def F (w : List Bool) : Bool×List Bool :=
  let r := readNat w
  let a := readNat (afterNat w)
  let q := readNat (afterNat (afterNat (afterNat w)))
  if (a*a)%q=r then (true,unary a) else (false,SquareRootAdvance.record r (a+1) q)
theorem F_record (r a q : ℕ) : F (SquareRootAdvance.record r a q)=
    if (a*a)%q=r then (true,unary a) else (false,SquareRootAdvance.record r (a+1) q) := by
  simp only [F,record_eq,readNat_prefix,afterNat_prefix,readNat_unary]
theorem result_eq (r a q : ℕ) : SquareRootTrial.result r a q=
    (F (SquareRootAdvance.record r a q)).1::(F (SquareRootAdvance.record r a q)).2 := by
  rw [F_record]
  by_cases h:(a*a)%q=r <;> simp [SquareRootTrial.result,SquareRootAdvance.output,h]
def index (r q : ℕ) (h : ∃ n, n<q ∧ (n*n)%q=r) : ℕ := Nat.find h
theorem index_lt (r q : ℕ) (h : ∃ n, n<q ∧ (n*n)%q=r) : index r q h<q :=
  (Nat.find_spec h).1
theorem index_residue (r q : ℕ) (h : ∃ n, n<q ∧ (n*n)%q=r) :
    ((index r q h)*(index r q h))%q=r := (Nat.find_spec h).2
theorem before_index (r q : ℕ) (h : ∃ n, n<q ∧ (n*n)%q=r) (i : ℕ) (hi : i< index r q h) :
    (i*i)%q≠r := by
  intro he
  exact Nat.find_min h hi ⟨hi.trans (index_lt r q h),he⟩
theorem state_succ_after (F : List Bool → Bool×List Bool) (n : ℕ) (x : List Bool) :
    FlagLoop.state F (n+1) x=(F (FlagLoop.state F n x)).2 :=
  Function.iterate_succ_apply' _ _ _
theorem state_record (r q : ℕ) (h : ∃ n, n<q ∧ (n*n)%q=r) (i : ℕ) (hi : i≤ index r q h) :
    FlagLoop.state F i (SquareRootAdvance.record r 0 q)=SquareRootAdvance.record r i q := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [state_succ_after]
      rw [ih (by omega),F_record]
      simp [before_index r q h i (by omega)]
theorem state_final (r q : ℕ) (h : ∃ n, n<q ∧ (n*n)%q=r) :
    FlagLoop.state F (index r q h+1) (SquareRootAdvance.record r 0 q)=unary (index r q h) := by
  rw [state_succ_after,state_record r q h _ (le_refl _),F_record]
  simp [index_residue r q h]
def machine : Machine := FlagLoop.machine SquareRootTrial.machine
noncomputable def time : Polynomial ℕ :=
  FlagLoop.timePolynomial SquareRootTrial.time Polynomial.X (Polynomial.C 3*Polynomial.X)
noncomputable def polyExec (r q : ℕ) (hq : 0<q) (h : ∃ n, n<q ∧ (n*n)%q=r) :
    EvalsToInTime (TM2.step machine.program) (machine.init (SquareRootAdvance.record r 0 q))
      (some (machine.halt (unary (index r q h))))
      (time.eval (SquareRootAdvance.record r 0 q).length) := by
  let L := (SquareRootAdvance.record r 0 q).length
  have hj := index_lt r q h
  have hlength : ∀ i≤ index r q h+1,
      (FlagLoop.state F i (SquareRootAdvance.record r 0 q)).length≤
        (Polynomial.C 3*Polynomial.X).eval L := by
    intro i hi
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    by_cases hil:i≤ index r q h
    · rw [state_record r q h i hil,SquareRootAdvance.record_length]
      dsimp only [L]
      rw [SquareRootAdvance.record_length]
      omega
    · have he:i=index r q h+1 := by omega
      rw [he,state_final,unary_length]
      dsimp only [L]
      rw [SquareRootAdvance.record_length]
      omega
  have hA : ∀ i≤ index r q h,
      EvalsToInTime (TM2.step SquareRootTrial.machine.program)
        (SquareRootTrial.machine.init (FlagLoop.state F i (SquareRootAdvance.record r 0 q)))
        (some (SquareRootTrial.machine.halt
          ((F (FlagLoop.state F i (SquareRootAdvance.record r 0 q))).1::
            (F (FlagLoop.state F i (SquareRootAdvance.record r 0 q))).2)))
        (SquareRootTrial.time.eval (FlagLoop.state F i (SquareRootAdvance.record r 0 q)).length) := by
    intro i hi
    rw [state_record r q h i hi]
    rw [←result_eq]
    exact SquareRootTrial.polyExec r i q hq
  have hn:index r q h≤Polynomial.X.eval L := by
    simp only [Polynomial.eval_X]
    dsimp only [L]
    rw [SquareRootAdvance.record_length]
    omega
  have hcontinue:∀ i< index r q h,
      (F (FlagLoop.state F i (SquareRootAdvance.record r 0 q))).1=false := by
    intro i hi
    rw [state_record r q h i (by omega),F_record]
    simp [before_index r q h i hi]
  have hfinal:(F (FlagLoop.state F (index r q h) (SquareRootAdvance.record r 0 q))).1=true := by
    rw [state_record r q h _ (le_refl _),F_record]
    simp [index_residue r q h]
  have hr := FlagLoop.executes_polynomial SquareRootTrial.machine SquareRootTrial.input_ne_output
    F (index r q h) (SquareRootAdvance.record r 0 q) SquareRootTrial.time Polynomial.X
      (Polynomial.C 3*Polynomial.X) hA hn hlength hcontinue hfinal
  rw [state_final] at hr
  exact hr
noncomputable def outputsInTime (r q : ℕ) (hq : 0<q) (h : ∃ n, n<q ∧ (n*n)%q=r) :
    TM2OutputsInTime machine.toFinTM2 (SquareRootAdvance.record r 0 q)
      (some (unary (index r q h))) (time.eval (SquareRootAdvance.record r 0 q).length) :=
  Machine.outputsInTime machine _ _ _ (polyExec r q hq h)
abbrev Domain := {z:ℕ×ℕ // 0<z.2 ∧ ∃ n, n<z.2 ∧ (n*n)%z.2=z.1}
def input (x : Domain) : List Bool := SquareRootAdvance.record x.val.1 0 x.val.2
def root (x : Domain) : ℕ := index x.val.1 x.val.2 x.property.2
noncomputable def computableInPolyTime : TM2ComputableInPolyTime input unary root where
  tm := machine.toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun := fun x => by
    change TM2OutputsInTime machine.toFinTM2 (List.map id (input x))
      (some (List.map id (unary (root x)))) (time.eval (input x).length)
    have h := outputsInTime x.val.1 x.val.2 x.property.1 x.property.2
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input,root] using h
end QEC.Coding.BitTuring.UnaryArithmetic.SquareRoot


