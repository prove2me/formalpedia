-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryProductSearch
-- name    : QEC_Coding_BitTuring_UnaryProductSearch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:15:44.824858+00:00
-- url     : https://prove2.me/theorems/9292719e-a493-4db9-b633-fd104bf89b85
-- title:
--   Unary Product Search
-- statement:
--   Definitions and structural lemmas for Unary Product Search, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryProductSearch.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryProductTrial
import Definitions.Def_QEC_Coding_BitTuring_UnarySquareRoot
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_ProductTrial_input_ne_output
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_SquareRootTrial_input_ne_output
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_unary_length

set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.ProductSearch
open Turing StateTransition
open SquareRoot (readNat afterNat readNat_prefix afterNat_prefix readNat_unary state_succ_after)
theorem record_eq (r a b q : ℕ) : ProductAdvance.record r a b q=
    UnaryOutputEquality.prefixInput r
      (UnaryOutputEquality.prefixInput a (UnaryOutputEquality.prefixInput b (unary q))) := by rfl
def F (w : List Bool) : Bool×List Bool :=
  let r := readNat w
  let a := readNat (afterNat w)
  let b := readNat (afterNat (afterNat w))
  let q := readNat (afterNat (afterNat (afterNat w)))
  if (a*b)%q=r then (true,unary a) else (false,ProductAdvance.record r (a+1) b q)
theorem F_record (r a b q : ℕ) : F (ProductAdvance.record r a b q)=
    if (a*b)%q=r then (true,unary a) else (false,ProductAdvance.record r (a+1) b q) := by
  simp only [F,record_eq,readNat_prefix,afterNat_prefix,readNat_unary]
theorem result_eq (r a b q : ℕ) : ProductTrial.result r a b q=
    (F (ProductAdvance.record r a b q)).1::(F (ProductAdvance.record r a b q)).2 := by
  rw [F_record]
  by_cases h:(a*b)%q=r <;> simp [ProductTrial.result,ProductAdvance.output,h]
def index (r b q : ℕ) (h : ∃ n, n<q ∧ (n*b)%q=r) : ℕ := Nat.find h
theorem index_lt (r b q : ℕ) (h : ∃ n, n<q ∧ (n*b)%q=r) : index r b q h<q :=
  (Nat.find_spec h).1
theorem index_residue (r b q : ℕ) (h : ∃ n, n<q ∧ (n*b)%q=r) :
    ((index r b q h)*b)%q=r := (Nat.find_spec h).2
theorem before_index (r b q : ℕ) (h : ∃ n, n<q ∧ (n*b)%q=r) (i : ℕ) (hi : i< index r b q h) :
    (i*b)%q≠r := by
  intro he
  exact Nat.find_min h hi ⟨hi.trans (index_lt r b q h),he⟩
theorem state_record (r b q : ℕ) (h : ∃ n, n<q ∧ (n*b)%q=r) (i : ℕ) (hi : i≤ index r b q h) :
    FlagLoop.state F i (ProductAdvance.record r 0 b q)=ProductAdvance.record r i b q := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [state_succ_after]
      rw [ih (by omega),F_record]
      simp [before_index r b q h i (by omega)]
theorem state_final (r b q : ℕ) (h : ∃ n, n<q ∧ (n*b)%q=r) :
    FlagLoop.state F (index r b q h+1) (ProductAdvance.record r 0 b q)=unary (index r b q h) := by
  rw [state_succ_after,state_record r b q h _ (le_refl _),F_record]
  simp [index_residue r b q h]
def machine : Machine := FlagLoop.machine ProductTrial.machine
noncomputable def time : Polynomial ℕ :=
  FlagLoop.timePolynomial ProductTrial.time Polynomial.X (Polynomial.C 3*Polynomial.X)
noncomputable def polyExec (r b q : ℕ) (hq : 0<q) (h : ∃ n, n<q ∧ (n*b)%q=r) :
    EvalsToInTime (TM2.step machine.program) (machine.init (ProductAdvance.record r 0 b q))
      (some (machine.halt (unary (index r b q h))))
      (time.eval (ProductAdvance.record r 0 b q).length) := by
  let L := (ProductAdvance.record r 0 b q).length
  have hj := index_lt r b q h
  have hlength : ∀ i≤ index r b q h+1,
      (FlagLoop.state F i (ProductAdvance.record r 0 b q)).length≤
        (Polynomial.C 3*Polynomial.X).eval L := by
    intro i hi
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    by_cases hil:i≤ index r b q h
    · rw [state_record r b q h i hil,ProductAdvance.record_length]
      dsimp only [L]
      rw [ProductAdvance.record_length]
      omega
    · have he:i=index r b q h+1 := by omega
      rw [he,state_final,unary_length]
      dsimp only [L]
      rw [ProductAdvance.record_length]
      omega
  have hA : ∀ i≤ index r b q h,
      EvalsToInTime (TM2.step ProductTrial.machine.program)
        (ProductTrial.machine.init (FlagLoop.state F i (ProductAdvance.record r 0 b q)))
        (some (ProductTrial.machine.halt
          ((F (FlagLoop.state F i (ProductAdvance.record r 0 b q))).1::
            (F (FlagLoop.state F i (ProductAdvance.record r 0 b q))).2)))
        (ProductTrial.time.eval (FlagLoop.state F i (ProductAdvance.record r 0 b q)).length) := by
    intro i hi
    rw [state_record r b q h i hi]
    rw [←result_eq]
    exact ProductTrial.polyExec r i b q hq
  have hn:index r b q h≤Polynomial.X.eval L := by
    simp only [Polynomial.eval_X]
    dsimp only [L]
    rw [ProductAdvance.record_length]
    omega
  have hcontinue:∀ i< index r b q h,
      (F (FlagLoop.state F i (ProductAdvance.record r 0 b q))).1=false := by
    intro i hi
    rw [state_record r b q h i (by omega),F_record]
    simp [before_index r b q h i hi]
  have hfinal:(F (FlagLoop.state F (index r b q h) (ProductAdvance.record r 0 b q))).1=true := by
    rw [state_record r b q h _ (le_refl _),F_record]
    simp [index_residue r b q h]
  have hr := FlagLoop.executes_polynomial ProductTrial.machine ProductTrial.input_ne_output
    F (index r b q h) (ProductAdvance.record r 0 b q) ProductTrial.time Polynomial.X
      (Polynomial.C 3*Polynomial.X) hA hn hlength hcontinue hfinal
  rw [state_final] at hr
  exact hr
noncomputable def outputsInTime (r b q : ℕ) (hq : 0<q) (h : ∃ n, n<q ∧ (n*b)%q=r) :
    TM2OutputsInTime machine.toFinTM2 (ProductAdvance.record r 0 b q)
      (some (unary (index r b q h))) (time.eval (ProductAdvance.record r 0 b q).length) :=
  Machine.outputsInTime machine _ _ _ (polyExec r b q hq h)
abbrev Domain := {z:ℕ×(ℕ×ℕ) // 0<z.2.2 ∧ ∃ n, n<z.2.2 ∧ (n*z.2.1)%z.2.2=z.1}
def input (x : Domain) : List Bool := ProductAdvance.record x.val.1 0 x.val.2.1 x.val.2.2
def root (x : Domain) : ℕ := index x.val.1 x.val.2.1 x.val.2.2 x.property.2
noncomputable def computableInPolyTime : TM2ComputableInPolyTime input unary root where
  tm := machine.toFinTM2
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun := fun x => by
    change TM2OutputsInTime machine.toFinTM2 (List.map id (input x))
      (some (List.map id (unary (root x)))) (time.eval (input x).length)
    have h := outputsInTime x.val.1 x.val.2.1 x.val.2.2 x.property.1 x.property.2
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input,root] using h
end QEC.Coding.BitTuring.UnaryArithmetic.ProductSearch


