-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryFieldInverse
-- name    : QEC_Coding_BitTuring_UnaryFieldInverse
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:30:36.662662+00:00
-- url     : https://prove2.me/theorems/b0fb737c-8638-4d7e-aa52-a4fcfbb6ad5c
-- title:
--   Unary Field Inverse
-- statement:
--   Definitions and structural lemmas for Unary Field Inverse, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryFieldInverse.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryProductSearch
import Definitions.Def_QEC_Coding_BitTuring_UnaryInverseInput
import Mathlib.Algebra.Field.ZMod
set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.InverseSearch
open Turing StateTransition
theorem exists_candidate (q b : ℕ) (hq : q.Prime) (hb : (b:ZMod q)≠0) :
    ∃ n, n<q ∧ (n*b)%q=1 := by
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  refine ⟨((b:ZMod q)⁻¹).val,ZMod.val_lt _,?_⟩
  apply (ModularTrial.product_eq_iff _ b 1 q hq.pos hq.one_lt).mpr
  simp only [ZMod.natCast_zmod_val,Nat.cast_one]
  exact inv_mul_cancel₀ hb
theorem index_eq_inverse (q b : ℕ) (hq : q.Prime) (hb : (b:ZMod q)≠0) :
    ProductSearch.index 1 b q (exists_candidate q b hq hb)=((b:ZMod q)⁻¹).val := by
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  have h := (ModularTrial.product_eq_iff _ b 1 q hq.pos hq.one_lt).mp
    (ProductSearch.index_residue 1 b q (exists_candidate q b hq hb))
  have he : (ProductSearch.index 1 b q (exists_candidate q b hq hb):ZMod q)=(b:ZMod q)⁻¹ := by
    have hh := congrArg (fun z:ZMod q => z*(b:ZMod q)⁻¹) h
    simpa only [mul_assoc,mul_inv_cancel₀ hb,mul_one,Nat.cast_one,one_mul] using hh
  have hh := congrArg ZMod.val he
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt
    (ProductSearch.index_lt 1 b q (exists_candidate q b hq hb))] using hh
noncomputable def polyExec (q b : ℕ) (hq : q.Prime) (hb : (b:ZMod q)≠0) :
    EvalsToInTime (TM2.step ProductSearch.machine.program)
      (ProductSearch.machine.init (ProductAdvance.record 1 0 b q))
      (some (ProductSearch.machine.halt (unary ((b:ZMod q)⁻¹).val)))
      (ProductSearch.time.eval (ProductAdvance.record 1 0 b q).length) := by
  have h := ProductSearch.polyExec 1 b q hq.pos (exists_candidate q b hq hb)
  rwa [index_eq_inverse q b hq hb] at h
end QEC.Coding.BitTuring.UnaryArithmetic.InverseSearch
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularInverse
open Turing StateTransition
def machine : Machine := Composition.machine InverseInput.machine ProductSearch.machine
noncomputable def size : Polynomial ℕ := Polynomial.X+Polynomial.C 3
noncomputable def time : Polynomial ℕ :=
  ProductSearch.time.comp size+Polynomial.C 2*size+Polynomial.C 2*Polynomial.X+Polynomial.C 3
noncomputable def polyExec (q u:ℕ) (hq:q.Prime) (hu:(u:ZMod q)≠0) :
    EvalsToInTime (TM2.step machine.program) (machine.init (pairInput u q))
      (some (machine.halt (unary ((u:ZMod q)⁻¹).val))) (time.eval (pairInput u q).length) := by
  have h := Composition.executes InverseInput.machine ProductSearch.machine _ _ _ _ _
    (InverseInput.exec u q) (InverseSearch.polyExec q u hq hu)
  refine {h with steps_le_m:=h.steps_le_m.trans ?_}
  simp only [ProductAdvance.record_length,pairInput_length,time,size,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_comp]
  have he:1+0+u+q+3=u+q+1+3 := by omega
  rw [he];omega
noncomputable def outputsInTime (q u:ℕ) (hq:q.Prime) (hu:(u:ZMod q)≠0) :
    TM2OutputsInTime machine.toFinTM2 (pairInput u q) (some (unary ((u:ZMod q)⁻¹).val))
      (time.eval (pairInput u q).length) := Machine.outputsInTime machine _ _ _ (polyExec q u hq hu)
abbrev Domain := {z:ℕ×ℕ // z.2.Prime ∧ z.1<z.2 ∧ (z.1:ZMod z.2)≠0}
def input (x:Domain) : List Bool := pairInput x.val.1 x.val.2
def inverse (x:Domain) : ℕ := ((x.val.1:ZMod x.val.2)⁻¹).val
noncomputable def computableInPolyTime : TM2ComputableInPolyTime input unary inverse where
  tm:=machine.toFinTM2
  inputAlphabet:=Equiv.refl Bool
  outputAlphabet:=Equiv.refl Bool
  time:=time
  outputsFun:=fun x => by
    change TM2OutputsInTime machine.toFinTM2 (List.map id (input x))
      (some (List.map id (unary (inverse x)))) (time.eval (input x).length)
    have h:=outputsInTime x.val.2 x.val.1 x.property.1 x.property.2.2
    dsimp only [Machine.toFinTM2] at h ⊢
    simpa only [List.map_id,input,inverse] using h
end QEC.Coding.BitTuring.UnaryArithmetic.ModularInverse


