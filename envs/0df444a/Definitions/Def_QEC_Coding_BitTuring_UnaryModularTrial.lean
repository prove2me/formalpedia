-- Prove2me | Definitions.Def_QEC_Coding_BitTuring_UnaryModularTrial
-- name    : QEC_Coding_BitTuring_UnaryModularTrial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:07:18.556202+00:00
-- url     : https://prove2.me/theorems/0687490d-6954-4e70-8b2a-c13739688a1e
-- title:
--   Unary Modular Trial
-- statement:
--   Definitions and structural lemmas for Unary Modular Trial, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BitTuring/UnaryModularTrial.lean

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryModularProduct
set_option autoImplicit false
namespace QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial
open Turing StateTransition
open UnaryOutputEquality
def machine : Machine := UnaryOutputEquality.machine ModularProduct.machine
noncomputable def time : Polynomial ℕ := timePolynomial ModularProduct.machine ModularProduct.time
def input (a b r q : ℕ) : List Bool := prefixInput r (FactorTest.tripleInput a b q)
noncomputable def polyExec (a b r q : ℕ) (hq : 0<q) :
    EvalsToInTime (TM2.step machine.program) (machine.init (input a b r q))
      (some (machine.halt [decide ((a*b)%q=r)])) (time.eval (input a b r q).length) :=
  executes_polynomial ModularProduct.machine r ((a*b)%q) _ ModularProduct.time
    (ModularProduct.polyExec a b q hq)
noncomputable def outputsInTime (a b r q : ℕ) (hq : 0<q) :
    TM2OutputsInTime machine.toFinTM2 (input a b r q)
      (some [decide ((a*b)%q=r)]) (time.eval (input a b r q).length) :=
  Machine.outputsInTime machine _ _ _ (polyExec a b r q hq)
theorem product_eq_iff (a b r q : ℕ) (hq : 0<q) (hr : r<q) :
    ((a*b)%q=r) ↔ ((a:ZMod q)*(b:ZMod q)=(r:ZMod q)) := by
  let : NeZero q := ⟨hq.ne'⟩
  constructor
  · intro h
    apply ZMod.val_injective q
    simpa only [←Nat.cast_mul,ZMod.val_natCast,Nat.mod_eq_of_lt hr] using h
  · intro h
    have hh := congrArg ZMod.val h
    simpa only [←Nat.cast_mul,ZMod.val_natCast,Nat.mod_eq_of_lt hr] using hh
noncomputable def outputsZModProductInTime (a b r q : ℕ) (hq : 0<q) (hr : r<q) :
    TM2OutputsInTime machine.toFinTM2 (input a b r q)
      (some [decide ((a:ZMod q)*(b:ZMod q)=(r:ZMod q))]) (time.eval (input a b r q).length) := by
  simpa only [product_eq_iff a b r q hq hr] using outputsInTime a b r q hq
noncomputable def outputsZModSquareInTime (a r q : ℕ) (hq : 0<q) (hr : r<q) :
    TM2OutputsInTime machine.toFinTM2 (input a a r q)
      (some [decide ((a:ZMod q)^2=(r:ZMod q))]) (time.eval (input a a r q).length) := by
  simpa only [pow_two] using outputsZModProductInTime a a r q hq hr
noncomputable def productComputableInPolyTime :
    TM2ComputableInPolyTime (UnaryOutputEquality.input ModularProduct.input)
      FactorTest.boolBits
      (fun z:(ℕ×(ℕ×ℕ+))×ℕ => decide ((z.1.1*z.1.2.1)%z.1.2.2.val=z.2)) :=
  computableInPolyTime ModularProduct.machine ModularProduct.input
    (fun x => (x.1*x.2.1)%x.2.2.val) ModularProduct.time
    (fun x => ModularProduct.polyExec x.1 x.2.1 x.2.2.val x.2.2.pos)
def squareInput (x : ℕ×ℕ+) : List Bool := FactorTest.tripleInput x.1 x.1 x.2.val
noncomputable def squareComputableInPolyTime :
    TM2ComputableInPolyTime (UnaryOutputEquality.input squareInput) FactorTest.boolBits
      (fun z:(ℕ×ℕ+)×ℕ => decide ((z.1.1*z.1.1)%z.1.2.val=z.2)) :=
  computableInPolyTime ModularProduct.machine squareInput
    (fun x => (x.1*x.1)%x.2.val) ModularProduct.time
    (fun x => ModularProduct.polyExec x.1 x.1 x.2.val x.2.pos)
def steps (a b r q : ℕ) : ℕ := ModularProduct.steps a b q+r+max ((a*b)%q) r+3
end QEC.Coding.BitTuring.UnaryArithmetic.ModularTrial


