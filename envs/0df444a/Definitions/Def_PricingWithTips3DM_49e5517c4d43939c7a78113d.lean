-- Prove2me | Definitions.Def_PricingWithTips3DM_49e5517c4d43939c7a78113d
-- name    : PricingWithTips3DM_49e5517c4d43939c7a78113d
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:45:09.026533+00:00
-- url     : https://prove2.me/theorems/f028ae17-4183-4751-ba3f-1770824a6c5d
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OneHotPredicate
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_a46ec1070e8b9fcb3ebc4d0c
import Definitions.Def_PricingWithTips3DM_f343fdd0ddecda3ae03e650c
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Concrete serialization of Boolean queries over one-hot families

A static predicate selects one sparse source-wire fiber.  The arbitrary-list
OR controller serializes that fiber exactly, including the all-false predicate
whose operand list is empty.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

def affineOneHotPredicateCanonicalFrames {n : Nat} (start : Nat)
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool) :
    List AffineOrFinPairFrame :=
  affineOrFinCanonicalFrames start (oneHotPredicateWires source f)

theorem affineOneHotPredicateGateStream_eq_trace {n : Nat} (start : Nat)
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool) :
    affineOrFinGateStream
        (affineOneHotPredicateCanonicalFrames start source f) =
      (CircuitBuilder.disjunctionGateTrace start
        (oneHotPredicateWires source f)).gates.flatMap
          encodeCircuitGate :=
  affineOrFinCanonicalGateStream_eq_trace start _

/-- Execute the exact semantic suffix of a one-hot predicate query. -/
def affineOneHotPredicate_run {n : Nat} (start : Nat)
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool)
    (output : List CircuitSym) :
    EvalsToInTime (step affineOrFinRevProgram)
      (affineOrFinLoopCfg
        (encodeAffineOrFinFrames
          (affineOneHotPredicateCanonicalFrames start source f)) output)
      (some (haltCfg affineOrFinRevProgram
        (((CircuitBuilder.disjunctionGateTrace start
          (oneHotPredicateWires source f)).gates.flatMap
            encodeCircuitGate).reverse ++ output)))
      (affineOrFinRevSteps
        (affineOneHotPredicateCanonicalFrames start source f)) := by
  simpa [affineOneHotPredicateCanonicalFrames] using
    affineOrFinCanonical_run start (oneHotPredicateWires source f) output

theorem affineOneHotPredicate_steps_le {n : Nat} (start : Nat)
    (source : Fin n → CircuitBuilder.Wire) (f : Fin n → Bool) :
    affineOrFinRevSteps
        (affineOneHotPredicateCanonicalFrames start source f) ≤
      100 * (encodeAffineOrFinFrames
        (affineOneHotPredicateCanonicalFrames start source f)).length + 3 :=
  affineOrFinRev_steps_le _

end CLRS.Chapter34.Turing.PolyBuilder


