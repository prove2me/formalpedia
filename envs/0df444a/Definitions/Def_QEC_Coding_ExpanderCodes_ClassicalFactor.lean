-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalFactor
-- name    : QEC_Coding_ExpanderCodes_ClassicalFactor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:39:38.971728+00:00
-- url     : https://prove2.me/theorems/e428d8d7-dac2-4e6e-95b8-df059722f602
-- title:
--   Classical Factor
-- statement:
--   Definitions and structural lemmas for Classical Factor, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/ClassicalFactor.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear
import Definitions.Def_QEC_Coding_ExpanderCodes_ClassicalRowReduction
set_option autoImplicit false
namespace QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
open QEC.Coding.DistanceBalancing
def classicalDistanceLowerBound
    (bitCount radiusNumerator radiusDenominator : Nat) : Nat :=
  radiusNumerator * bitCount / radiusDenominator
def ClassicalFactorCertificate
    {bit check : Type}
    [Fintype bit] [DecidableEq bit]
    [Fintype check] [DecidableEq check]
    (Y : Word (ZMod 2) bit →ₗ[ZMod 2] Word (ZMod 2) check)
    (distance locality : Nat) : Prop :=
  Function.Surjective (ClassicalRowReduction.reducedBoundary Y) ∧
    ClassicalDistanceAtLeast
      (LinearMap.toMatrix' (ClassicalRowReduction.reducedBoundary Y))
      distance ∧
    Module.finrank (ZMod 2)
        (LinearMap.ker (ClassicalRowReduction.reducedBoundary Y)) ≥
      Fintype.card bit - Fintype.card check ∧
    (∀ b, HammingWeight
      (wordLinearMapTranspose (ClassicalRowReduction.reducedBoundary Y)
        (Pi.single b 1)) ≤ locality) ∧
    (∀ a, HammingWeight
      (ClassicalRowReduction.reducedBoundary Y (Pi.single a 1)) ≤ locality)
end QEC.Coding.ExpanderCodes.PK20


