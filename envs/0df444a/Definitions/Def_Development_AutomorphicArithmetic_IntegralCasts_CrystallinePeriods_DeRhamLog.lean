-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamLog
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamLog
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T09:51:15.376169+00:00
-- url     : https://prove2.me/theorems/a484705d-4db0-5280-aceb-8e9c01d49088
-- title:
--   De Rham Log
-- statement:
--   Definitions and structural lemmas for De Rham Log, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRhamLog.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamMap
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_ExistsFactorialMulEqPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal Polynomial
namespace Reformulated.AutPerF
universe u v
section Trunc
variable {B : Type*} [CommRing B] [Algebra ℚ B]
end Trunc
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
namespace BdRPlus
def logTeich (η : tateModule p R) : BdRPlus p R :=
  log (algebraMap (Ainf p R) _ (Ainf.teich p η.1)) (by
    rw [IsScalarTower.algebraMap_apply _ (AinfInv p R), theta_algebraMap, AinfInv.theta_algebraMap,
      Ainf.theta_teich, show PreTilt.untilt η.1 = 1 from η.2, map_one])
theorem p_mul_inv : (p : BdRPlus p R) * algebraMap ℚ_[p] _ (p : ℚ_[p])⁻¹ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] (BdRPlus p R)), ← map_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero), map_one]
def teichDivP (ϖ : PFlat p R) : BdRPlus p R :=
  algebraMap (Ainf p R) _ (Ainf.teich p ϖ.1) * algebraMap ℚ_[p] _ (p : ℚ_[p])⁻¹
theorem theta_teichDivP (ϖ : PFlat p R) : theta p R (teichDivP ϖ) = 1 := by
  rw [teichDivP, map_mul, IsScalarTower.algebraMap_apply _ (AinfInv p R), theta_algebraMap,
    AinfInv.theta_algebraMap, Ainf.theta_teich, ϖ.2, map_natCast, ← map_natCast (theta p R),
    ← map_mul, p_mul_inv, map_one]
def logFlat (ϖ : PFlat p R) : BdRPlus p R := log (teichDivP ϖ) (theta_teichDivP ϖ)
end BdRPlus
end Reformulated.AutPerF


