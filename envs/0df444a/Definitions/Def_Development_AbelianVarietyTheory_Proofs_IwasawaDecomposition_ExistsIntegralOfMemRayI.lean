-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIntegralOfMemRayI
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIntegralOfMemRayI
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:20.872899+00:00
-- url     : https://prove2.me/theorems/eb1993bc-6165-48da-b244-08ab7cb39810
-- title:
--   Exists Integral Of Mem Ray I
-- statement:
--   Definitions and structural lemmas for Exists Integral Of Mem Ray I, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIntegralOfMemRayI.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GlobalTheory.Mem.RayData
section aux
variable {K : Type} [Field K] [NumberField K]
def idealUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.2 hI)
open NumberField IsDedekindDomain in
open scoped nonZeroDivisors in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Mem.RayData.span_ne_bot {a : 𝓞 K} (ha : a ≠ 0) : Ideal.span {a} ≠ ⊥ := by
  rwa [Ne, Ideal.span_singleton_eq_bot]
variable {M : ℕ} (D : RayData K M)
end aux
end GlobalTheory.Mem.RayData
end


