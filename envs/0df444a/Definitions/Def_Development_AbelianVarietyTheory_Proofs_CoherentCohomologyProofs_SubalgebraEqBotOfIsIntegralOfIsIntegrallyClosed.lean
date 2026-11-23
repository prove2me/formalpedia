-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:09:46.628156+00:00
-- url     : https://prove2.me/theorems/e43d396a-3bfb-4384-b383-ddd854a4870b
-- title:
--   Subalgebra Eq Bot Of Is Integral Of Is Integrally Closed
-- statement:
--   Definitions and structural lemmas for Subalgebra Eq Bot Of Is Integral Of Is Integrally Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SubalgebraEqBotOfIsIntegralOfIsIntegrallyClosed.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries TensorProduct
namespace GlobalTheory
section Contraction
variable {A : Type*} [CommRing A] (M : Submonoid A) {S : Type*} [CommRing S] [Algebra A S]
  [IsLocalization M S]
end Contraction
section PowerSeries
open PowerSeries IsLocalRing
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
section Away
variable {ϖ : O} (hϖ : Irreducible ϖ) (S : Type*) [CommRing S] [Algebra O⟦X⟧ S]
  [IsLocalization.Away (C ϖ : O⟦X⟧) S]
include hϖ
variable (𝔭 : Ideal S) [𝔭.IsPrime] (h𝔭 : 𝔭 = Ideal.span {algebraMap O⟦X⟧ S X})
  (V : Type*) [CommRing V] [Algebra S V] [IsLocalization.AtPrime V 𝔭]
include h𝔭
end Away
end PowerSeries
universe u
end GlobalTheory


