-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfBijective
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfBijective
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:14:59.614636+00:00
-- url     : https://prove2.me/theorems/5c453703-e41f-4ab1-8efe-f6b3ceb9c287
-- title:
--   Wedge Of Bijective
-- statement:
--   Definitions and structural lemmas for Wedge Of Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeOfBijective.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.CompanionTheory.Hodge.WedgeField
def sqEquiv {R : Type} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (E : M ≃ₗ[R] N) : ⋀[R]^2 M ≃ₗ[R] ⋀[R]^2 N :=
  LinearEquiv.ofLinear (exteriorPower.map 2 (E : M →ₗ[R] N)) (exteriorPower.map 2 (E.symm : N →ₗ[R] M))
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])
    (by rw [← exteriorPower.map_comp]; simp [exteriorPower.map_id])
end GlobalTheory.CompanionTheory.Hodge.WedgeField


