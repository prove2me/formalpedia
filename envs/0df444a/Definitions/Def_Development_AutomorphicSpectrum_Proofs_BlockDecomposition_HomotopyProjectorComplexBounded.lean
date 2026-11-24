-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HomotopyProjectorComplexBounded
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HomotopyProjectorComplexBounded
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:15:14.453702+00:00
-- url     : https://prove2.me/theorems/78c9191b-a380-4c9b-9a8c-1510e303cea9
-- title:
--   Homotopy Projector Complex Bounded
-- statement:
--   Definitions and structural lemmas for Homotopy Projector Complex Bounded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HomotopyProjectorComplexBounded.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
namespace GlobalTheory.CompanionTheory.PerfRetract
section Elements
variable {R : Type} [CommRing R] {K C E : ℕ → Type}
  [∀ p, AddCommGroup (K p)] [∀ p, AddCommGroup (C p)] [∀ p, AddCommGroup (E p)]
  [∀ p, Module R (K p)] [∀ p, Module R (C p)] [∀ p, Module R (E p)]
end Elements
section Complex
variable {R : Type} [CommRing R] {E : ℕ → Type} [∀ n, AddCommGroup (E n)] [∀ n, Module R (E n)]
noncomputable def cyclesMap (d : ∀ n, E n →ₗ[R] E (n + 1))
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (r : ∀ n, E n →ₗ[R] C.X n)
    (hr : ∀ p, r (p + 1) ∘ₗ d p = (C.d p (p + 1)).hom ∘ₗ r p) (j : ℕ) :
    LinearMap.ker (d j) →ₗ[R] LinearMap.ker (C.d j (j + 1)).hom :=
  (r j ∘ₗ (LinearMap.ker (d j)).subtype).codRestrict _ fun x => by
    have h1 := LinearMap.congr_fun (hr j) x.1
    simp only [LinearMap.comp_apply] at h1
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, ← h1,
      LinearMap.mem_ker.1 x.2, map_zero]
end Complex
section Main
variable {R : Type} [CommRing R]
end Main
end GlobalTheory.CompanionTheory.PerfRetract


