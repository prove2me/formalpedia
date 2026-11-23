-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisCohomologyLocalizationExact
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaloisCohomologyLocalizationExact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:43.65574+00:00
-- url     : https://prove2.me/theorems/6904c282-795b-4d76-a191-707428928e39
-- title:
--   Galois Cohomology Localization Exact
-- statement:
--   Definitions and structural lemmas for Galois Cohomology Localization Exact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaloisCohomologyLocalizationExact.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_PairSums_SumPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.S2pt
namespace GlobalTheory.CompanionTheory.LocalPerfect
section General
variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [DiscreteTopology M]
  {D : Type*} [Group D] [TopologicalSpace D]
  (χ : Γ →* Rˣ) (ρ : Representation R Γ M) (φ : D →* Γ) (χ' : D →* Rˣ)
theorem twDual_comp_apply (h : χ.comp φ = χ') (g : D) (y : TDual R M) :
    ((twDual χ ρ).comp φ) g y = ((twDual χ' (ρ.comp φ)).comp (MonoidHom.id D)) g y := by
  subst h
  ext m
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, twDual_apply, map_inv]
def dualMap (h : χ.comp φ = χ') :
    H1 ((twDual χ ρ).comp φ) →ₗ[R] H1 ((twDual χ' (ρ.comp φ)).comp (MonoidHom.id D)) :=
  mapH1 _ _ LinearMap.id continuous_id (twDual_comp_apply χ ρ φ χ' h)
def coefMap : H1 (ρ.comp φ) →ₗ[R] H1 ((ρ.comp φ).comp (MonoidHom.id D)) :=
  mapH1 _ _ LinearMap.id continuous_id (fun _ _ => rfl)
end General
end GlobalTheory.CompanionTheory.LocalPerfect
end


