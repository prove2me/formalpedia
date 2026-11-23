-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_MirabolicDerivatives_TwistedKernels_TwKerLeComapOf
-- name    : Development_WeilBound_CoreStatements_TemperedRepresentationTheory_MirabolicDerivatives_TwistedKernels_TwKerLeComapOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:32.136808+00:00
-- url     : https://prove2.me/theorems/30be9e03-1a93-4778-8c8b-e4d304e79c94
-- title:
--   Tw Ker Le Comap Of
-- statement:
--   Definitions and structural lemmas for Tw Ker Le Comap Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/TemperedRepresentationTheory/MirabolicDerivatives/TwistedKernels/TwKerLeComapOf.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
namespace GlobalTheory.BZMir
variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
theorem twKer_le_comap_of (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (N : Subgroup G) (θ : N →* ℂˣ)
    (f : V →ₗ[ℂ] W) (hf : ∀ g v, f (ρ g v) = σ g (f v)) : twKer ρ N θ ≤ (twKer σ N θ).comap f := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨n, v, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  refine Submodule.subset_span ⟨n, f v, ?_⟩
  rw [map_sub, map_smul, hf]
def twMap (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (N : Subgroup G) (θ : N →* ℂˣ)
    (f : V →ₗ[ℂ] W) (hf : ∀ g v, f (ρ g v) = σ g (f v)) : TwJacquet ρ N θ →ₗ[ℂ] TwJacquet σ N θ :=
  (twKer ρ N θ).mapQ (twKer σ N θ) f (twKer_le_comap_of ρ σ N θ f hf)
end GlobalTheory.BZMir
end


