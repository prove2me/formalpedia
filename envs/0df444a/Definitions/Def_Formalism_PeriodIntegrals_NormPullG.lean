-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_NormPullG
-- name    : Formalism_PeriodIntegrals_NormPullG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:02.390812+00:00
-- url     : https://prove2.me/theorems/5f1f8b45-8fe2-4f2e-ab55-f25e1e15471a
-- title:
--   Norm Pull G
-- statement:
--   Definitions and structural lemmas for Norm Pull G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/NormPullG.lean

import Definitions.Def_Formalism_PeriodIntegrals_ThGDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
def NormPullG : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ (ψ : (T → I → J → ℂ) ≃ₗ[ℂ] (T → I → J → ℂ)), (∀ z w, HfG A (ψ z) (ψ w) = HfG A z w) →
    ∀ La₁ La₂ : AddSubgroup (T → I → J → ℂ), GoodLat s A La₁ → (∀ z, z ∈ La₂ ↔ ψ z ∈ La₁) →
      ∀ F ∈ ThSpG s A La₁, (fun z => F (ψ z)) ∈ ThSpG s A La₂ ∧ normSqG A La₂ (fun z => F (ψ z)) = normSqG A La₁ F
end PI


