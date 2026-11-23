-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_SchurClosable
-- name    : Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_SchurClosable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:20.024156+00:00
-- url     : https://prove2.me/theorems/d1066deb-0da7-4e2e-bd60-799bf5dca577
-- title:
--   Schur Closable
-- statement:
--   Definitions and structural lemmas for Schur Closable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/HaarTransfer/SchurClosable.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.IndefR.Leaf
open Filter Topology
def SchurClosable : Prop :=
  ∀ (G H H' : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (π : G →* (H →L[ℂ] H)) (π' : G →* (H' →L[ℂ] H')),
    (∀ g x, ‖π g x‖ = ‖x‖) → (∀ g x, ‖π' g x‖ = ‖x‖) →
    (∀ B : H →L[ℂ] H, (∀ g, B.comp (π g) = (π g).comp B) → ∃ c : ℂ, B = c • ContinuousLinearMap.id ℂ H) →
    ∀ (D : Submodule ℂ H) (A : D →ₗ[ℂ] H'), Dense (D : Set H) →
      (∀ g, ∀ x ∈ D, π g x ∈ D) →
      (∀ g (x : D) (hx : π g x ∈ D), A ⟨π g x, hx⟩ = π' g (A x)) →
      (∀ (u : ℕ → D) (y : H'), Tendsto (fun n => (u n : H)) atTop (𝓝 0) →
        Tendsto (fun n => A (u n)) atTop (𝓝 y) → y = 0) →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : D, inner ℂ (A x) (A y) = (c : ℂ) * inner ℂ (x : H) (y : H)
end Formalism.IndefR.Leaf


