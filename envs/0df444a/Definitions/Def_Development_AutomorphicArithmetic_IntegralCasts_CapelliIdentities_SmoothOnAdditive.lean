-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:57.893781+00:00
-- url     : https://prove2.me/theorems/16a78647-01ca-4bd0-b00b-2834d7bfada7
-- title:
--   Smooth On Additive
-- statement:
--   Definitions and structural lemmas for Smooth On Additive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SmoothOnAdditive.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.SmoothOnAdditive.SmOn.{u_1, u_3} :
    {E : Type u_1} →
      {V : Type u_3} →
        [inst : NormedAddCommGroup E] →
          [NormedSpace ℝ E] → [inst : NormedAddCommGroup V] → [NormedSpace ℝ V] → Set E → (E → V) → Prop :=
    fun {E : Type u_1} {V : Type u_3} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
        (A : Set E) (f : E → V) ↦
      ∀ a ∈ A, ∃ (U : Set E) (F : E → V), IsOpen U ∧ a ∈ U ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧ ∀ g ∈ U, g ∈ A → f g = F g
namespace UpperTheory.Reformulated.B.SmoothOnAdditive.Helpers
end UpperTheory.Reformulated.B.SmoothOnAdditive.Helpers


