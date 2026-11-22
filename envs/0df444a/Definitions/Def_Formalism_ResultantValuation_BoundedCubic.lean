-- Prove2me | Definitions.Def_Formalism_ResultantValuation_BoundedCubic
-- name    : Formalism_ResultantValuation_BoundedCubic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:09:50.927805+00:00
-- url     : https://prove2.me/theorems/4855b9e0-e5c5-47b9-855c-de31a9343a8f
-- title:
--   Bounded Cubic
-- statement:
--   Definitions and structural lemmas for Bounded Cubic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/BoundedCubic.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.ResultantValuation
def thirdDiff {G : Type} [AddCommGroup G] (φ : G → ℝ) (x y z : G) : ℝ :=
  φ (x + y + z) - φ (x + y) - φ (x + z) - φ (y + z) + φ x + φ y + φ z - φ 0
def BoundedCubic : Prop :=
  ∀ (G : Type) [AddCommGroup G] (φ : G → ℝ), (∃ C : ℝ, ∀ x, |φ x| ≤ C) →
    (∃ c : ℝ, ∀ x y z, thirdDiff φ x y z = c) → ∀ x, φ x = φ 0
end Formalism.ResultantValuation


