-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolyNonnegAtZero
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPolyNonnegAtZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:03.50095+00:00
-- url     : https://prove2.me/theorems/42b17817-4eda-4448-b6c8-58b95e6ccf53
-- title:
--   Statements Poly Nonneg At Zero
-- statement:
--   Definitions and structural lemmas for Statements Poly Nonneg At Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsPolyNonnegAtZero.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open Filter
def PolyNonnegAtZero.Statement : Prop :=
  ∀ (d : ℕ) (p : Polynomial ℝ) (c : ℝ), 0 < c →
    (∀ t : ℚ, 0 < t → 0 < p.eval (t : ℝ) → c * (t : ℝ) ^ d ≤ p.eval (t : ℝ)) →
    (∀ᶠ t in atTop, 0 < p.eval t) → 0 ≤ p.eval 0
end GroundTheory.Heights₂.Heights.HilbertSamuel


