-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsMixedTopAlgebra
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsMixedTopAlgebra
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:35.297741+00:00
-- url     : https://prove2.me/theorems/1dbcc3dc-0ba8-4b5e-8127-52c3be6e4de7
-- title:
--   Statements Mixed Top Algebra
-- statement:
--   Definitions and structural lemmas for Statements Mixed Top Algebra, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsMixedTopAlgebra.lean

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
def MixedTopAlgebra.Statement : Prop :=
  ∀ (d : ℕ) (m : ℕ → ℝ), 2 ≤ d → (∀ i, 1 ≤ i → i ≤ d → 0 ≤ m i) → 0 < m d →
    (∀ q p : ℕ, 1 ≤ q → 1 ≤ p →
      0 < ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * (q : ℝ) ^ (d - i) * (p : ℝ) ^ i * m i →
      0 ≤ ∑ i ∈ Finset.range d, ((d - 1).choose i : ℝ) * (q : ℝ) ^ (d - 1 - i) * (p : ℝ) ^ i * m i) →
    0 ≤ m 0
end GroundTheory.Heights₂.Heights.HilbertSamuel


