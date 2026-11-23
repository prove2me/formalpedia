-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_ScGapBig
-- name    : Formalism_PeriodIntegrals_ScGapBig
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:36.970698+00:00
-- url     : https://prove2.me/theorems/13019377-3581-427e-b4a4-3ebe1714be75
-- title:
--   Sc Gap Big
-- statement:
--   Definitions and structural lemmas for Sc Gap Big, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ScGapBig.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.ScGapBig
def rk48 (k r : ℕ) : ℕ := 2 * r + k + 1
def GapBig (k r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∃ t : ℕ, Odd t ∧ rk48 k r + 5 ≤ t ∧ 1801 ≤ rk48 k r + t ∧
    ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      2 * ((rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 < b ⟨j.val + 1, hj⟩ - b j
def ScGapBig : Prop :=
  ∀ (k r : ℕ) (b : Fin (2 * r + 2) → ℝ), 1801 ≤ rk48 k r →
    (∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      16 * (rk48 k r : ℝ) ^ 19 ≤ b ⟨j.val + 1, hj⟩ - b j) →
    GapBig k r b
end PI.ScGapBig


