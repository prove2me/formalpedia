-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_GapNum
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_SpectralGap_GapNum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:35.538224+00:00
-- url     : https://prove2.me/theorems/a68b3669-7404-4c33-8c43-d4d2934c8eb5
-- title:
--   Gap Num
-- statement:
--   Definitions and structural lemmas for Gap Num, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/SpectralGap/GapNum.lean

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
namespace ReciprocityTheory.ChartRestriction.DS.Lap
def hNum (n q : ℕ) : ℝ :=
  max (2 + max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * ((n - q : ℕ) : ℝ) * (q : ℝ)))
    (max (16 * (n : ℝ) * (min (n - q) q : ℕ) + 8 * Real.sqrt (2 * ((min (n - q) q : ℕ) : ℝ)) + 2)
      (8 * Real.sqrt (2 * ((min (n - q) q : ℕ) : ℝ)) *
        (4 * max (2 * (n : ℝ) * ((min (n - q) q : ℕ) : ℝ)) (2 * ((q : ℝ) - 1) * (n : ℝ) ^ 2) + 1)))
def GapNumStatement : Prop :=
  ∀ (n q t : ℕ) (x : ℝ), 2 ≤ n → 1 ≤ q → 2 * q ≤ n + 1 → n + 5 ≤ t →
    2 * ((n + 2 * q * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 < x → hNum n q < x
end ReciprocityTheory.ChartRestriction.DS.Lap


