-- Prove2me | Definitions.Def_SkipListConc_heightPMF
-- name    : SkipListConc_heightPMF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:51.342926+00:00
-- url     : https://prove2.me/theorems/5b93b0dc-a50b-431a-ba2d-842cbc970719
-- title:
--   Distribution of $H_x(j)$ as point masses
-- statement:
--   The distribution of the height $H_x(j)$ of item $x$ after $j$ operations, as the sequence of point masses $\ell\mapsto\Pr[H_x(j)=\ell]$, $\ell\ge 0$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §3, pp.16–17

import Mathlib
import Definitions.Def_SkipListConc_height

open MeasureTheory

namespace SkipListConc

/-- The distribution of `H_x(j)` as point masses, `ℓ ↦ Pr[H_x(j) = ℓ]` (Kapoor–Tanveer,
*Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript
(sha256 f82c3d35…6dab6c), §3, pp.16–17). -/
noncomputable def heightPMF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : ℝ) {K : ℕ}
    {α : Type*} (ξ : α × ℕ → Ω → ℝ × (ℕ → Fin K) × ℕ) (x : α) (j : ℕ) (ℓ : ℕ) : ℝ :=
  (P {ω | height p ξ x j ω = ℓ}).toReal

end SkipListConc


