-- Prove2me | Definitions.Def_NisanRonen_Rounding_roundUp
-- name    : NisanRonen_Rounding_roundUp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:15:56.270239+00:00
-- url     : https://prove2.me/theorems/07d49f3f-10d4-4e72-b416-2c2edd58ccc9
-- title:
--   Rounding up to an integer multiple of $\delta$
-- statement:
--   For a grid step $\delta > 0$ and a real number $v$,
--
--   $$
--   \hat v = \delta \left\lceil \frac{v}{\delta} \right\rceil
--   $$
--
--   is $v$ **rounded up to an integer multiple of $\delta$**: the least integer multiple of $\delta$ that is at least $v$. Values already on the grid are unchanged, and $v \le \hat v < v + \delta$.
--
--   The rounding mechanism rounds every entry of the declared types, and every corrected actual time, in this way.
--
--   **Formalization Note** Only $\delta > 0$ is ever used.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, p. 192 (PDF p. 27), Notation: "let t̂ denote the vector where all entries are rounded up to an integer multiple of δ"

import Mathlib

namespace NisanRonen.Rounding

/-- **Rounding up to the δ-grid** (Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001), p. 192: "The entries t^i_j are first
rounded up to integer multiples of δ"; Notation, p. 192: "let t̂ denote the vector where all
entries are rounded up to an integer multiple of δ"). `roundUp δ v = δ · ⌈v / δ⌉`, the least
integer multiple of `δ` that is `≥ v` (for `δ > 0`); values on the grid are unchanged.

**Formalization Note** Used only with `δ > 0`; the value for `δ ≤ 0` is irrelevant. -/
noncomputable def roundUp (δ v : ℝ) : ℝ := δ * ⌈v / δ⌉

end NisanRonen.Rounding


