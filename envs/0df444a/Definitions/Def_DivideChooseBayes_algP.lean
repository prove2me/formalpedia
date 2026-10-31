-- Prove2me | Definitions.Def_DivideChooseBayes_algP
-- name    : DivideChooseBayes_algP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:26:59.926979+00:00
-- url     : https://prove2.me/theorems/87d106bf-e944-4401-9540-4fed63fdb80f
-- title:
--   Guessed probability $P_k = 1/2 - k\delta$ on iteration $k$
-- statement:
--   Algorithm 1 starts with $P=1/2$ and decreases it by $\delta$ at the end of each iteration, so on iteration $k=0,1,2,\dots$ (counted from 0)
--
--   $$P_k = \frac12 - k\,\delta .$$
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Algorithm 1, lines 2 and 11, p.9

import Mathlib
import Definitions.Def_DivideChooseBayes_algDelta

namespace DivideChooseBayes

/-- **The value of `P` on the `k`-th iteration of Algorithm 1.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Algorithm 1, lines 2 and 11, p.9: `P ← 1/2`, then `P ← P − δ` at the end of each
iteration. On iteration `k = 0, 1, 2, …` (counted from `0`), `P_k = 1/2 − k δ`. -/
noncomputable def algP {ι : Type*} [Fintype ι] (gD : ι → ℝ) (γ : ℝ) (k : ℕ) : ℝ :=
  1 / 2 - k * algDelta gD γ

end DivideChooseBayes


