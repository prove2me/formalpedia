-- Prove2me | Definitions.Def_DivideChooseBayes_pileTwoValue
-- name    : DivideChooseBayes_pileTwoValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:27:03.294766+00:00
-- url     : https://prove2.me/theorems/0a6df03a-196e-44e8-a2a1-2bfc531f5bc2
-- title:
--   Value of pile 2: $\sum_i (1-p_i) x_i$
-- statement:
--   For values $x\in\mathbb R^n$ and a division $q$ with $p_i=q_i/2+1/2$, pile 2 is worth
--
--   $$\sum_{i=1}^n (1-p_i)\,x_i .$$
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, p.5, (ii) and the payoff paragraph

import Mathlib
import Definitions.Def_DivideChooseBayes_pOfQ

namespace DivideChooseBayes

/-- **Value of pile 2.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, p.5, (ii) and the payoff paragraph.

For values `x : ι → ℝ` and a division `q`, pile 2 is worth `∑ᵢ (1 − pᵢ) xᵢ` with `p = pOfQ q`. -/
noncomputable def pileTwoValue {ι : Type*} [Fintype ι] (x q : ι → ℝ) : ℝ := ∑ i, (1 - pOfQ q i) * x i

end DivideChooseBayes


