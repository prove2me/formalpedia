-- Prove2me | Definitions.Def_DivideChooseBayes_pileOneValue
-- name    : DivideChooseBayes_pileOneValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:27:16.062538+00:00
-- url     : https://prove2.me/theorems/7b32159c-91c7-403f-aa02-d234b47dcc58
-- title:
--   Value of pile 1: $\sum_i p_i x_i$
-- statement:
--   For a vector of values $x\in\mathbb R^n$ (the divider's $g^D$ or the chooser's $g^C$) and a division $q$ with $p_i=q_i/2+1/2$, pile 1 is worth
--
--   $$\sum_{i=1}^n p_i\,x_i .$$
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, p.5, (ii) and the payoff paragraph

import Mathlib
import Definitions.Def_DivideChooseBayes_pOfQ

namespace DivideChooseBayes

/-- **Value of pile 1.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, p.5, (ii) and the payoff paragraph.

For values `x : ι → ℝ` (the divider's `gᴰ` or the chooser's `gᶜ`) and a division `q`, pile 1 is
worth `∑ᵢ pᵢ xᵢ` with `p = pOfQ q`. -/
noncomputable def pileOneValue {ι : Type*} [Fintype ι] (x q : ι → ℝ) : ℝ := ∑ i, pOfQ q i * x i

end DivideChooseBayes


