-- Prove2me | Definitions.Def_DivideChooseBayes_cpObjective
-- name    : DivideChooseBayes_cpObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:26:15.942302+00:00
-- url     : https://prove2.me/theorems/431db2a3-3e98-4668-a591-04500fa21bc4
-- title:
--   Objective $u_P$ of the program $\mathcal C_P$
-- statement:
--   For divider values $g^D$ and a guessed probability $P$, the objective of the program $\mathcal C_P$ in Algorithm 1 is
--
--   $$u_P(q)=\sum_{i=1}^n \frac{g^D_i}{2}\big(P(1-q_i)+(1-P)(1+q_i)\big).$$
--
--   It is the divider's interim expected utility of $q$ if the chooser picked pile 1 with probability exactly $P$.
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Algorithm 1, line 5, p.9

import Mathlib

namespace DivideChooseBayes

/-- **The objective `u_P` of the program `C_P`.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Algorithm 1, line 5, p.9 (also p.8):
`u_P = ∑ᵢ (gᴰᵢ/2) (P (1 − qᵢ) + (1 − P) (1 + qᵢ))`. -/
noncomputable def cpObjective {ι : Type*} [Fintype ι] (gD : ι → ℝ) (P : ℝ) (q : ι → ℝ) : ℝ :=
  ∑ i, gD i / 2 * (P * (1 - q i) + (1 - P) * (1 + q i))

end DivideChooseBayes


