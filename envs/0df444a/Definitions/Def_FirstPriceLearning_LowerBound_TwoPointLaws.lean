-- Prove2me | Definitions.Def_FirstPriceLearning_LowerBound_TwoPointLaws
-- name    : FirstPriceLearning_LowerBound_TwoPointLaws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:37.058029+00:00
-- url     : https://prove2.me/theorems/139b0bdc-ba06-4bb9-916f-3f6ba04f90cb
-- title:
--   The two HOB laws $G_1, G_2$ of Le Cam's two-point argument (App. B)
-- statement:
--   For a parameter $\Delta$, let $G_1$ and $G_2$ be the laws of a highest other bid taking values in $\{1/3,2/3\}$:
--
--   $$
--   G_1=\bigl(\tfrac12+\Delta\bigr)\delta_{1/3}+\bigl(\tfrac12-\Delta\bigr)\delta_{2/3},\qquad
--   G_2=\bigl(\tfrac12-\Delta\bigr)\delta_{1/3}+\bigl(\tfrac12+\Delta\bigr)\delta_{2/3}.
--   $$
--
--   Their CDFs are $G_1(x)=0$ for $0\le x<1/3$, $\tfrac12+\Delta$ for $1/3\le x<2/3$, $1$ for $x\ge2/3$, and the same with $\tfrac12-\Delta$ for $G_2$. For $\Delta\in(0,1/4)$ both are probability measures supported on $[0,1]$. They are the two hypotheses of the two-point lower bound for Theorem 9.
--
--   **Formalization Note** Both laws are instances of `twoPointLaw p`, the measure with mass $p$ at $1/3$ and $1-p$ at $2/3$, with the masses taken in $\mathbb R_{\ge0}$ (`Real.toNNReal`), so `twoPointLaw p` is a probability measure exactly when $0\le p\le1$. `Solutions/verification` checks the probability and support properties and the middle value of each CDF.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, pp. 36–37, App. B, definitions of G1, G2

import Mathlib

open MeasureTheory

namespace FirstPriceLearning.LowerBound

/-- The two-point law on `{1/3, 2/3}` with mass `p` at `1/3` and `1 − p` at `2/3` (a probability
measure when `0 ≤ p ≤ 1`). -/
noncomputable def twoPointLaw (p : ℝ) : Measure ℝ :=
  p.toNNReal • Measure.dirac (1 / 3 : ℝ) + (1 - p).toNNReal • Measure.dirac (2 / 3 : ℝ)

/-- The HOB law with CDF `G₁` of App. B, p. 36: `G₁(x) = 0` on `[0, 1/3)`, `1/2 + Δ` on `[1/3, 2/3)`,
`1` on `[2/3, ∞)`, i.e. masses `(1/2 + Δ, 1/2 − Δ)` at `(1/3, 2/3)` (p. 37). -/
noncomputable def lawG1 (Δ : ℝ) : Measure ℝ :=
  twoPointLaw (1 / 2 + Δ)

/-- The HOB law with CDF `G₂` of App. B, p. 36: `G₂(x) = 0` on `[0, 1/3)`, `1/2 − Δ` on `[1/3, 2/3)`,
`1` on `[2/3, ∞)`, i.e. masses `(1/2 − Δ, 1/2 + Δ)` at `(1/3, 2/3)` (p. 37). -/
noncomputable def lawG2 (Δ : ℝ) : Measure ℝ :=
  twoPointLaw (1 / 2 - Δ)

end FirstPriceLearning.LowerBound


