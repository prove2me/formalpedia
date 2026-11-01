-- Prove2me | Definitions.Def_ParetoDDO_DRPredictor
-- name    : ParetoDDO_DRPredictor
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:34:04.564773+00:00
-- url     : https://prove2.me/theorems/5730d75a-afe3-4560-b57f-f5e225e575c5
-- title:
--   The distributionally robust predictor $\tilde c^\star$ (3.3) and prescriptor $\tilde x^\star$ (3.4)
-- statement:
--   Let $I$ be a rate function, $r>0$ the risk-aversion parameter and $c$ the model-based predictor on $X\times\operatorname{cl}\Theta$.
--
--   1. **Definition 3.4.** The distributionally robust predictor is
--   $$
--   \tilde c^\star(x,s)=\begin{cases}\max_{\theta\in\operatorname{cl}\Theta}\{c(x,\theta):I(s,\theta)\le r\}&\text{if }\exists\,\theta\in\operatorname{cl}\Theta\text{ with }I(s,\theta)\le r,\\ \sup_{\theta\in\operatorname{cl}\Theta}c(x,\theta)&\text{otherwise.}\end{cases}
--   $$
--   2. **Definition 3.5.** A distributionally robust prescriptor is any $\tilde x^\star:\mathbb S\to X$ that is quasi-continuous on $\mathbb S_\infty$ and satisfies $\tilde x^\star(s)\in\arg\min_{x\in X}\tilde c^\star(x,s)$ for all $s\in\mathbb S$.
--
--   $\tilde c^\star(x,s)$ is the worst-case cost over the models in the $I$-ball of radius $r$ around $s$.
--
--   **Formalization Note** The maximum is written as `sSup` over the feasible set; it is attained when $I$ is regular and $c$ is continuous on $X\times\operatorname{cl}\Theta$ (p.21), and the second branch is finite because $c$ is bounded there. The comparison $I(s,\theta)\le r$ is in $[0,\infty]$.
-- source:
--   Sutter, Van Parys, Kuhn, A Pareto dominance principle for data-driven optimization, arXiv:2010.06606v4, Definition 3.4, (3.3), p.21; Definition 3.5, (3.4), p.22

import Mathlib
import Definitions.Def_ParetoDDO_Setting

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ParetoDDO

variable {n d : ℕ}

open Classical in
/-- **Definition 3.4** (distributionally robust predictor; arXiv:2010.06606v4, (3.3), p.21). For a
rate function `I` and a risk-aversion parameter `r`,
`c̃⋆(x, s) = max_{θ ∈ cl Θ} {c(x, θ) : I(s, θ) ≤ r}` if some `θ ∈ cl Θ` has `I(s, θ) ≤ r`, and
`c̃⋆(x, s) = sup_{θ ∈ cl Θ} c(x, θ)` otherwise.

**Formalization Note** The maximum is written `sSup` over the feasible set; it is attained when `I` is
regular (level-compactness) and `c` is continuous on `X × cl Θ` (p.21). The supremum of the second
branch is finite because `c` is bounded on `X × cl Θ` (Assumption 2.2). The comparison `I(s, θ) ≤ r`
is in `[0, ∞]`. -/
noncomputable def drPredictor (c : Vec n → Vec d → ℝ) (Θ : Set (Vec d))
    (I : Vec d → Vec d → ℝ≥0∞) (r : ℝ) (x : Vec n) (s : Vec d) : ℝ :=
  if ∃ θ ∈ closure Θ, I s θ ≤ ENNReal.ofReal r then
    sSup ((fun θ => c x θ) '' {θ | θ ∈ closure Θ ∧ I s θ ≤ ENNReal.ofReal r})
  else sSup ((fun θ => c x θ) '' closure Θ)

/-- **Definition 3.5** (distributionally robust prescriptor; arXiv:2010.06606v4, (3.4), p.22). A function
`x̃⋆ : S → X` that is quasi-continuous on `S∞ = {S∞(θ) : θ ∈ Θ}` and satisfies
`x̃⋆(s) ∈ argmin_{x ∈ X} c̃⋆(x, s)` for all `s ∈ S`. -/
def IsDRPrescriptor (X : Set (Vec n)) (S : Set (Vec d)) (Sinf : Vec d → Vec d) (Θ : Set (Vec d))
    (c : Vec n → Vec d → ℝ) (I : Vec d → Vec d → ℝ≥0∞) (r : ℝ) (xt : Vec d → Vec n) : Prop :=
  QuasiContinuousOn (Sinf '' Θ) xt ∧
    ∀ s ∈ S, xt s ∈ X ∧ IsMinOn (fun x => drPredictor c Θ I r x s) X (xt s)

end ParetoDDO


