-- Prove2me | Definitions.Def_BewleyGE_IsSavingsPolicy
-- name    : BewleyGE_IsSavingsPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:31:36.784988+00:00
-- url     : https://prove2.me/theorems/b4356a48-5e32-4d7e-bae5-81d53f735658
-- title:
--   Savings policy $g$ satisfying equation (1)
-- statement:
--   A measurable function $g$ is a **savings policy** at prices $(p,r)$ (for the demand $x$ and value function $V$) if for every $a\in A(p,r)$, $g(a)\in C(a,p)$ and $g(a)$ attains the maximum in the Bellman equation:
--   $$
--   g(a)\in\operatorname*{argmax}_{b\in C(a,p)}\Big[U\big(x^*(a-b,p)\big)+\beta\sum_{y\in\mathcal Y}e(y)V\big((1+r)b+p\cdot y\big)\Big].\tag{1}
--   $$
--
--   **Formalization Note** Measurability of $g$ is part of the definition so that the wealth operator, built from images of measures under $g$, is well defined.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, (1), p.8

import Mathlib
import Definitions.Def_BewleyGE_bellmanObjective
import Definitions.Def_BewleyGE_savingsSet
import Definitions.Def_BewleyGE_wealthSet

namespace BewleyGE

/-- **Savings policy** satisfying equation (1). Light, arXiv:1906.06810v2, (1), p.8:
`g(a, p, r) = argmax_{b ∈ C(a,p)} U(x*(a − b, p)) + β ∑_{y ∈ 𝒴} e(y) V((1 + r) b + p · y, p, r)`.

`g` is measurable, and for every `a ∈ A(p, r)` the savings `g a` are feasible, `g a ∈ C(a, p)`,
and attain the value `V a` (with `V` the value function, `V a` is the maximum, so `g a` is a
maximizer).

**Formalization Note.** Measurability of `g` is required so that the wealth operator `M`, a
mixture of pushforwards along `a ↦ (1 + r) g a + p · y`, is not the zero measure. Values of `g`
off `A(p, r)` are otherwise unconstrained. -/
def IsSavingsPolicy {n : ℕ} (E : Economy n) (p : Fin n → ℝ) (r : ℝ)
    (x : ℝ → Fin n → ℝ) (V g : ℝ → ℝ) : Prop :=
  Measurable g ∧
  ∀ a ∈ wealthSet E p r, g a ∈ savingsSet E p r a ∧ bellmanObjective E p r x V a (g a) = V a

end BewleyGE


