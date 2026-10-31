-- Prove2me | Definitions.Def_AvgCostLP_Model
-- name    : AvgCostLP_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:30.845999+00:00
-- url     : https://prove2.me/theorems/b168049b-3116-4f2a-9f10-efd9f4c2dd39
-- title:
--   §2.1 — the MDP model $(\mathbb X,\mathbb A,A(\cdot),q,c)$ with graph $\Gamma$
-- statement:
--   Let $\mathbb X$ (states) and $\mathbb A$ (actions) be measurable spaces. An **average-cost MDP model** consists of
--
--   1. a set $A(x)\subset\mathbb A$ of admissible actions for every state $x$, nonempty for every $x$, whose graph
--   $$\Gamma:=\{(x,a)\mid x\in\mathbb X,\ a\in A(x)\}$$
--   is a Borel subset of $\mathbb X\times\mathbb A$;
--   2. a state transition stochastic kernel $q(dy\mid x,a)$ on $\mathbb X$ given $\mathbb X\times\mathbb A$;
--   3. a nonnegative Borel measurable one-stage cost $c:\mathbb X\times\mathbb A\to[0,+\infty]$ that is real-valued on $\Gamma$ and equals $+\infty$ outside $\Gamma$.
--
--   This is the model of §2.1 on which every policy, cost criterion and linear program of the mission is built.
--
--   **Formalization Note** The kernel is a Mathlib Markov kernel; the cost takes values in $[0,+\infty]$, and "real-valued on $\Gamma$, $+\infty$ outside" is the condition $c(x,a)=+\infty\iff a\notin A(x)$. The topological standing assumptions ($\mathbb X$ a Borel space, $\mathbb A$ countable and discrete) are stated in the theorems.
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §2.1, p.5

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AvgCostLP

/-- Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision
Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §2.1,
p.5: the MDP model.

The state space `X` and the countable action space `A` carry σ-algebras (the standing topological
assumptions, "`X` a Borel space, `A` countable and discrete", are put on the theorems). A model
consists of

* the admissible action sets `A(x) ⊂ A`, nonempty for every state `x`, whose graph
  `Γ = {(x, a) | x ∈ X, a ∈ A(x)}` is a measurable (Borel) subset of `X × A`;
* the state transition stochastic kernel `q(dy | x, a)` on `X` given `X × A`, defined on all of
  `X × A`;
* the one-stage cost `c : X × A → [0, +∞]`, Borel measurable, real-valued on `Γ` and `+∞` outside
  `Γ`.

**Formalization Note** The kernel is a Mathlib `Kernel (X × A) X` with `IsMarkovKernel`
(measurable into the probability measures; on separable metrizable spaces this is the paper's
Borel measurable map into `P(X)` with the weak topology). The cost takes values in `ℝ≥0∞`, and
`c p = ⊤ ↔ p ∉ Γ` encodes "real-valued on `Γ`, `+∞` outside `Γ`". -/
structure Model (X A : Type*) [MeasurableSpace X] [MeasurableSpace A] where
  /-- the admissible action set `A(x)` -/
  adm : X → Set A
  /-- every `A(x)` is nonempty -/
  adm_nonempty : ∀ x, (adm x).Nonempty
  /-- the graph `Γ` of `A(·)` is a Borel subset of `X × A` -/
  measurableSet_graph : MeasurableSet {p : X × A | p.2 ∈ adm p.1}
  /-- the state transition stochastic kernel `q(dy | x, a)` -/
  q : Kernel (X × A) X
  [isMarkovKernel_q : IsMarkovKernel q]
  /-- the one-stage cost `c(x, a) ∈ [0, +∞]` -/
  c : X × A → ℝ≥0∞
  measurable_c : Measurable c
  /-- `c` is real-valued on `Γ` and `+∞` outside `Γ` -/
  c_eq_top_iff : ∀ p : X × A, c p = ⊤ ↔ p.2 ∉ adm p.1

attribute [instance] Model.isMarkovKernel_q

/-- The graph `Γ := {(x, a) | x ∈ X, a ∈ A(x)}` of the admissible action map (p.5). -/
def Model.graph {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] (M : Model X A) :
    Set (X × A) :=
  {p | p.2 ∈ M.adm p.1}

end AvgCostLP


