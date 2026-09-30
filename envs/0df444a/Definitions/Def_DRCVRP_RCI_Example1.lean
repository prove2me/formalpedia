-- Prove2me | Definitions.Def_DRCVRP_RCI_Example1
-- name    : DRCVRP_RCI_Example1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:20:15.164843+00:00
-- url     : https://prove2.me/theorems/c73dbc28-4c97-42ee-9eae-86d3e6984c99
-- title:
--   The ambiguity set and the distribution $\mathbb P^\star$ of Example 1
-- statement:
--   Example 1 of the paper has $n=2$ customers. Its ambiguity set is the set of all probability distributions $\mathbb P$ on $\mathbb R^2$ with
--   $$
--   \mathbb P(\tilde q_1=1)=0.925,\quad \mathbb P(\tilde q_1=2)=0.075,\quad \mathbb P(\tilde q_2=1)=0.925,\quad \mathbb P(\tilde q_2=2)=0.075 ,
--   $$
--   that is, each customer has demand $1$ with probability $0.925$ and demand $2$ with probability $0.075$; the joint distribution (the dependence between the two demands) is not restricted.
--
--   The distribution $\mathbb P^\star$ is the law of $(\tilde q_1,\tilde q_2)$ where, for $\tilde u$ uniformly distributed on $[0,1]$,
--   $$
--   \tilde q_1=\begin{cases}2&\text{if }\tilde u\in[0,0.075],\\1&\text{otherwise,}\end{cases}\qquad
--   \tilde q_2=\begin{cases}2&\text{if }\tilde u\in[0.1,0.175],\\1&\text{otherwise.}\end{cases}
--   $$
--
--   The example shows that without condition (S) the two formulations RVRP($\mathcal P$) and 2VF($\mathcal P$) are not equivalent.
--
--   **Formalization Note** Customers are 0-based, so $\tilde q_1,\tilde q_2$ are `q 0, q 1`. $\mathbb P^\star$ is the push-forward of Lebesgue measure restricted to $[0,1]$ under the map $u\mapsto(\tilde q_1(u),\tilde q_2(u))$.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §3, p. 721, Example 1

import Mathlib

open MeasureTheory

namespace DRCVRP.RCI

/-- The ambiguity set of Example 1 (p. 721): all probability distributions `ℙ` on `ℝ²` with
`ℙ(q̃_1 = 1) = 0.925`, `ℙ(q̃_1 = 2) = 0.075`, `ℙ(q̃_2 = 1) = 0.925`, `ℙ(q̃_2 = 2) = 0.075`.
Customers are 0-based: the paper's `q̃_1, q̃_2` are `q 0, q 1`. The joint law is unrestricted. -/
def example1AmbiguitySet : Set (Measure (Fin 2 → ℝ)) :=
  {P | IsProbabilityMeasure P ∧
    P {q | q 0 = 1} = ENNReal.ofReal 0.925 ∧ P {q | q 0 = 2} = ENNReal.ofReal 0.075 ∧
    P {q | q 1 = 1} = ENNReal.ofReal 0.925 ∧ P {q | q 1 = 2} = ENNReal.ofReal 0.075}

open Classical in
/-- The demand realisation of Example 1 as a function of `u ∈ [0,1]` (p. 721):
`q̃_1 = 2` if `u ∈ [0, 0.075]` and `1` otherwise; `q̃_2 = 2` if `u ∈ [0.1, 0.175]` and `1`
otherwise. -/
noncomputable def example1Demand (u : ℝ) : Fin 2 → ℝ :=
  ![if u ∈ Set.Icc (0 : ℝ) 0.075 then 2 else 1, if u ∈ Set.Icc (0.1 : ℝ) 0.175 then 2 else 1]

/-- The distribution `ℙ⋆` of Example 1 (p. 721): the law of `example1Demand ũ` for `ũ` uniformly
distributed on `[0,1]`. -/
noncomputable def example1PStar : Measure (Fin 2 → ℝ) :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).map example1Demand

end DRCVRP.RCI


