-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_outerLimit
-- name    : RockafellianRelax_Supplement_outerLimit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:16:32.984697+00:00
-- url     : https://prove2.me/theorems/d23e05cd-e976-4a61-9890-7ef3b6a85743
-- title:
--   Outer limit of a sequence of sets
-- statement:
--   For subsets $S^\nu$ of a topological space $X$, the **outer limit** is
--
--   $$
--   \operatorname{LimOut} S^\nu = \{x \mid \exists\,\nu_1<\nu_2<\cdots \text{ and } a_j\in S^{\nu_j} \text{ with } a_j \to x\}.
--   $$
--
--   It expresses condition (5.1), $\operatorname{LimOut}(\operatorname{gph}\partial f^\nu)\subset\operatorname{gph}\partial f$.
--
--   **Formalization Note** A subsequence is a strictly increasing map $\mathbb N\to\mathbb N$. Only the chosen members need exist. The paper's spaces are Euclidean, where this sequential definition is the Painlevé–Kuratowski outer limit.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §5, p.24 (LimOut)

import Mathlib

namespace RockafellianRelax.Supplement

/-- **Outer limit of a sequence of sets.** Royset, Chen & Eckstrand, arXiv:2204.04762v4, §5, p.24: "LimOut Sν = {x ∈ ℝⁿ | ∃ subsequence
N ⊂ ℕ and xν ∈ Sν, ν ∈ N, such that xν →_N x}."

**Formalization Note.** A subsequence is a strictly increasing `k : ℕ → ℕ`, and only the chosen
members `a j ∈ S (k j)` need exist, so finitely or infinitely many of the other sets may be empty.
-/
def outerLimit {X : Type*} [TopologicalSpace X] (S : ℕ → Set X) : Set X :=
  {x | ∃ (k : ℕ → ℕ) (a : ℕ → X), StrictMono k ∧ (∀ j, a j ∈ S (k j)) ∧
    Filter.Tendsto a Filter.atTop (nhds x)}

end RockafellianRelax.Supplement


