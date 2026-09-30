-- Prove2me | Definitions.Def_SteuerChoo_Lexico_nondominated
-- name    : SteuerChoo_Lexico_nondominated
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:49:10.707061+00:00
-- url     : https://prove2.me/theorems/9cc43d25-ef2d-47a4-bc74-a7f6d17cbc19
-- title:
--   Dominance and the nondominated set $N \subseteq Z$ of a multiple objective program
-- statement:
--   Consider the multiple objective program $\max\{f_1(x)=z_1\},\dots,\max\{f_k(x)=z_k\}$ subject to $x\in S$, and let $Z\subseteq\mathbb R^k$ be its set of feasible criterion vectors (the image of $S$ under $f=(f_1,\dots,f_k)$).
--
--   A criterion vector $z$ **dominates** $\bar z$ when
--   $$
--   z_i\ge \bar z_i \ \text{ for all } i \quad\text{and}\quad z_i>\bar z_i \ \text{ for at least one } i .
--   $$
--   A vector $\bar z\in Z$ is **nondominated** if no $z\in Z$ dominates it, and $N\subseteq Z$ denotes the set of all nondominated criterion vectors.
--
--   These are the basic objects of multiple objective programming: $N$ is the set every scalarization in the paper is meant to reach.
--
--   **Formalization Note** Criterion vectors are functions $\mathrm{Fin}\,k\to\mathbb R$ (objectives indexed $0,\dots,k-1$). The decision space $S$ and the objectives $f_i$ are eliminated: $Z$ is given directly as a set of criterion vectors. `Dominates z zbar` states the paper's two conditions literally; `nondominated Z` is a `Set`, with $Z$ an arbitrary (not necessarily finite) set.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983), p. 326, §1, definition of nondominated criterion vector and of N

import Mathlib

namespace SteuerChoo.Lexico

/-- `z` dominates `zbar`: `zbar i ≤ z i` for every objective `i`, with strict
inequality for at least one objective (Steuer–Choo 1983, §1, p. 326). -/
def Dominates {k : ℕ} (z zbar : Fin k → ℝ) : Prop :=
  (∀ i, zbar i ≤ z i) ∧ ∃ i, zbar i < z i

/-- The nondominated set `N ⊆ Z`: the criterion vectors of `Z` that no other
member of `Z` dominates (Steuer–Choo 1983, §1, p. 326). -/
def nondominated {k : ℕ} (Z : Set (Fin k → ℝ)) : Set (Fin k → ℝ) :=
  {zbar | zbar ∈ Z ∧ ¬ ∃ z ∈ Z, Dominates z zbar}

end SteuerChoo.Lexico


