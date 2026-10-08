-- Prove2me | Definitions.Def_ShapleyScarf_Balanced_MarketGame
-- name    : ShapleyScarf_Balanced_MarketGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:47:59.743378+00:00
-- url     : https://prove2.me/theorems/69c50591-0bae-48f9-a7d2-5d5744740826
-- title:
--   Sections 2 and 4 — housing market characteristic function
-- statement:
--   Let $N$ be a finite trader set, with item $j$ initially owned by trader $j$. A real matrix $A=(a_{ij})$ records trader $i$'s ranking of item $j$, including ties. An $S$-allocation is a zero-one matrix $P$ with exactly one 1 in each column indexed by $S$ and zeros in every row and column outside $S$. An $S$-permutation also has every row sum at most 1.
--
--   For $x\in\mathbb R^N$, put
--   $$
--   b_{S|ij}(x)=
--   \begin{cases}
--   1,&i\in S\ \text{and}\ x_i\le a_{ij},\\
--   0,&\text{otherwise},
--   \end{cases}
--   \qquad
--   V(S)=\{x:\exists\text{ an }S\text{-permutation }P,\ P_{ij}\le b_{S|ij}(x)\ \forall i,j\}.
--   $$
--
--   Thus a coalition can obtain a payoff vector when it can permute its own items so that each member receives an item ranked at least as high as the stated payoff. The formula also defines $V(\varnothing)=\mathbb R^N$; game conditions apply only to nonempty coalitions.
-- source:
--   Shapley and Scarf, On cores and indivisibility, J. Math. Econ. 1 (1974), DOI 10.1016/0304-4068(74)90033-0; pp. 106–107 of the source printing, Section 2, S-allocation and S-permutation; pp. 109–110, Section 4, B_S(x) and V(S)

import Mathlib
noncomputable section

namespace ShapleyScarf.Balanced

def IsSAllocation {N : Type*} [Fintype N] [DecidableEq N]
    (S : Finset N) (P : Matrix N N ℝ) : Prop :=
  (∀ i j, P i j = 0 ∨ P i j = 1) ∧
  (∀ j ∈ S, ∑ i, P i j = 1) ∧
  (∀ i, i ∉ S → ∀ j, P i j = 0) ∧
  (∀ j, j ∉ S → ∀ i, P i j = 0)

def IsSPermutation {N : Type*} [Fintype N] [DecidableEq N]
    (S : Finset N) (P : Matrix N N ℝ) : Prop :=
  IsSAllocation S P ∧ ∀ i, ∑ j, P i j ≤ 1

def acceptableMatrix {N : Type*} [Fintype N] [DecidableEq N]
    (A : N → N → ℝ) (S : Finset N) (x : N → ℝ) : Matrix N N ℝ :=
  fun i j => if i ∈ S ∧ x i ≤ A i j then 1 else 0

def marketGame {N : Type*} [Fintype N] [DecidableEq N]
    (A : N → N → ℝ) (S : Finset N) : Set (N → ℝ) :=
  {x | ∃ P : Matrix N N ℝ, IsSPermutation S P ∧
    ∀ i j, P i j ≤ acceptableMatrix A S x i j}

end ShapleyScarf.Balanced


