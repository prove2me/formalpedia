-- Prove2me | Definitions.Def_GreedNorm_Supplement_IsAlphaBudgOracle
-- name    : GreedNorm_Supplement_IsAlphaBudgOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:51:59.046203+00:00
-- url     : https://prove2.me/theorems/810d71d4-e7ba-498c-83e6-09106030224d
-- title:
--   $\alpha$-approximate BudgCard oracle
-- statement:
--   **Budgeted Cardinality Maximization (BudgCard)** (Definition 3.1): given a universe $U'$, a load function $\mathrm{load}:2^{U'}\to\mathbb R_{\ge0}$ and a budget $B\ge0$, find $S\subseteq U'$ maximizing $|S|$ subject to $\mathrm{load}(S)\le B$.
--
--   A map $\mathrm{budg}$ answering, for every part $i\in[m]$, every sub-universe $U'\subseteq U$ and every budget $B$, the BudgCard instance $(U',\mathrm{load}_i,B)$ is **$\alpha$-approximate** if, for every $B\ge0$ for which the instance has a feasible set, its answer $S=\mathrm{budg}(i,U',B)$ satisfies
--
--   $$
--   S\subseteq U',\qquad \mathrm{load}_i(S)\le B,\qquad |S|\ \ge\ \alpha\cdot\max\{|T| : T\subseteq U',\ \mathrm{load}_i(T)\le B\}.
--   $$
--
--   Nothing is required on an instance without a feasible set or with $B<0$. This is the hypothesis "an $\alpha$-approximation algorithm for BudgCard" of Theorem 3.2, which must hold for every such oracle.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Definition 3.1 and Theorem 3.2, p.6 (PDF 8)

import Mathlib

namespace GreedNorm

/-- **An `α`-approximate BudgCard oracle** for the load functions `load_1, …, load_m`.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256
2a3d250c…a300b1b6), Definition 3.1, p.6 (PDF 8): "Budgeted Cardinality Maximization (BudgCard). We are given a
universe U of n elements, a load function load : 2^U → R≥0, and a budget B ≥ 0. The goal is to
find a subset S ⊆ U maximizing |S| subject to load(S) ≤ B", and Theorem 3.2: "An α-approximation
algorithm for BudgCard".

`budg i U' B` is the answer on the BudgCard instance with universe `U' ⊆ Fin n`, load function
`load i` (restricted to subsets of `U'`) and budget `B ≥ 0`. Whenever that instance has a
feasible set, the answer `S` is feasible (`S ⊆ U'`, `load i S ≤ B`) and
`|S| ≥ α · |T|` for every feasible `T`, i.e. `|S| ≥ α · max{|T| : T ⊆ U', load i T ≤ B}`.

**Formalization Note** No requirement is placed on an infeasible instance or on a negative
budget (the source defines BudgCard only for `B ≥ 0`). The ratio `α` is a real number; the
theorem using this predicate assumes `0 < α ≤ 1`. -/
def Supplement.IsAlphaBudgOracle {n m : ℕ} (α : ℝ) (load : Fin m → Finset (Fin n) → ℝ)
    (budg : Fin m → Finset (Fin n) → ℝ → Finset (Fin n)) : Prop :=
  ∀ (i : Fin m) (U' : Finset (Fin n)) (B : ℝ), 0 ≤ B →
    (∃ T ⊆ U', load i T ≤ B) →
      budg i U' B ⊆ U' ∧ load i (budg i U' B) ≤ B ∧
        ∀ T ⊆ U', load i T ≤ B → α * (T.card : ℝ) ≤ ((budg i U' B).card : ℝ)

end GreedNorm


