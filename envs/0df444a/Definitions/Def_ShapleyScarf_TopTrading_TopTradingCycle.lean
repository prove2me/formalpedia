-- Prove2me | Definitions.Def_ShapleyScarf_TopTrading_TopTradingCycle
-- name    : ShapleyScarf_TopTrading_TopTradingCycle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:09.846041+00:00
-- url     : https://prove2.me/theorems/d607f178-b28a-45a3-a208-5158d7d66a5a
-- title:
--   Section 6, pp. 113-114 — top trading cycles and the top-trading-cycle partition
-- statement:
--   Let $N$ be the finite set of traders of a housing market with preference matrix $A=(a_{ij})$ (ties allowed).
--
--   **Top trading cycle.** For $R \subseteq N$, a **top trading cycle for $R$** is a set $S$ with $\emptyset \subset S \subseteq R$ whose $s$ members can be indexed in a cyclic order $S = \{i_1, i_2, \dots, i_s = i_0\}$ in such a way that each trader $i_r$ likes the good of $i_{r+1}$ at least as well as any other good in $R$:
--   $$a_{i_r\, i_{r+1}} \ge a_{i_r\, j}\qquad\text{for all } j\in R .$$
--   A top trading cycle may consist of a single trader, who then likes his own good best in $R$.
--
--   **Top-trading-cycle partition.** A partition
--   $$N = S^1 \cup S^2 \cup \cdots \cup S^p$$
--   into disjoint sets in which $S^1$ is a top trading cycle for $N$, $S^2$ is a top trading cycle for $N - S^1$, and in general $S^j$ is a top trading cycle for $N - (S^1 \cup \cdots \cup S^{j-1})$. The partition records, for each trader $i$, the index of the cycle containing him and his **cyclic successor** in that cycle; the successor map sends each $S^j$ onto itself. Any choice of cycle at any stage is allowed.
--
--   These are the objects of David Gale's constructive method (Section 6): carrying out the indicated trades within each cycle gives an allocation that is both in the core and competitive.
--
--   **Formalization Note** The cyclic order is encoded by a successor map `next : N → N`: $S$ is nonempty, $S \subseteq R$, `next` maps $S$ into $S$, every member of $S$ reaches every other member by iterating `next` (so $S$ is one cycle, not a union of cycles), and $a_{i\,\mathrm{next}(i)} \ge a_{ij}$ for $i\in S$, $j \in R$. A partition is a structure with the number of cycles $p$, a stage map `stage : N → Fin p` and the successor map `next`; the cycle $S^{j+1}$ of the paper is $\{i : \mathrm{stage}(i) = j\}$ (Lean counts from $0$) and $N - (S^1\cup\cdots\cup S^{j})$ is $\{i : \mathrm{stage}(i) \ge j\}$. Disjointness and covering hold by construction, and every cycle is nonempty. For the empty market $p = 0$.
-- source:
--   Shapley and Scarf, On cores and indivisibility, J. Math. Econ. 1 (1974); pp. 113-114 of the source printing, Section 6 (definition of a top trading cycle for R; the partition N = S^1 ∪ ... ∪ S^p)

import Mathlib

namespace ShapleyScarf.TopTrading

/-- **Top trading cycle for `R`** (Shapley–Scarf 1974, §6, pp. 113–114). A set `S` with
`∅ ⊂ S ⊆ R` whose members form a single cycle `i₁ → i₂ → ⋯ → i_s → i₁` of the successor map
`next` (`next` maps `S` into `S` and every member of `S` reaches every other by iterating `next`),
such that each member `i` of `S` likes the good of its successor `next i` at least as well as any
other good in `R`. A single trader with `next i = i` is allowed. -/
def IsTopTradingCycle {N : Type*} (A : N → N → ℝ) (R S : Finset N) (next : N → N) : Prop :=
  S.Nonempty ∧ S ⊆ R ∧ (∀ i ∈ S, next i ∈ S) ∧
    (∀ i ∈ S, ∀ i' ∈ S, ∃ k : ℕ, next^[k] i = i') ∧
    ∀ i ∈ S, ∀ j ∈ R, A i j ≤ A i (next i)

/-- **Top-trading-cycle partition** (Shapley–Scarf 1974, §6, p. 114): `N = S¹ ∪ S² ∪ ⋯ ∪ Sᵖ`,
where `S^{j+1}` (Lean index `j : Fin p`, counted from `0`) is the set of traders with
`stage i = j`, and it is a top trading cycle, for the successor map `next`, for the traders not
yet removed, `N − (S¹ ∪ ⋯ ∪ Sʲ) = {i | j ≤ stage i}`. Every trader lies in exactly one stage, and
`next i` is trader `i`'s cyclic successor in his own cycle. -/
structure TTCPartition {N : Type*} [Fintype N] [DecidableEq N] (A : N → N → ℝ) where
  /-- the number of cycles -/
  p : ℕ
  /-- the cycle containing each trader (`0` is the first cycle `S¹`) -/
  stage : N → Fin p
  /-- each trader's cyclic successor in his cycle -/
  next : N → N
  /-- the `j`-th cycle is a top trading cycle for the traders of stage `≥ j` -/
  isTopTradingCycle : ∀ j : Fin p,
    IsTopTradingCycle A (Finset.univ.filter fun i => j ≤ stage i)
      (Finset.univ.filter fun i => stage i = j) next

end ShapleyScarf.TopTrading


