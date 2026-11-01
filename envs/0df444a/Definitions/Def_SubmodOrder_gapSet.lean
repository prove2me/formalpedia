-- Prove2me | Definitions.Def_SubmodOrder_gapSet
-- name    : SubmodOrder_gapSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:36:19.306842+00:00
-- url     : https://prove2.me/theorems/833055c9-67e9-46c0-8408-21cdd5da0a42
-- title:
--   The gaps of a set in the order $\pi$
-- statement:
--   Let $\pi$ be an order of the ground set and $S=\{s_1,\dots,s_{k'}\}$ a set listed in increasing $\pi$-index. For $j=0,\dots,k'$ let
--
--   $$
--   E(j)=\{s_1,\dots,s_j\},\qquad O_{j+1}=\{e\in T\setminus S:\ s_j \text{ precedes } e \text{ and } e \text{ precedes } s_{j+1}\}
--   $$
--
--   for a second set $T$, where $s_0$ and $s_{k'+1}$ impose no bound. Then $\{O_1,\{s_1\},O_2,\{s_2\},\dots,\{s_{k'}\},O_{k'+1}\}$ is an interleaved partition of $T\cup S$; this is the partition used in the proof of Theorem 2, with $S$ the output of Threshold Add and $T$ an optimal set.
--
--   **Formalization Note** 0-based: `prefixSet π S j` is $E(j)$, the elements of $S$ with fewer than $j$ elements of $S$ before them, and `gapSet π S T j` is $O_{j+1}$, the elements of $T\setminus S$ with exactly $j$ elements of $S$ before them.
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, proof of Theorem 2, p.21, "Set Oj+1 contains all elements in OPT between sj and sj+1"

import Mathlib

namespace SubmodOrder

/-- `prefixSet π S j` is the set of the first `j` elements of `S` in increasing `π`-index, i.e.
`E(j) = {s₁, …, s_j}` when `S = {s₁, …, s_{k′}}` is listed in `π`-order (Udwani,
arXiv:2107.02743v5, proof of Theorem 2, p.21: "Applying Corollary 2 on OPT ∪ S with Ej = sj for
j ∈ [k′]").

**Formalization Note.** An element `s ∈ S` is among the first `j` exactly when fewer than `j`
elements of `S` have a smaller `π`-index. Threshold Add scans in `π`-order, so this is also the
order in which the elements were added. -/
def prefixSet {α : Type*} {n : ℕ} (π : α ≃ Fin n) (S : Finset α) (j : ℕ) : Finset α :=
  S.filter fun s => (S.filter fun s' => π s' < π s).card < j

/-- `gapSet π S T j` is the set of elements of `T \ S` that lie in the `j`-th gap of `S`: exactly
`j` elements of `S` have a smaller `π`-index. For `j = 0, …, k′` these are the sets
`O₁, …, O_{k′+1}` of the interleaved partition `{O₁, {s₁}, O₂, {s₂}, …, {s_{k′}}, O_{k′+1}}` of
`T ∪ S` (Udwani, arXiv:2107.02743v5, proof of Theorem 2, p.21: "Set Oj+1 contains all elements in
OPT between sj and sj+1").

**Formalization Note.** 0-based: `gapSet π S T j` is the paper's `O_{j+1}`, and
`prefixSet π S j` is the matching `E(j)`. -/
def gapSet {α : Type*} [DecidableEq α] {n : ℕ} (π : α ≃ Fin n) (S T : Finset α) (j : ℕ) :
    Finset α :=
  (T \ S).filter fun e => (S.filter fun s => π s < π e).card = j

end SubmodOrder


