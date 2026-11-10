-- Prove2me | Definitions.Def_GreedNorm_Feasible
-- name    : GreedNorm_Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:47.361277+00:00
-- url     : https://prove2.me/theorems/3cc89770-47e7-4562-96f5-f19ff51dfa93
-- title:
--   Feasible extensions $F(A)$ under $p$ matroid constraints
-- statement:
--   Let $M_1,\dots,M_p$ be matroids on a finite ground set $E$ and $A\subseteq E$. The set of **feasible extensions** of $A$ is
--
--   $$
--   F(A)=\{e\in E\setminus A:\ A\cup\{e\}\text{ is independent in every } M_i\}.
--   $$
--
--   $A$ is **maximally feasible** when $F(A)=\emptyset$.
--
--   **Formalization Note** Matroids are Mathlib `Matroid E` indexed by `Fin p`.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §3.2 Augmentation and Theorem 3.10, p.8 (PDF 10)

import Mathlib

namespace GreedNorm

/-- **The feasible extensions `F(A)` under `p` matroid constraints**: the elements `e ∉ A` such
that `A ∪ {e}` is independent in every matroid `M_1, …, M_p`.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §3.2 "Augmentation", p.8 (PDF 10): "Let F(A) be the set of configurations (i, S) such that
A ∪ {(i, S)} remains valid and t-bounded", in the generic form used by Theorem 3.10 ("p matroid
constraints").

**Formalization Note** Ground type `E` is finite; the matroids are Mathlib `Matroid E` indexed by
`Fin p`. An element outside a matroid's ground set is never feasible. Elements already in `A`
are excluded: the page's `F(A)` also contains them (`A ∪ {e} = A`), but their marginal is `0`,
which by monotonicity is at most every marginal of a new element, so neither the maximum in the
definition of an `α`-augmentation nor "maximally feasible" (no new element can be added)
changes. -/
noncomputable def Feasible {E : Type} [Fintype E] [DecidableEq E] {p : ℕ}
    (M : Fin p → Matroid E) (A : Finset E) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => e ∉ A ∧ ∀ i, (M i).Indep (↑(insert e A) : Set E))

end GreedNorm


