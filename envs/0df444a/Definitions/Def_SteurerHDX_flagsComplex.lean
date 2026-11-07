-- Prove2me | Definitions.Def_SteurerHDX_flagsComplex
-- name    : SteurerHDX_flagsComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:31:01.881934+00:00
-- url     : https://prove2.me/theorems/ea68eded-163b-4a71-8caa-a6005541d04f
-- title:
--   The projected flags complex $\mathcal X^{S_k}$ over $\mathbb F_q^{2r}$
-- statement:
--   Let $\mathbb F_q$ be a finite field, $r\in\mathbb N$ and $S_k=\{r-k,\dots,r-1,r,r+1,\dots,r+k\}$. The **projected flags complex** $\mathcal X^{S_k}$ has as vertices the subspaces $W\subset\mathbb F_q^{2r}$ with $\dim W\in S_k$, and as faces the chains of such subspaces (finite sets of pairwise comparable subspaces). Its facets are the maximal chains
--   $$W_1\subset W_2\subset\dots\subset W_{2k+1},\qquad \dim W_i=r-k-1+i .$$
--   It is the Hopkins–Ray construction of sparse top-link expanders used in the paper.
--
--   **Formalization Note** $q$ is the cardinality of a finite field $F$ (finite fields are exactly the fields of prime-power order). For $k<r$, $S_k\subseteq[2r-1]$ as the page requires.
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, Section 2.3, p.4

import Mathlib

namespace SteurerHDX

/-- **The projected flags complex X^{S_k}.** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, Section 2.3, p.4: "Let r ∈ ℕ, let q be a
prime power … The projected flags complex X^S is the k-partite k-dimensional simplicial complex
whose vertices are the subspaces W ⊂ F_q^{2r} with dim(W) ∈ S, partitioned according to
dimension. Its facets are maximal chains X^S(k) = {W₁ ⊂ W₂ ⊂ ⋯ ⊂ W_k : dim(Wᵢ) = sᵢ}. We take S
to be S_k = {r − k, …, r − 1, r, r + 1, …, r + k}."

**Formalization Note.** `F` is a finite field with q = |F| elements (finite fields are exactly
the fields of prime-power order). The faces are the finite sets of subspaces of F^{2r} with
dimension in S_k = [r − k, r + k] that are chains (pairwise comparable); a chain has distinct
dimensions, so its facets are the maximal chains with one subspace of each dimension in S_k.
For k < r we have S_k ⊆ [2r − 1], as the page requires. -/
noncomputable def flagsComplex (F : Type*) [Field F] [Fintype F] (r k : ℕ) :
    Finset (Finset (Submodule F (Fin (2 * r) → F))) :=
  haveI : Finite (Submodule F (Fin (2 * r) → F)) :=
    Finite.of_injective (fun W : Submodule F (Fin (2 * r) → F) => (W : Set (Fin (2 * r) → F)))
      SetLike.coe_injective
  haveI : Fintype (Submodule F (Fin (2 * r) → F)) := Fintype.ofFinite _
  by classical
  exact Finset.univ.filter (fun s : Finset (Submodule F (Fin (2 * r) → F)) =>
    (∀ W ∈ s, r - k ≤ Module.finrank F W ∧ Module.finrank F W ≤ r + k) ∧
    (∀ W ∈ s, ∀ W' ∈ s, W ≤ W' ∨ W' ≤ W))

end SteurerHDX


