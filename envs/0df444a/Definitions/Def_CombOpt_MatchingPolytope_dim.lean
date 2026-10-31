-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_dim
-- name    : CombOpt_MatchingPolytope_dim
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:05:20.381009+00:00
-- url     : https://prove2.me/theorems/9baaae5b-de9e-4f64-a782-89973aa92d08
-- title:
--   The dimension $\dim(K)$ of a set of vectors
-- statement:
--   The **dimension** $\dim(K)$ of a set $K\subseteq\mathbb R^n$ is one less than the maximum cardinality of an affinely independent finite set $X\subseteq K$:
--   $$\dim(K)=\max\{|X|:\ X\subseteq K \text{ finite, affinely independent}\}-1.$$
--   In particular $\dim(\emptyset)=-1$ and a single point has dimension $0$.
--
--   Dimension characterizes facets (Proposition 6.16).
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product. The value is an integer. The set of cardinalities contains $0$ and is bounded by $n+1$, so the maximum exists.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.3, p. 211 (PDF p. 219)

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_AffinelyIndependent

namespace CombOpt.MatchingPolytope

/-- **The dimension of a set.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.3, p. 211 (PDF p. 219): "The dimension of a set K ⊆ ℝ^n (denoted by dim(K)) is one
less than the maximum cardinality of an affinely-independent set X ⊆ K."

`dim K` is `(max {|X| : X ⊆ K finite, affinely independent}) − 1`, an integer.

**Formalization Note.** `ℝ^n` is the coordinate space `ι → ℝ` over a finite index type `ι`
(`Fin n` for the book's `ℝ^n`, `E` for `ℝ^E`); `w ⬝ᵥ x` is `w^T x`. The value is in `ℤ`, so `dim ∅ = 0 − 1 = −1` (the empty set is the largest affinely
independent subset of `∅`). The set of cardinalities is nonempty (it contains `0`) and bounded by
`card ι + 1` (an affinely independent set in `ℝ^n` has at most `n + 1` elements), so the `sSup`
in `ℕ` is its maximum and the `ℕ` default `sSup ∅ = 0` is never used. -/
noncomputable def dim {ι : Type*} [Fintype ι] (K : Set (ι → ℝ)) : ℤ :=
  ((sSup {k : ℕ | ∃ X : Finset (ι → ℝ), (↑X : Set (ι → ℝ)) ⊆ K ∧ AffinelyIndependent X ∧
      X.card = k} : ℕ) : ℤ) - 1

end CombOpt.MatchingPolytope


