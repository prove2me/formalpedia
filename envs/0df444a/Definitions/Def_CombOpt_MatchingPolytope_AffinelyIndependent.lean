-- Prove2me | Definitions.Def_CombOpt_MatchingPolytope_AffinelyIndependent
-- name    : CombOpt_MatchingPolytope_AffinelyIndependent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:04:20.879115+00:00
-- url     : https://prove2.me/theorems/8d2efa0c-70e2-4885-971e-0070afe3de8b
-- title:
--   An affinely independent finite set of vectors
-- statement:
--   A finite set $X\subseteq\mathbb R^n$ is **affinely independent** if the only solution $(\lambda_x:\ x\in X)$ of the system
--   $$\sum_{x\in X}\lambda_x x=0,\qquad \sum_{x\in X}\lambda_x=0 \qquad (6.6)$$
--   is $\lambda_x=0$ for all $x\in X$.
--
--   Affine independence defines the dimension of a set.
--
--   **Formalization Note** The space $\mathbb R^n$ is the coordinate space $\mathbb R^\iota$ of functions $\iota\to\mathbb R$ on a finite index type $\iota$ (take $\iota=\{1,\dots,n\}$ for $\mathbb R^n$, or $\iota=E$ for $\mathbb R^E$), and $w^\top x$ is the dot product. The book's definition is transcribed directly; the empty set is affinely independent.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.3, p. 211 (PDF p. 219), (6.6)

import Mathlib

namespace CombOpt.MatchingPolytope

/-- **An affinely independent finite set.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.3, p. 211 (PDF p. 219): "A finite set of vectors X is affinely independent if the only
solution of the system of equations
`Σ(x λ_x : x ∈ X) = 0`, `Σ(λ_x : x ∈ X) = 0`   (6.6)
is to set λ_x = 0 for all x ∈ X."

**Formalization Note.** `ℝ^n` is the coordinate space `ι → ℝ` over a finite index type `ι`
(`Fin n` for the book's `ℝ^n`, `E` for `ℝ^E`); `w ⬝ᵥ x` is `w^T x`. The book's definition is transcribed directly (it is equivalent to Mathlib's
`AffineIndependent` of the inclusion of `X`, which is not used here). The empty set is affinely
independent. -/
def AffinelyIndependent {ι : Type*} (X : Finset (ι → ℝ)) : Prop :=
  ∀ c : (ι → ℝ) → ℝ, ∑ x ∈ X, c x • x = 0 → ∑ x ∈ X, c x = 0 → ∀ x ∈ X, c x = 0

end CombOpt.MatchingPolytope


