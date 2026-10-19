-- Prove2me | Definitions.Def_ShapeMoment_LogConcave_DiscreteMoment
-- name    : ShapeMoment_LogConcave_DiscreteMoment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:11.03745+00:00
-- url     : https://prove2.me/theorems/1dc1e766-16d2-4e7e-a7c5-8f448ac44831
-- title:
--   Finite moments on {1, …, n}
-- statement:
--   On the finite sample space $\Omega=\{1,\ldots,n\}$, the support point is $w_j=j$ and the $i$th moment of a real weight vector $x$ is
--
--   $$M_i(x)=\sum_{j=1}^n j^i x_j.$$
--
--   The one-based extension of $x$ is zero outside the sample space. A maximal solution lies in its feasible set and maximizes the given linear objective there. These objects supply reusable finite moment notation.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 5, (1a)–(1c)

import Mathlib

open scoped BigOperators

namespace ShapeMoment.LogConcave

/-- The point at paper index `j.val + 1` in the sample space `{1, ..., n}`. -/
def w {n : ℕ} (j : Fin n) : ℝ := (j.val : ℝ) + 1

/-- The `i`th moment of a finite real weight vector on `{1, ..., n}`. -/
def moment {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  ∑ j, w j ^ i * x j

/-- One-based indexing of a vector, extended by zero outside `{1, ..., n}`. -/
def ext {n : ℕ} (x : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : 1 ≤ j ∧ j ≤ n then x ⟨j - 1, by omega⟩ else 0

/-- A feasible maximizer of the finite linear objective with coefficients `f`. -/
def IsMaxSol {n : ℕ} (f : Fin n → ℝ) (S : Set (Fin n → ℝ))
    (x : Fin n → ℝ) : Prop :=
  x ∈ S ∧ ∀ y ∈ S, (∑ j, f j * y j) ≤ ∑ j, f j * x j

end ShapeMoment.LogConcave


