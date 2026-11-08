-- Prove2me | Definitions.Def_AffDisp4n_IsAffineDisperser
-- name    : AffDisp4n_IsAffineDisperser
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:30.077002+00:00
-- url     : https://prove2.me/theorems/aac1a183-257d-415e-a865-fc78c901803e
-- title:
--   Affine disperser for dimension $d$
-- statement:
--   An **affine subspace** of $\mathbb F_2^n$ is a translate $b + V$ of a linear subspace $V \subseteq \mathbb F_2^n$; its dimension is $\dim V$. A function $f : \mathbb F_2^n \to \mathbb F_2$ is an **affine disperser for dimension $d$** if it is nonconstant on every affine subspace of dimension $d$: for every such $S$ there are $x, y \in S$ with $f(x) \ne f(y)$.
--
--   Gate elimination produces an affine subspace on which a small circuit is constant, so a small circuit cannot compute an affine disperser (Theorem 4.1).
--
--   **Formalization Note** Affine subspaces are Mathlib's `AffineSubspace`, required nonempty, with dimension the `finrank` of the direction. For $d > n$ there is no such subspace and every function qualifies; for $d = 0$ no function qualifies.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.5, p.16, Definition 2.1

import Mathlib

namespace AffDisp4n

/-- **Affine disperser** (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), Definition 2.1, p.16): `f : 𝔽₂ⁿ → 𝔽₂` is an affine disperser for
dimension `d` if it is nonconstant on every affine subspace of `𝔽₂ⁿ` of dimension `d`. An affine
subspace is a translate `b + V` of a linear subspace `V` (§2.5, p.16).

**Formalization Note** Affine subspaces are Mathlib's `AffineSubspace (ZMod 2) (Fin n → ZMod 2)`. They
are required to be nonempty (Mathlib's `⊥` is the empty one), and the dimension is the dimension of the
direction `V`. "Nonconstant on S" means two points of `S` with different values. -/
def IsAffineDisperser {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) (d : ℕ) : Prop :=
  ∀ S : AffineSubspace (ZMod 2) (Fin n → ZMod 2), (S : Set (Fin n → ZMod 2)).Nonempty →
    Module.finrank (ZMod 2) S.direction = d → ∃ x ∈ S, ∃ y ∈ S, f x ≠ f y

end AffDisp4n


