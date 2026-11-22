-- Prove2me | Definitions.Def_KissingNumber
-- name    : KissingNumber
-- status  : Definition
-- author  : @LG
-- created : 2026-11-21T21:55:27.338948+00:00
-- url     : https://prove2.me/theorems/770a7c1e-e019-4f7b-86f6-23d82ee50472
-- title:
--   Kissing configurations and the kissing number $\tau(d)$
-- statement:
--   The **kissing number** $\tau(d)$ is the largest number of non-overlapping unit balls in $\mathbb{R}^d$ that can simultaneously touch a common unit ball. After rescaling, the centers of the touching balls form a finite set of unit vectors with pairwise inner products at most $\tfrac12$ (equivalently, pairwise Euclidean distances at least $1$).
--
--   This file defines a **kissing configuration** `KissingConfig d` as a finite set of unit vectors in $\mathbb{R}^d$ whose distinct points have inner product $\le \tfrac12$, and defines
--   $$\tau(d)=\sup\{\,|C| : C \text{ a kissing configuration in dimension } d\,\},$$
--   valued in the extended naturals $\mathbb{N}_\infty$.
--
--   It is the standard spherical-code formulation of the kissing number problem and coincides with the platform's `SpherePacking.kissingNumber`. It is the shared definition on which every theorem of this mission rests.
--
--   **Formalization Note.** The ambient space is `EuclideanSpace ℝ (Fin d)`; the value is an `ℕ∞`-valued supremum over all configurations. Finiteness and attainment are not built into the definition; they are proved separately as the well-posedness milestone.
-- source:
--   https://en.wikipedia.org/wiki/Kissing_number (Mathematical statement section); Conway & Sloane, Sphere Packings, Lattices and Groups, 3rd ed., Springer 1999, Ch. 2

import Mathlib

namespace KissingNumber

noncomputable section

open scoped InnerProductSpace

/-- The ambient Euclidean space `ℝ^d`. -/
abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A kissing configuration in dimension `d`: a finite set of unit vectors in `ℝ^d`
with pairwise inner products at most `1/2` (equivalently, pairwise distances at least `1`).
These are exactly the (rescaled) centers of non-overlapping unit balls touching a common
unit ball. -/
structure KissingConfig (d : ℕ) where
  points : Finset (Ambient d)
  unit_norm : ∀ x ∈ points, ‖x‖ = 1
  inner_le : ∀ x ∈ points, ∀ y ∈ points, x ≠ y → ⟪x, y⟫_ℝ ≤ (1 : ℝ) / 2

/-- The kissing number `τ(d)`: the largest number of non-overlapping unit balls in `ℝ^d`
that can touch a common unit ball. Defined as the supremum of the cardinalities of all
kissing configurations, valued in `ℕ∞`. -/
def kissingNumber (d : ℕ) : ℕ∞ :=
  ⨆ C : KissingConfig d, (C.points.card : ℕ∞)

end

end KissingNumber


