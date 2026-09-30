-- Prove2me | Definitions.Def_ConeLifts_StableSet_HasPSDLift
-- name    : ConeLifts_StableSet_HasPSDLift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:15:53.148272+00:00
-- url     : https://prove2.me/theorems/19909a07-bffc-49b9-8ed1-73bf99fa8fd1
-- title:
--   Positive semidefinite lift: $C = \pi(\mathcal S^k_+ \cap L)$
-- statement:
--   Let $\mathcal S^k_+$ be the cone of $k \times k$ real symmetric positive semidefinite matrices. A set $C \subseteq \mathbb R^n$ **admits an $\mathcal S^k_+$-lift** if there are an affine subspace $L$ of the space of real $k\times k$ matrices and a linear map $\pi$ from that space to $\mathbb R^n$ such that
--
--   $$
--   C = \pi(\mathcal S^k_+ \cap L).
--   $$
--
--   This is Definition 2.1 with $K = \mathcal S^k_+$: a set with such a lift is the projection of the feasible region of a semidefinite program with a $k\times k$ matrix variable.
--
--   **Formalization Note** `psdCone k` is the set of real $k\times k$ matrices satisfying Mathlib's `Matrix.PosSemidef`, which includes symmetry, so it is exactly $\mathcal S^k_+$. The ambient space is all $k\times k$ matrices rather than the symmetric ones; this does not change whether a lift exists: a lift inside the symmetric matrices extends linearly to all matrices, and a lift inside all matrices restricts to the symmetric ones (intersect $L$ with them and restrict $\pi$), since $\mathcal S^k_+$ lies in the symmetric matrices. Lifts need not be proper.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 3, Definition 2.1 with K = S^k_+ (the cone S^k_+ as introduced on p. 1)

import Mathlib
import Definitions.Def_ConeLifts_StableSet_HasConeLift

namespace ConeLifts.StableSet

/-- The cone `Sᵏ₊` of `k × k` real symmetric positive semidefinite matrices (Gouveia, Parrilo &
Thomas, arXiv:1111.3164v2, §1, p. 1), as a subset of all real `k × k` matrices. Mathlib's
`Matrix.PosSemidef` includes symmetry (`Xᴴ = X`), so this set is exactly `Sᵏ₊`. -/
def psdCone (k : ℕ) : Set (Matrix (Fin k) (Fin k) ℝ) :=
  {X | X.PosSemidef}

/-- `C ⊆ ℝⁿ` **admits a `Sᵏ₊`-lift** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2,
Definition 2.1, p. 3, with `K = Sᵏ₊`): there are an affine subspace `L` of the space of real
`k × k` matrices and a linear map `π` from that space to `ℝⁿ` with `C = π(Sᵏ₊ ∩ L)`.

The ambient space is all `k × k` matrices rather than the symmetric ones. Existence of a lift is
unaffected: a lift in the symmetric matrices extends (same `L`, `π` extended linearly), and a
lift in all matrices restricts (intersect `L` with the symmetric matrices, which contain
`Sᵏ₊`, and restrict `π`). -/
def HasPSDLift (k : ℕ) {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  HasConeLift (psdCone k) C

end ConeLifts.StableSet


