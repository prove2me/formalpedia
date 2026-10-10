-- Prove2me | Definitions.Def_DDMomentDRO_Type3_DDCone
-- name    : DDMomentDRO_Type3_DDCone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:37.280146+00:00
-- url     : https://prove2.me/theorems/adea38ee-448c-4cd0-9e30-3005c2c84004
-- title:
--   Definition 1, p. 15 — diagonally dominant matrices and the cones DD(U)
-- statement:
--   **Definition 1.** A symmetric real $n\times n$ matrix $A$ is **diagonally dominant (dd)** if
--   $$a_{ii} \ge \sum_{j\ne i} |a_{ij}| \quad \text{for all } i.$$
--
--   For a matrix $U \in \mathbb R^{n\times n}$, the cone
--   $$DD(U) = \{M \in S_n : M = U^\top Q U \text{ for some dd matrix } Q\},$$
--   where $S_n$ is the set of real symmetric $n\times n$ matrices.
--
--   The paper uses these polyhedral cones as inner approximations of the positive semidefinite cone, replacing $Z \succeq 0$, $Y \succeq 0$ to obtain mixed-integer linear programs that give upper bounds.
--
--   **Formalization Note** Symmetry is part of the definition of dd, as on the page; indices are `Fin n`.
-- source:
--   Yu & Shen, Multistage distributionally robust mixed-integer programming with decision-dependent moment-based ambiguity sets, arXiv:2002.12518v3, p. 15, §4.2.2, Definition 1 and DD(U)

import Mathlib

namespace DDMomentDRO.Type3

open Matrix

/-- Definition 1: a symmetric matrix `A` is diagonally dominant if `aᵢᵢ ≥ ∑_{j ≠ i} |aᵢⱼ|`. -/
def IsDD {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  A.IsSymm ∧ ∀ i, ∑ j ∈ Finset.univ.erase i, |A i j| ≤ A i i

/-- The cone `DD(U) = {M ∈ Sₙ | M = Uᵀ Q U for some dd matrix Q}`. -/
def DDcone {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {M | M.IsSymm ∧ ∃ Q, IsDD Q ∧ M = Uᵀ * Q * U}

end DDMomentDRO.Type3


