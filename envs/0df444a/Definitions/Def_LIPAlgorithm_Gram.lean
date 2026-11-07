-- Prove2me | Definitions.Def_LIPAlgorithm_Gram
-- name    : LIPAlgorithm_Gram
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:52:36.09062+00:00
-- url     : https://prove2.me/theorems/b498ea9e-c629-4767-9d02-a836e1eb5a29
-- title:
--   Integral Gram matrices and the coordinate isomorphism set $\mathrm{Iso}(G_1,G_2)$
-- statement:
--   An input lattice is given by a Gram matrix $G\in S^{>0}_n(\mathbb Z)$, an $n\times n$ symmetric positive definite matrix with integer entries. For two such matrices,
--
--   $$\mathrm{Iso}(G_1,G_2)=\{U\in GL_n(\mathbb Z): G_1=U^\top G_2U\}.$$
--
--   The same set is defined for positive definite rational Gram matrices. A Gram matrix is **well-rounded** if the integer vectors $z\neq 0$ that minimize $z^\top Gz$ span $\mathbb R^n$.
--
--   These are the objects of the main theorem. Stating the problem on Gram matrices avoids any question about the bit complexity of real bases.
--
--   **Formalization Note** Membership in $GL_n(\mathbb Z)$ is the clause that $\det U$ is a unit: $G_1=(4)$, $G_2=(1)$, $U=(2)$ satisfies the matrix equation and is not an isomorphism.
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), §2.1, p.8; §2.2, pp.10–11; Definition of ‖z‖_G, p.9

import Mathlib

namespace LIPAlgorithm

/-- An `n × n` integer matrix, the input format of the paper's algorithmic problems.
Aggarwal, Jiang, Li, Liu, *An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem*, STOC 2027
submission (manuscript sha256 61ee52aa…), §2.2, p.10: "an input lattice is given by an integral Gram
matrix G ∈ S>0 n (Z), and isomorphisms are represented by coordinate change matrices U ∈ GLn(Z)". -/
abbrev Gram (n : ℕ) := Matrix (Fin n) (Fin n) ℤ

/-- `G ∈ S>0 n (Z)` (§2.1, p.8): symmetric positive definite with integer entries.

**Formalization Note.** `Matrix.PosDef` over `ℝ` includes symmetry (Hermitian over `ℝ`). -/
def IsGram {n : ℕ} (G : Gram n) : Prop :=
  (G.map (Int.cast : ℤ → ℝ)).PosDef

/-- `Iso(G₁, G₂) = {U ∈ GLn(Z) : G₁ = U⊤G₂U}` (§2.2, p.11).

**Formalization Note.** Membership in `GLn(Z)` is the clause `IsUnit U.det`: `G₁ = [4]`, `G₂ = [1]`,
`U = [2]` satisfies the matrix equation and is not an isomorphism. `U` sends coordinates with respect
to `G₁` to coordinates with respect to `G₂`. -/
def isoSet {n : ℕ} (G₁ G₂ : Gram n) : Set (Gram n) :=
  {U | IsUnit U.det ∧ G₁ = U.transpose * G₂ * U}

/-- An `r × r` rational matrix, the format of the lattices of Theorem 5.12 (p.27). -/
abbrev RatGram (r : ℕ) := Matrix (Fin r) (Fin r) ℚ

/-- A positive definite rational Gram matrix ("a rank-r positive definite rational lattice", p.27). -/
def IsRatGram {r : ℕ} (G : RatGram r) : Prop :=
  (G.map (Rat.cast : ℚ → ℝ)).PosDef

/-- `Iso(G₁, G₂)` for rational Gram matrices: the same set as `isoSet`, with `U ∈ GLr(Z)` read in `ℚ`. -/
def ratIsoSet {r : ℕ} (G₁ G₂ : RatGram r) : Set (Gram r) :=
  {U | IsUnit U.det ∧
    G₁ = (U.map (Int.cast : ℤ → ℚ)).transpose * G₂ * U.map (Int.cast : ℤ → ℚ)}

/-- `z` is a shortest nonzero coordinate vector for the norm `‖z‖_G = √(z⊤Gz)` (§2.1, p.9). -/
def IsMinCoord {n : ℕ} (G : Gram n) (z : Fin n → ℤ) : Prop :=
  z ≠ 0 ∧ ∀ y : Fin n → ℤ, y ≠ 0 → z ⬝ᵥ G.mulVec z ≤ y ⬝ᵥ G.mulVec y

/-- The Gram form of "well-rounded" (§2.1, p.9): the shortest vectors of `G` span `ℝⁿ`. -/
def IsWellRoundedGram {n : ℕ} (G : Gram n) : Prop :=
  Submodule.span ℝ {v : Fin n → ℝ | ∃ z : Fin n → ℤ, IsMinCoord G z ∧ v = fun i => (z i : ℝ)} = ⊤

end LIPAlgorithm


