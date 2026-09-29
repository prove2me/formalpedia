-- Prove2me | Definitions.Def_GPSAnalysis_Core_Mesh
-- name    : GPSAnalysis_Core_Mesh
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T07:18:50.430918+00:00
-- url     : https://prove2.me/theorems/4a33d94d-b0cb-48d5-b622-c73c9099f63d
-- title:
--   Positive spanning directions $D=G\bar Z$ and the mesh $M_k=\{x_k+\Delta_k Dz : z\in\mathbb Z_+^{|D|}\}$
-- statement:
--   Let $G\in\mathbb R^{n\times n}$ be a generating matrix and $\bar Z\in\mathbb Z^{n\times p}$ an integer matrix with columns $\bar z_1,\dots,\bar z_p$. The **direction matrix** is $D=G\bar Z$; its columns $d_j=G\bar z_j$ are the directions of the method.
--
--   For a set $S$ of column indices, the columns $\{d_j : j\in S\}$ form a **positive spanning set** of $\mathbb R^n$ when their nonnegative linear combinations span $\mathbb R^n$:
--
--   $$\Big\{\textstyle\sum_{j\in S} c_j d_j : c_j\ge 0\Big\}=\mathbb R^n .$$
--
--   Given a current iterate $x_k\in\mathbb R^n$ and a mesh size parameter $\Delta_k$, the **mesh** is
--
--   $$M_k=\{x_k+\Delta_k D z : z\in\mathbb Z_+^{p}\},$$
--
--   the set of points reached from $x_k$ by a nonnegative integer combination of all directions of $D$, scaled by $\Delta_k$ (Eq. (2.4) of the paper).
--
--   These objects encode the rule that makes pattern search work: all directions are integer combinations of the columns of one fixed matrix $G$, so the meshes are translated, scaled copies of a lattice.
--
--   **Formalization Note** Directions are indexed by `Fin p` with $p=|D|$, a subset of directions is a `Finset (Fin p)`, and $z\in\mathbb Z_+^p$ is `Fin p → ℕ`. The nonsingularity of $G$ is not part of these definitions; it is a field of the GPS setup.
-- source:
--   Audet, Dennis, Analysis of Generalized Pattern Searches, SIAM J. Optim. 13 (2003), p. 892, Section 2, positive spanning set D = G Zbar and Eq. (2.4)

import Mathlib

open Matrix

namespace GPSAnalysis.Core

/-- The direction matrix `D = G Z̄` (p. 892): column `j` is `d_j = G z̄_j`, with `G ∈ ℝ^{n×n}`
and `Z̄` an integer `n × |D|` matrix. -/
def dirMatrix {n p : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (Zbar : Matrix (Fin n) (Fin p) ℤ) :
    Matrix (Fin n) (Fin p) ℝ :=
  G * Zbar.map (fun z : ℤ => (z : ℝ))

/-- Column `j` of a direction matrix, as a vector of `ℝⁿ`. -/
def direction {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) (j : Fin p) : Fin n → ℝ :=
  fun i => D i j

/-- The set of nonnegative linear combinations of the columns of `D` indexed by `S`. -/
def nonnegSpan {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) (S : Finset (Fin p)) :
    Set (Fin n → ℝ) :=
  {v | ∃ c : Fin p → ℝ, (∀ j, 0 ≤ c j) ∧ v = ∑ j ∈ S, c j • direction D j}

/-- The columns of `D` indexed by `S` form a positive spanning set of `ℝⁿ` (p. 892): their
nonnegative linear combinations span `ℝⁿ`. -/
def IsPositiveSpanning {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) (S : Finset (Fin p)) : Prop :=
  nonnegSpan D S = Set.univ

/-- The mesh (2.4): `M_k = {x_k + Δ_k D z : z ∈ ℤ₊^{|D|}}`, centred at `xk` with mesh size
parameter `Δk`. -/
def mesh {n p : ℕ} (D : Matrix (Fin n) (Fin p) ℝ) (xk : Fin n → ℝ) (Δk : ℝ) :
    Set (Fin n → ℝ) :=
  {y | ∃ z : Fin p → ℕ, y = xk + Δk • (D *ᵥ (fun j => (z j : ℝ)))}

end GPSAnalysis.Core


