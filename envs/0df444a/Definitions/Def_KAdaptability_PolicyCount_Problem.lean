-- Prove2me | Definitions.Def_KAdaptability_PolicyCount_Problem
-- name    : KAdaptability_PolicyCount_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:01:26.088499+00:00
-- url     : https://prove2.me/theorems/156d51d9-4ba1-4db0-8cd5-fed2c58bc31c
-- title:
--   Data of the two-stage robust binary program with objective uncertainty, the uncertainty set Ξ and dim 𝒴
-- statement:
--   An instance of the two-stage robust binary program with objective uncertainty consists of the following data. There are $N$ first-stage variables, $M$ second-stage variables, $L$ second-stage constraints and $Q$ uncertain parameters; the paper uses the letter $Q$ both for this dimension and for a matrix, so in Lean the dimension is called `nQ` and the matrix `Q`.
--
--   1. Matrices $C\in\mathbb R^{Q\times N}$, $Q\in\mathbb R^{Q\times M}$, $T\in\mathbb R^{L\times N}$, $W\in\mathbb R^{L\times M}$ and a right-hand side $h\in\mathbb R^L$.
--   2. An uncertainty set $\Xi=\{\xi\in\mathbb R^Q : A\xi\le b\}$ with $A\in\mathbb R^{R\times Q}$, $b\in\mathbb R^R$ (componentwise inequality), which is assumed **nonempty and bounded**.
--   3. A first-stage feasible set $\mathcal X\subseteq\mathbb R^N_+$.
--   4. A finite second-stage feasible set $\mathcal Y\subseteq\{0,1\}^M$ of binary vectors.
--
--   The **affine dimension** of $\mathcal Y$ is
--   $$\dim\mathcal Y=\dim\operatorname{span}\{y-y' : y,y'\in\mathcal Y\},$$
--   the dimension of the smallest affine subspace containing $\mathcal Y$.
--
--   These are the standing assumptions of §1 (p. 6) and §2 (p. 10) of the paper; every problem of this mission is built from this data.
--
--   **Formalization Note** $\mathcal X$ is an arbitrary set of nonnegative vectors (the paper allows continuous and binary first-stage components, and its endnote 1 says boundedness of $\mathcal X$ is for exposition only). A subset of $\{0,1\}^M$ is exactly the set of binary points of a polyhedron, so $\mathcal Y$ is a `Finset` of 0/1 vectors. Nonemptiness and boundedness of $\Xi$ are fields of the structure. For $\mathcal Y=\emptyset$ the Lean affine dimension is $0$ (the paper's convention would give $-1$); every statement of the mission holds under either reading in that case.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 6 (problem (P) and its data, Ξ nonempty bounded polyhedron), p. 10 (problem (PO), h ∈ ℝ^L), p. 12 (Theorem 1: affine dimension of 𝒴)

import Mathlib

open Matrix

namespace KAdaptability.PolicyCount

/-- The data of the two-stage robust binary program with objective uncertainty (𝒫𝒪), p. 6 and
p. 10 of Hanasusanto–Kuhn–Wiesemann. Dimensions: `N` first-stage variables, `M` second-stage
variables, `L` second-stage constraints, `nQ` uncertain parameters (the paper's `Q`), `R` rows of
the uncertainty set's description. The matrix the paper calls `Q` is the field `Q`.
The standing assumptions of §1 are part of the data: `𝒳 ⊆ ℝ^N_+`, every point of `𝒴` is a
0/1 vector (so `𝒴` is finite), and `Ξ = {ξ : Aξ ≤ b}` is a nonempty bounded polyhedron. -/
structure Problem (N M L nQ R : ℕ) where
  /-- First-stage objective matrix `C ∈ ℝ^{Q×N}`. -/
  C : Matrix (Fin nQ) (Fin N) ℝ
  /-- Second-stage objective matrix `Q ∈ ℝ^{Q×M}`. -/
  Q : Matrix (Fin nQ) (Fin M) ℝ
  /-- Technology matrix `T ∈ ℝ^{L×N}`. -/
  T : Matrix (Fin L) (Fin N) ℝ
  /-- Recourse matrix `W ∈ ℝ^{L×M}`. -/
  W : Matrix (Fin L) (Fin M) ℝ
  /-- Deterministic right-hand side `h ∈ ℝ^L`. -/
  h : Fin L → ℝ
  /-- Uncertainty set description `A ∈ ℝ^{R×Q}`. -/
  A : Matrix (Fin R) (Fin nQ) ℝ
  /-- Uncertainty set description `b ∈ ℝ^R`. -/
  b : Fin R → ℝ
  /-- First-stage feasible set `𝒳`. -/
  X : Set (Fin N → ℝ)
  /-- Second-stage feasible set `𝒴`. -/
  Y : Finset (Fin M → ℝ)
  /-- `𝒳 ⊆ ℝ^N_+`. -/
  X_nonneg : ∀ x ∈ X, 0 ≤ x
  /-- `𝒴 ⊆ {0,1}^M`. -/
  Y_binary : ∀ y ∈ Y, ∀ i, y i = 0 ∨ y i = 1
  /-- `Ξ` is nonempty. -/
  Xi_nonempty : {ξ : Fin nQ → ℝ | A *ᵥ ξ ≤ b}.Nonempty
  /-- `Ξ` is bounded. -/
  Xi_bounded : Bornology.IsBounded {ξ : Fin nQ → ℝ | A *ᵥ ξ ≤ b}

variable {N M L nQ R : ℕ}

/-- The uncertainty set `Ξ = {ξ ∈ ℝ^Q : Aξ ≤ b}` (componentwise inequality). -/
def Problem.Xi (P : Problem N M L nQ R) : Set (Fin nQ → ℝ) :=
  {ξ | P.A *ᵥ ξ ≤ P.b}

/-- `dim 𝒴`, the affine dimension of `𝒴`: the dimension of the linear span of the differences
of points of `𝒴` (equal to `0` when `𝒴` is empty or a single point). -/
noncomputable def Problem.dimY (P : Problem N M L nQ R) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ (P.Y : Set (Fin M → ℝ)))

end KAdaptability.PolicyCount


