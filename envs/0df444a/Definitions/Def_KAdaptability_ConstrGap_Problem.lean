-- Prove2me | Definitions.Def_KAdaptability_ConstrGap_Problem
-- name    : KAdaptability_ConstrGap_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:59:39.258454+00:00
-- url     : https://prove2.me/theorems/b17f564a-2a54-4773-9f5d-0523cd2e9578
-- title:
--   Data of the generic two-stage robust binary program 𝒫 and its uncertainty set Ξ
-- statement:
--   An instance of the generic two-stage robust binary program $\mathcal P$ (uncertainty in the objective **and** in the constraint right-hand sides) consists of the following data. There are $N$ first-stage variables, $M$ second-stage variables, $L$ second-stage constraints and $Q$ uncertain parameters; the paper uses the letter $Q$ both for this dimension and for a matrix, so in Lean the dimension is called `nQ` and the matrix `Q`.
--
--   1. Matrices $C\in\mathbb R^{Q\times N}$, $Q\in\mathbb R^{Q\times M}$, $T\in\mathbb R^{L\times N}$, $W\in\mathbb R^{L\times M}$ and $H\in\mathbb R^{L\times Q}$.
--   2. An uncertainty set
--   $$\Xi=\{\xi\in\mathbb R^Q : A\xi\le b\},\qquad A\in\mathbb R^{R\times Q},\ b\in\mathbb R^R,$$
--   (componentwise inequality), which is assumed to be a **nonempty bounded** polyhedron.
--   3. A first-stage feasible set $\mathcal X\subseteq\{0,1\}^N$.
--   4. A second-stage feasible set $\mathcal Y\subseteq\{0,1\}^M$ of binary vectors (hence finite).
--
--   These are the standing assumptions of §1 (p. 6) of the paper, together with the assumption $\mathcal X\subseteq\{0,1\}^N$ made throughout §3 (p. 14), the section that studies $\mathcal P$ with constraint uncertainty. The right-hand side $H\xi$ is linear in $\xi$; affine dependence is modelled, as on p. 6, by an auxiliary parameter $\xi_{Q+1}$ with the constraint $\xi_{Q+1}=1$ added to $\Xi$.
--
--   **Formalization Note** $\mathcal X$ is a `Set` of 0/1 vectors and $\mathcal Y$ a `Finset` of 0/1 vectors; every subset of $\{0,1\}^n$ is the set of binary points of a polyhedron, so these are exactly the paper's classes. Nonemptiness and boundedness of $\Xi$ are fields of the structure, so every instance must prove them.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 6 (problem (P), its data, Ξ a nonempty bounded polyhedron, affine dependence via ξ_{Q+1} = 1), p. 14 (§3: 𝒳 ⊆ {0,1}^N)

import Mathlib

open Matrix

namespace KAdaptability.ConstrGap

/-- The data of the generic two-stage robust binary program 𝒫 (p. 6 of Hanasusanto–Kuhn–Wiesemann),
under the standing assumptions of §3 (p. 14). Dimensions: `N` first-stage variables, `M`
second-stage variables, `L` second-stage constraints, `nQ` uncertain parameters (the paper's `Q`),
`R` rows of the description of the uncertainty set. The matrix the paper calls `Q` is the field `Q`.
Standing assumptions carried as fields: `𝒳 ⊆ {0,1}^N` (§3, p. 14), every point of `𝒴` is a 0/1
vector (so `𝒴` is finite), and `Ξ = {ξ : Aξ ≤ b}` is a nonempty bounded polyhedron (p. 6). -/
structure Problem (N M L nQ R : ℕ) where
  /-- First-stage objective matrix `C ∈ ℝ^{Q×N}`. -/
  C : Matrix (Fin nQ) (Fin N) ℝ
  /-- Second-stage objective matrix `Q ∈ ℝ^{Q×M}`. -/
  Q : Matrix (Fin nQ) (Fin M) ℝ
  /-- Technology matrix `T ∈ ℝ^{L×N}`. -/
  T : Matrix (Fin L) (Fin N) ℝ
  /-- Recourse matrix `W ∈ ℝ^{L×M}`. -/
  W : Matrix (Fin L) (Fin M) ℝ
  /-- Uncertain right-hand side matrix `H ∈ ℝ^{L×Q}`. -/
  H : Matrix (Fin L) (Fin nQ) ℝ
  /-- Uncertainty set description `A ∈ ℝ^{R×Q}`. -/
  A : Matrix (Fin R) (Fin nQ) ℝ
  /-- Uncertainty set description `b ∈ ℝ^R`. -/
  b : Fin R → ℝ
  /-- First-stage feasible set `𝒳`. -/
  X : Set (Fin N → ℝ)
  /-- Second-stage feasible set `𝒴`. -/
  Y : Finset (Fin M → ℝ)
  /-- `𝒳 ⊆ {0,1}^N` (standing assumption of §3). -/
  X_binary : ∀ x ∈ X, ∀ i, x i = 0 ∨ x i = 1
  /-- `𝒴 ⊆ {0,1}^M`. -/
  Y_binary : ∀ y ∈ Y, ∀ j, y j = 0 ∨ y j = 1
  /-- `Ξ` is nonempty. -/
  Xi_nonempty : {ξ : Fin nQ → ℝ | A *ᵥ ξ ≤ b}.Nonempty
  /-- `Ξ` is bounded. -/
  Xi_bounded : Bornology.IsBounded {ξ : Fin nQ → ℝ | A *ᵥ ξ ≤ b}

variable {N M L nQ R : ℕ}

/-- The uncertainty set `Ξ = {ξ ∈ ℝ^Q : Aξ ≤ b}` (componentwise inequality). -/
def Problem.Xi (P : Problem N M L nQ R) : Set (Fin nQ → ℝ) :=
  {ξ | P.A *ᵥ ξ ≤ P.b}

end KAdaptability.ConstrGap


