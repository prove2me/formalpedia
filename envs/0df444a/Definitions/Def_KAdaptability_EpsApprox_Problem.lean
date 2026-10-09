-- Prove2me | Definitions.Def_KAdaptability_EpsApprox_Problem
-- name    : KAdaptability_EpsApprox_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:59:14.936976+00:00
-- url     : https://prove2.me/theorems/77eb9f5f-51ec-49b2-bfd2-9737c0668848
-- title:
--   Data of the two-stage robust binary program 𝒫 with constraint uncertainty, binary first stage (§3)
-- statement:
--   An instance of the two-stage robust binary program with constraint uncertainty consists of the following data. There are $N$ first-stage variables, $M$ second-stage variables, $L$ second-stage constraints and $Q$ uncertain parameters; the paper uses the letter $Q$ both for this dimension and for a matrix, so in Lean the dimension is called `nQ` and the matrix `Q`.
--
--   1. Matrices $C\in\mathbb R^{Q\times N}$, $Q\in\mathbb R^{Q\times M}$, $T\in\mathbb R^{L\times N}$, $W\in\mathbb R^{L\times M}$ and $H\in\mathbb R^{L\times Q}$.
--   2. An uncertainty set $\Xi=\{\xi\in\mathbb R^Q : A\xi\le b\}$ with $A\in\mathbb R^{R\times Q}$, $b\in\mathbb R^R$ (componentwise inequality), which is assumed **nonempty and bounded**.
--   3. A first-stage feasible set $\mathcal X\subseteq\{0,1\}^N$.
--   4. A finite second-stage feasible set $\mathcal Y\subseteq\{0,1\}^M$.
--
--   The second-stage constraints read $Tx+Wy\le H\xi$, and the cost of a first-stage decision $x$ and a second-stage decision $y$ under the parameter $\xi$ is $\xi^\top Cx+\xi^\top Qy$. A **decision** with $K$ policies is a pair $(x,\{y^k\}_{k\in\mathcal K})\in\mathcal X\times\mathcal Y^K$, $\mathcal K=\{1,\dots,K\}$.
--
--   These are the standing assumptions of §1 (p. 6) of the paper together with the assumption $\mathcal X\subseteq\{0,1\}^N$ that holds throughout §3 (p. 14).
--
--   **Formalization Note** Parameters $\xi$ live in `EuclideanSpace ℝ (Fin nQ)`, so that norms and distances are Euclidean as in the paper; `ξ.ofLp` is the underlying coordinate vector. A subset of $\{0,1\}^M$ is exactly the set of binary points of a polyhedron, so $\mathcal Y$ is a `Finset` of 0/1 vectors. The decision index set $\mathcal K$ is `Fin K`.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. 6 (problem (P) and its data; Ξ a nonempty bounded polyhedron), p. 14 (§3 standing assumption 𝒳 ⊆ {0,1}^N)

import Mathlib

open Matrix

namespace KAdaptability.EpsApprox

/-- The data of the two-stage robust binary program with constraint uncertainty (𝒫), p. 6 of
Hanasusanto–Kuhn–Wiesemann, under the standing assumption of §3 (p. 14) that `𝒳 ⊆ {0,1}^N`.
Dimensions: `N` first-stage variables, `M` second-stage variables, `L` second-stage constraints,
`nQ` uncertain parameters (the paper's `Q`), `R` rows of the uncertainty set's description.
The matrix the paper calls `Q` is the field `Q`.
The standing assumptions are part of the data: every point of `𝒳` is a 0/1 vector, every point
of `𝒴` is a 0/1 vector (so `𝒴` is finite), and `Ξ = {ξ : Aξ ≤ b}` is a nonempty bounded
polyhedron. -/
structure Problem (N M L nQ R : ℕ) where
  /-- First-stage objective matrix `C ∈ ℝ^{Q×N}`. -/
  C : Matrix (Fin nQ) (Fin N) ℝ
  /-- Second-stage objective matrix `Q ∈ ℝ^{Q×M}`. -/
  Q : Matrix (Fin nQ) (Fin M) ℝ
  /-- Technology matrix `T ∈ ℝ^{L×N}`. -/
  T : Matrix (Fin L) (Fin N) ℝ
  /-- Recourse matrix `W ∈ ℝ^{L×M}`. -/
  W : Matrix (Fin L) (Fin M) ℝ
  /-- Right-hand side matrix `H ∈ ℝ^{L×Q}`. -/
  H : Matrix (Fin L) (Fin nQ) ℝ
  /-- Uncertainty set description `A ∈ ℝ^{R×Q}`. -/
  A : Matrix (Fin R) (Fin nQ) ℝ
  /-- Uncertainty set description `b ∈ ℝ^R`. -/
  b : Fin R → ℝ
  /-- First-stage feasible set `𝒳`. -/
  X : Set (Fin N → ℝ)
  /-- Second-stage feasible set `𝒴`. -/
  Y : Finset (Fin M → ℝ)
  /-- `𝒳 ⊆ {0,1}^N` (standing assumption of §3, p. 14). -/
  X_binary : ∀ x ∈ X, ∀ i, x i = 0 ∨ x i = 1
  /-- `𝒴 ⊆ {0,1}^M`. -/
  Y_binary : ∀ y ∈ Y, ∀ i, y i = 0 ∨ y i = 1
  /-- `Ξ` is nonempty. -/
  Xi_nonempty : {ξ : Fin nQ → ℝ | A *ᵥ ξ ≤ b}.Nonempty
  /-- `Ξ` is bounded. -/
  Xi_bounded : Bornology.IsBounded {ξ : Fin nQ → ℝ | A *ᵥ ξ ≤ b}

namespace Problem

variable {N M L nQ R : ℕ} (P : Problem N M L nQ R)

/-- The uncertainty set `Ξ = {ξ ∈ ℝ^Q : Aξ ≤ b}`, as a subset of Euclidean space `ℝ^Q` (the
paper's norm is the Euclidean one). -/
def Xi : Set (EuclideanSpace ℝ (Fin nQ)) :=
  {ξ | P.A *ᵥ ξ.ofLp ≤ P.b}

/-- The left-hand side `Tx + Wy` of the second-stage constraints `Tx + Wy ≤ Hξ`. -/
def lhs (x : Fin N → ℝ) (y : Fin M → ℝ) : Fin L → ℝ :=
  P.T *ᵥ x + P.W *ᵥ y

/-- The right-hand side `Hξ` of the second-stage constraints. -/
def rhs (ξ : EuclideanSpace ℝ (Fin nQ)) : Fin L → ℝ :=
  P.H *ᵥ ξ.ofLp

/-- The cost `ξ⊤Cx + ξ⊤Qy` of the first-stage decision `x` and the second-stage policy `y`
under the parameter `ξ`, split into its two terms. -/
def firstCost (ξ : EuclideanSpace ℝ (Fin nQ)) (x : Fin N → ℝ) : ℝ :=
  ξ.ofLp ⬝ᵥ (P.C *ᵥ x)

/-- The second-stage cost `ξ⊤Qy`. -/
def secondCost (ξ : EuclideanSpace ℝ (Fin nQ)) (y : Fin M → ℝ) : ℝ :=
  ξ.ofLp ⬝ᵥ (P.Q *ᵥ y)

/-- A decision `(x, {y^k}_{k∈𝒦}) ∈ 𝒳 × 𝒴^K` with `K` second-stage policies. -/
def IsDecision {K : ℕ} (x : Fin N → ℝ) (y : Fin K → Fin M → ℝ) : Prop :=
  x ∈ P.X ∧ ∀ k, y k ∈ P.Y

end Problem

end KAdaptability.EpsApprox


