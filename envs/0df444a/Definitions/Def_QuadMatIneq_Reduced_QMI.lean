-- Prove2me | Definitions.Def_QuadMatIneq_Reduced_QMI
-- name    : QuadMatIneq_Reduced_QMI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:58:12.014526+00:00
-- url     : https://prove2.me/theorems/b479aea5-204a-42bd-af76-0af5bea201ae
-- title:
--   §1.1, §3 (3.2), (3.5), (3.9) — Moore–Penrose pseudo-inverse, the QMI sets 𝒵_r(Π), 𝒵_r^+(Π), 𝒵_r^0(Π), the Schur complement Π|Π₂₂, the class 𝚷_{q,r}, Π_W and 𝒮W
-- statement:
--   This file fixes the vocabulary of quadratic matrix inequalities (QMIs) used throughout the mission. All matrices are real.
--
--   **Pseudo-inverse.** For a matrix $A \in \mathbb R^{a\times b}$, the Moore–Penrose pseudo-inverse $A^\dagger \in \mathbb R^{b\times a}$ is the unique matrix $X$ satisfying the four Penrose conditions
--   $$AXA = A,\qquad XAX = X,\qquad (AX)^\top = AX,\qquad (XA)^\top = XA.$$
--
--   **QMI solution sets.** Let $\Pi \in \mathbb S^{q+r}$ be partitioned as $\Pi = \begin{bmatrix}\Pi_{11} & \Pi_{12}\\ \Pi_{21} & \Pi_{22}\end{bmatrix}$ with $\Pi_{11}$ of size $q\times q$ and $\Pi_{22}$ of size $r\times r$. For $Z \in \mathbb R^{r\times q}$ write
--   $$\begin{bmatrix} I_q \\ Z\end{bmatrix}^\top \Pi \begin{bmatrix} I_q \\ Z\end{bmatrix} \in \mathbb R^{q\times q}.$$
--   The sets $\mathcal Z_r(\Pi)$, $\mathcal Z_r^+(\Pi)$ and $\mathcal Z_r^0(\Pi)$ consist of all $Z\in\mathbb R^{r\times q}$ for which this matrix is positive semidefinite, positive definite, or zero, respectively.
--
--   **Schur complement and the class $\boldsymbol\Pi_{q,r}$.** The generalized Schur complement of $\Pi$ with respect to $\Pi_{22}$ is
--   $$\Pi\,|\,\Pi_{22} := \Pi_{11} - \Pi_{12}\Pi_{22}^\dagger\Pi_{21},$$
--   and $\boldsymbol\Pi_{q,r}$ is the set of symmetric $\Pi\in\mathbb S^{q+r}$ with $\Pi_{22}\le 0$, $\Pi\,|\,\Pi_{22}\ge 0$ and $\ker\Pi_{22}\subseteq\ker\Pi_{12}$.
--
--   **Images under right multiplication.** For $W \in \mathbb R^{q\times p}$ and $\mathcal S\subseteq\mathbb R^{r\times q}$, $\mathcal S W := \{SW : S\in\mathcal S\}\subseteq \mathbb R^{r\times p}$, and
--   $$\Pi_W := \begin{bmatrix} W^\top & 0\\ 0 & I_r\end{bmatrix}\Pi\begin{bmatrix} W & 0\\ 0 & I_r\end{bmatrix} = \begin{bmatrix} W^\top\Pi_{11}W & W^\top\Pi_{12}\\ \Pi_{21}W & \Pi_{22}\end{bmatrix}\in\mathbb S^{p+r}.$$
--
--   These objects carry every statement of the mission: the parameterization of QMI solution sets, their images under linear maps, and the data-driven stabilization LMIs.
--
--   **Formalization Note** The order relations follow the paper's convention that $A \ge 0$ includes symmetry (Mathlib's `PosSemidef`). The pseudo-inverse is defined by choice (`Classical.epsilon`) among matrices satisfying the four Penrose conditions; since such a matrix always exists and is unique, this is exactly $A^\dagger$ (Mathlib's total inverse `A⁻¹`, which is $0$ on singular matrices, is not used). The index types of the two blocks are arbitrary finite types, so $q$ and $r$ are their cardinalities; kernel inclusions are stated pointwise on vectors.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §1.1 p. 3, §3 pp. 5–6, (3.2), (3.5); §3.3 p. 8, (3.9)

import Mathlib

namespace QuadMatIneq.Reduced

open Matrix

section PseudoInverse

variable {a b : Type*} [Fintype a] [Fintype b]

/-- `X` satisfies the four Penrose conditions for `A`: `AXA = A`, `XAX = X`, `(AX)ᵀ = AX`,
`(XA)ᵀ = XA`. -/
def IsMoorePenrose (A : Matrix a b ℝ) (X : Matrix b a ℝ) : Prop :=
  A * X * A = A ∧ X * A * X = X ∧ (A * X)ᵀ = A * X ∧ (X * A)ᵀ = X * A

/-- The Moore–Penrose pseudo-inverse `A†` (§1.1): the matrix satisfying the four Penrose
conditions, which exists and is unique for every real matrix. -/
noncomputable def pinv (A : Matrix a b ℝ) : Matrix b a ℝ :=
  Classical.epsilon (IsMoorePenrose A)

end PseudoInverse

section QMI

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The quadratic form `[I_q; Z]ᵀ Π [I_q; Z]` of a QMI, for `Π ∈ 𝕊^{q+r}` partitioned with
`Π₁₁` of size `q × q` and `Π₂₂` of size `r × r`, and `Z ∈ ℝ^{r×q}`. -/
def qmiForm (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (Z : Matrix κ ι ℝ) : Matrix ι ι ℝ :=
  (Matrix.fromRows (1 : Matrix ι ι ℝ) Z)ᵀ * P * Matrix.fromRows (1 : Matrix ι ι ℝ) Z

/-- `𝒵_r(Π)`: all `Z ∈ ℝ^{r×q}` with `[I; Z]ᵀ Π [I; Z] ⩾ 0`. -/
def ZSet (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Set (Matrix κ ι ℝ) :=
  {Z | (qmiForm P Z).PosSemidef}

/-- `𝒵_r^+(Π)`: all `Z ∈ ℝ^{r×q}` with `[I; Z]ᵀ Π [I; Z] > 0`. -/
def ZPlus (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Set (Matrix κ ι ℝ) :=
  {Z | (qmiForm P Z).PosDef}

/-- `𝒵_r^0(Π)`: all `Z ∈ ℝ^{r×q}` with `[I; Z]ᵀ Π [I; Z] = 0`. -/
def ZZero (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Set (Matrix κ ι ℝ) :=
  {Z | qmiForm P Z = 0}

/-- The generalized Schur complement `Π | Π₂₂ := Π₁₁ − Π₁₂ Π₂₂† Π₂₁` of (3.2). -/
noncomputable def schur (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Matrix ι ι ℝ :=
  P.toBlocks₁₁ - P.toBlocks₁₂ * pinv P.toBlocks₂₂ * P.toBlocks₂₁

/-- `Π ∈ 𝚷_{q,r}` (3.5): `Π` symmetric, `Π₂₂ ⩽ 0`, `Π | Π₂₂ ⩾ 0` and `ker Π₂₂ ⊆ ker Π₁₂`. -/
def InPi (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Prop :=
  P.IsHermitian ∧ (-P.toBlocks₂₂).PosSemidef ∧ (schur P).PosSemidef ∧
    ∀ v, P.toBlocks₂₂ *ᵥ v = 0 → P.toBlocks₁₂ *ᵥ v = 0

variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

/-- `Π_W := [Wᵀ 0; 0 I_r] Π [W 0; 0 I_r] ∈ 𝕊^{p+r}` of (3.9), for `W ∈ ℝ^{q×p}`. -/
def PiW (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (W : Matrix ι ρ ℝ) : Matrix (ρ ⊕ κ) (ρ ⊕ κ) ℝ :=
  Matrix.fromBlocks Wᵀ 0 0 (1 : Matrix κ κ ℝ) * P * Matrix.fromBlocks W 0 0 (1 : Matrix κ κ ℝ)

/-- `𝒮W := {SW : S ∈ 𝒮}` (§3.3), for `𝒮 ⊆ ℝ^{r×q}` and `W ∈ ℝ^{q×p}`. -/
def setMul (S : Set (Matrix κ ι ℝ)) (W : Matrix ι ρ ℝ) : Set (Matrix κ ρ ℝ) :=
  (fun Z => Z * W) '' S

end QMI

end QuadMatIneq.Reduced


