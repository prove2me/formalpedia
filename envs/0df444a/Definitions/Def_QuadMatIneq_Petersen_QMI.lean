-- Prove2me | Definitions.Def_QuadMatIneq_Petersen_QMI
-- name    : QuadMatIneq_Petersen_QMI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:32.072435+00:00
-- url     : https://prove2.me/theorems/f9f452e3-17b7-4519-9563-1e0eae1253df
-- title:
--   §1.1, §3, (3.5) — pseudo-inverse, QMI sets $\mathcal Z_r(\Pi)$, $\mathcal Z_r^+(\Pi)$, $\mathcal Z_r^0(\Pi)$, Schur complement $\Pi\,|\,\Pi_{22}$, class $\boldsymbol\Pi_{q,r}$
-- statement:
--   This file fixes the matrix objects of Sections 1.1 and 3 of van Waarde, Camlibel, Eising and Trentelman. All matrices are real.
--
--   1. **Moore–Penrose pseudo-inverse.** For $A\in\mathbb R^{a\times b}$, a matrix $X\in\mathbb R^{b\times a}$ satisfies the *Penrose conditions* if
--   $$AXA=A,\qquad XAX=X,\qquad (AX)^\top=AX,\qquad (XA)^\top=XA .$$
--   Such an $X$ exists and is unique; it is the pseudo-inverse $A^\dagger$.
--
--   2. **Quadratic matrix inequalities.** Let $\Pi\in\mathbb S^{q+r}$ be partitioned as $\Pi=\begin{bmatrix}\Pi_{11}&\Pi_{12}\\ \Pi_{21}&\Pi_{22}\end{bmatrix}$ with $\Pi_{11}$ of size $q\times q$ and $\Pi_{22}$ of size $r\times r$. For $Z\in\mathbb R^{r\times q}$ the quadratic form is $\begin{bmatrix}I_q\\ Z\end{bmatrix}^\top\Pi\begin{bmatrix}I_q\\ Z\end{bmatrix}\in\mathbb R^{q\times q}$, and
--   $$\mathcal Z_r(\Pi)=\Big\{Z:\begin{bmatrix}I_q\\ Z\end{bmatrix}^\top\Pi\begin{bmatrix}I_q\\ Z\end{bmatrix}\geqslant0\Big\},\quad \mathcal Z_r^+(\Pi)=\{Z:\cdots>0\},\quad \mathcal Z_r^0(\Pi)=\{Z:\cdots=0\}.$$
--
--   3. **Schur complement and the class $\boldsymbol\Pi_{q,r}$.** The generalized Schur complement is $\Pi\,|\,\Pi_{22}:=\Pi_{11}-\Pi_{12}\Pi_{22}^\dagger\Pi_{21}$, and
--   $$\boldsymbol\Pi_{q,r}=\{\Pi\in\mathbb S^{q+r}:\ \Pi_{22}\leqslant0,\ \Pi\,|\,\Pi_{22}\geqslant0,\ \ker\Pi_{22}\subseteq\ker\Pi_{12}\}.$$
--
--   Here $A\geqslant0$ ($A>0$) means $A$ is symmetric positive semidefinite (definite), as in §1.1 of the paper. These objects are the language of every matrix S-lemma in the paper.
--
--   **Formalization Note** The pseudo-inverse is chosen by Hilbert's $\varepsilon$ among the matrices satisfying the four Penrose conditions; since such a matrix exists and is unique, this is exactly $A^\dagger$ and never a junk value (Mathlib's `A⁻¹` would be $0$ on singular $\Pi_{22}$). The index sets of the two blocks are arbitrary finite types `ι` (size $q$) and `κ` (size $r$); $\mathbb R^{r\times q}$ is `Matrix κ ι ℝ`. Positive (semi)definiteness is Mathlib's `PosDef`/`PosSemidef`, which includes symmetry; $\Pi_{22}\leqslant0$ is `(-Π₂₂).PosSemidef`; a kernel inclusion is stated with matrix–vector products.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §1.1 p. 3; §3 pp. 5–6, (3.2), (3.5) and the definitions of 𝒵_r(Π), 𝒵_r^+(Π), 𝒵_r^0(Π)

import Mathlib

namespace QuadMatIneq.Petersen

open Matrix

section PseudoInverse

variable {a b : Type*} [Fintype a] [Fintype b]

/-- The four Penrose conditions: `X` is a Moore–Penrose pseudo-inverse of `A`. -/
def IsMoorePenrose (A : Matrix a b ℝ) (X : Matrix b a ℝ) : Prop :=
  A * X * A = A ∧ X * A * X = X ∧ (A * X)ᵀ = A * X ∧ (X * A)ᵀ = X * A

/-- The Moore–Penrose pseudo-inverse `A†` (§1.1), chosen by `Classical.epsilon` among the
matrices satisfying the four Penrose conditions; such a matrix exists and is unique. -/
noncomputable def pinv (A : Matrix a b ℝ) : Matrix b a ℝ :=
  Classical.epsilon (IsMoorePenrose A)

end PseudoInverse

section QMI

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The quadratic form `[I_q; Z]ᵀ Π [I_q; Z]` of a partitioned `Π ∈ 𝕊^{q+r}`. -/
def qmiForm (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (Z : Matrix κ ι ℝ) : Matrix ι ι ℝ :=
  (Matrix.fromRows (1 : Matrix ι ι ℝ) Z)ᵀ * P * Matrix.fromRows (1 : Matrix ι ι ℝ) Z

/-- `𝒵_r(Π) = {Z ∈ ℝ^{r×q} | [I; Z]ᵀ Π [I; Z] ⩾ 0}`. -/
def ZSet (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Set (Matrix κ ι ℝ) :=
  {Z | (qmiForm P Z).PosSemidef}

/-- `𝒵_r^+(Π) = {Z ∈ ℝ^{r×q} | [I; Z]ᵀ Π [I; Z] > 0}`. -/
def ZPlus (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Set (Matrix κ ι ℝ) :=
  {Z | (qmiForm P Z).PosDef}

/-- `𝒵_r^0(Π) = {Z ∈ ℝ^{r×q} | [I; Z]ᵀ Π [I; Z] = 0}`. -/
def ZZero (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Set (Matrix κ ι ℝ) :=
  {Z | qmiForm P Z = 0}

/-- The generalized Schur complement `Π | Π₂₂ := Π₁₁ − Π₁₂ Π₂₂† Π₂₁`. -/
noncomputable def schur (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Matrix ι ι ℝ :=
  P.toBlocks₁₁ - P.toBlocks₁₂ * pinv P.toBlocks₂₂ * P.toBlocks₂₁

/-- `Π ∈ 𝚷_{q,r}` (3.5): `Π` symmetric, `Π₂₂ ⩽ 0`, `Π | Π₂₂ ⩾ 0` and `ker Π₂₂ ⊆ ker Π₁₂`. -/
def InPi (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Prop :=
  P.IsHermitian ∧ (-P.toBlocks₂₂).PosSemidef ∧ (schur P).PosSemidef ∧
    ∀ v : κ → ℝ, P.toBlocks₂₂ *ᵥ v = 0 → P.toBlocks₁₂ *ᵥ v = 0

end QMI

end QuadMatIneq.Petersen


