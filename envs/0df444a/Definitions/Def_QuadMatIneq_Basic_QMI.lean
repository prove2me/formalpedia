-- Prove2me | Definitions.Def_QuadMatIneq_Basic_QMI
-- name    : QuadMatIneq_Basic_QMI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:20.68411+00:00
-- url     : https://prove2.me/theorems/131925a2-7db7-4fbb-8c55-0ea9cbdff3ee
-- title:
--   §1.1, §3 (3.2), (3.5) — Moore–Penrose pseudo-inverse, the QMI sets 𝒵_r(Π), 𝒵_r^+(Π), 𝒵_r^0(Π), the Schur complement Π|Π₂₂ and the class 𝚷_{q,r}
-- statement:
--   All matrices are real. Fix integers $q, r \ge 0$ (in Lean: finite index types $\iota$, $\kappa$ with $q = |\iota|$, $r = |\kappa|$). This file sets up the objects of §1.1 and §3 of van Waarde–Camlibel–Eising–Trentelman.
--
--   1. **Moore–Penrose pseudo-inverse.** For $A \in \mathbb{R}^{m\times n}$, a matrix $X \in \mathbb{R}^{n\times m}$ is a Moore–Penrose pseudo-inverse of $A$ if it satisfies the four Penrose conditions
--   $$AXA = A,\qquad XAX = X,\qquad (AX)^\top = AX,\qquad (XA)^\top = XA.$$
--   Such an $X$ exists and is unique; it is denoted $A^\dagger$.
--
--   2. **Partition.** A symmetric matrix $\Pi \in \mathbb{S}^{q+r}$ is partitioned as
--   $$\Pi = \begin{bmatrix} \Pi_{11} & \Pi_{12} \\ \Pi_{21} & \Pi_{22}\end{bmatrix},$$
--   with $\Pi_{11}$ of size $q\times q$ and $\Pi_{22}$ of size $r \times r$.
--
--   3. **Quadratic matrix inequality.** For $Z \in \mathbb{R}^{r\times q}$ put $F_\Pi(Z) := \begin{bmatrix} I_q \\ Z\end{bmatrix}^\top \Pi \begin{bmatrix} I_q \\ Z\end{bmatrix} \in \mathbb{R}^{q \times q}$, and
--   $$\mathcal Z_r(\Pi) = \{Z : F_\Pi(Z) \ge 0\},\quad \mathcal Z_r^+(\Pi) = \{Z : F_\Pi(Z) > 0\},\quad \mathcal Z_r^0(\Pi) = \{Z : F_\Pi(Z) = 0\},$$
--   where $\ge 0$ and $> 0$ denote positive semidefiniteness and positive definiteness.
--
--   4. **Generalized Schur complement.** $\Pi\,|\,\Pi_{22} := \Pi_{11} - \Pi_{12}\Pi_{22}^\dagger\Pi_{21}$.
--
--   5. **The class $\boldsymbol\Pi_{q,r}$** (3.5): the symmetric $\Pi$ with $\Pi_{22} \le 0$, $\Pi\,|\,\Pi_{22} \ge 0$ and $\ker \Pi_{22} \subseteq \ker \Pi_{12}$.
--
--   These are the objects about which the basic properties of QMI solution sets (Theorem 3.2) are stated; every later result of the paper is phrased in them.
--
--   **Formalization Note.** Mathlib has no matrix pseudo-inverse, so $A^\dagger$ is `Classical.epsilon` applied to the four Penrose conditions; since a matrix satisfying them exists and is unique, this is exactly $A^\dagger$ (and not the total inverse `A⁻¹`, which is $0$ on singular matrices). Positive (semi)definiteness is Mathlib's `PosDef`/`PosSemidef`, which include symmetry, as the paper's notation does (§1.1). Kernel inclusion $\ker A \subseteq \ker B$ is written $\forall v,\ Av = 0 \Rightarrow Bv = 0$. Symmetry of $\Pi$ is `IsHermitian`, which over $\mathbb R$ is $\Pi^\top = \Pi$.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §1.1 p. 3; §3 pp. 5–6, display after (3.2) and (3.5)

import Mathlib

namespace QuadMatIneq.Basic

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

end QuadMatIneq.Basic


