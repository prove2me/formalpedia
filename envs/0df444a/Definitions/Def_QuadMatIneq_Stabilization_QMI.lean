-- Prove2me | Definitions.Def_QuadMatIneq_Stabilization_QMI
-- name    : QuadMatIneq_Stabilization_QMI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:43.724992+00:00
-- url     : https://prove2.me/theorems/769f3d87-fd80-48a7-a11e-7a586fcbb97d
-- title:
--   §1.1, §3 (3.2), (3.5) — Moore–Penrose pseudo-inverse, the QMI sets 𝒵_r(Π), 𝒵_r^+(Π), 𝒵_r^0(Π), the Schur complement Π|Π₂₂ and the class 𝚷_{q,r}
-- statement:
--   Throughout, all matrices are real. For finite index sets $\iota,\kappa$ with $q=|\iota|$ and $r=|\kappa|$, a matrix $\Pi\in\mathbb{S}^{q+r}$ is partitioned as
--   $$\Pi=\begin{bmatrix}\Pi_{11}&\Pi_{12}\\ \Pi_{21}&\Pi_{22}\end{bmatrix},\qquad \Pi_{11}\in\mathbb{R}^{q\times q},\ \Pi_{22}\in\mathbb{R}^{r\times r}.$$
--
--   1. **Moore–Penrose pseudo-inverse.** For $A\in\mathbb{R}^{p\times s}$, $A^\dagger$ is the unique $X\in\mathbb{R}^{s\times p}$ with $AXA=A$, $XAX=X$, $(AX)^\top=AX$ and $(XA)^\top=XA$.
--   2. **Solution sets of a quadratic matrix inequality.** For $Z\in\mathbb{R}^{r\times q}$,
--   $$\mathcal Z_r(\Pi)=\Big\{Z:\begin{bmatrix}I_q\\ Z\end{bmatrix}^{\!\top}\Pi\begin{bmatrix}I_q\\ Z\end{bmatrix}\geqslant 0\Big\},$$
--   and $\mathcal Z_r^+(\Pi)$, $\mathcal Z_r^0(\Pi)$ are defined in the same way with "$>0$" and "$=0$".
--   3. **Generalized Schur complement.** $\Pi\,|\,\Pi_{22}=\Pi_{11}-\Pi_{12}\Pi_{22}^\dagger\Pi_{21}$.
--   4. **The class $\boldsymbol\Pi_{q,r}$** ((3.5)): $\Pi\in\boldsymbol\Pi_{q,r}$ if $\Pi$ is symmetric, $\Pi_{22}\leqslant 0$, $\Pi\,|\,\Pi_{22}\geqslant 0$ and $\ker\Pi_{22}\subseteq\ker\Pi_{12}$.
--
--   Here $A\geqslant 0$ means that $A$ is symmetric and positive semidefinite, $A>0$ that it is symmetric and positive definite, and $A\leqslant 0$ that $-A\geqslant 0$ (§1.1). The class $\boldsymbol\Pi_{q,r}$ is exactly the class of matrices for which $\mathcal Z_r(\Pi)$ is nonempty under the sign conditions on $\Pi_{22}$, and every noise model of the paper is of this form.
--
--   **Formalization Note** The pseudo-inverse is `Classical.epsilon` applied to the four Penrose conditions; since exactly one matrix satisfies them, this is the paper's $A^\dagger$ and not a junk value (Mathlib's `Matrix.inv` is deliberately not used, as it returns $0$ on singular matrices and $\Pi_{22}$ is typically singular). $\ker A\subseteq\ker B$ is written $\forall v,\ Av=0\Rightarrow Bv=0$. The index sets are arbitrary finite types, and $[I_q;Z]$ is `Matrix.fromRows 1 Z`.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §1.1 p. 3; §3 pp. 5–6, (3.2), (3.5)

import Mathlib

namespace QuadMatIneq.Stabilization

open Matrix

/-! §1.1 (p. 3) and §3 (pp. 5–6) of van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3:
the Moore–Penrose pseudo-inverse, the solution sets of a quadratic matrix inequality,
the generalized Schur complement and the class `𝚷_{q,r}`. -/

section PseudoInverse

variable {a b : Type*} [Fintype a] [Fintype b]

/-- `X` satisfies the four Penrose conditions for `A`: `AXA = A`, `XAX = X`, `(AX)ᵀ = AX`,
`(XA)ᵀ = XA`. These determine `X` uniquely, and such an `X` always exists. -/
def IsMoorePenrose (A : Matrix a b ℝ) (X : Matrix b a ℝ) : Prop :=
  A * X * A = A ∧ X * A * X = X ∧ (A * X)ᵀ = A * X ∧ (X * A)ᵀ = X * A

/-- The Moore–Penrose pseudo-inverse `A†` (§1.1, p. 3), chosen by `Classical.epsilon` among the
matrices satisfying the four Penrose conditions (exactly one does). -/
noncomputable def pinv (A : Matrix a b ℝ) : Matrix b a ℝ :=
  Classical.epsilon (IsMoorePenrose A)

end PseudoInverse

section QMI

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The quadratic form `[I_q; Z]ᵀ Π [I_q; Z]` of a QMI, for `Π ∈ 𝕊^{q+r}` partitioned with
`Π₁₁` of size `q × q` (index `ι`) and `Π₂₂` of size `r × r` (index `κ`), and `Z ∈ ℝ^{r×q}`. -/
def qmiForm (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (Z : Matrix κ ι ℝ) : Matrix ι ι ℝ :=
  (Matrix.fromRows (1 : Matrix ι ι ℝ) Z)ᵀ * P * Matrix.fromRows (1 : Matrix ι ι ℝ) Z

/-- `𝒵_r(Π) = {Z ∈ ℝ^{r×q} : [I; Z]ᵀ Π [I; Z] ⩾ 0}` (p. 5). -/
def ZSet (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Set (Matrix κ ι ℝ) :=
  {Z | (qmiForm P Z).PosSemidef}

/-- `𝒵_r^+(Π) = {Z ∈ ℝ^{r×q} : [I; Z]ᵀ Π [I; Z] > 0}` (p. 6). -/
def ZPlus (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Set (Matrix κ ι ℝ) :=
  {Z | (qmiForm P Z).PosDef}

/-- `𝒵_r^0(Π) = {Z ∈ ℝ^{r×q} : [I; Z]ᵀ Π [I; Z] = 0}` (p. 6). -/
def ZZero (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Set (Matrix κ ι ℝ) :=
  {Z | qmiForm P Z = 0}

/-- The generalized Schur complement `Π | Π₂₂ = Π₁₁ − Π₁₂ Π₂₂† Π₂₁` (p. 6, after (3.2)). -/
noncomputable def schur (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Matrix ι ι ℝ :=
  P.toBlocks₁₁ - P.toBlocks₁₂ * pinv P.toBlocks₂₂ * P.toBlocks₂₁

/-- `Π ∈ 𝚷_{q,r}` ((3.5), p. 6): `Π ∈ 𝕊^{q+r}`, `Π₂₂ ⩽ 0`, `Π | Π₂₂ ⩾ 0` and
`ker Π₂₂ ⊆ ker Π₁₂`. -/
def InPi (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) : Prop :=
  P.IsHermitian ∧ (-P.toBlocks₂₂).PosSemidef ∧ (schur P).PosSemidef ∧
    ∀ v : κ → ℝ, P.toBlocks₂₂ *ᵥ v = 0 → P.toBlocks₁₂ *ᵥ v = 0

end QMI

end QuadMatIneq.Stabilization


