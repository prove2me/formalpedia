-- Prove2me | Definitions.Def_RobinsonSR_NLP_Setting
-- name    : RobinsonSR_NLP_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:32.117387+00:00
-- url     : https://prove2.me/theorems/d36ceacf-bf0b-4e8b-a069-4e2157a69d4c
-- title:
--   DEFINITION p. 45 and (4.1)–(4.6), pp. 53–55 — normal cone, strong regularity, the KKT generalized equation (4.3) and the matrices (4.5)–(4.6)
-- statement:
--   This file fixes the objects of §4 of Robinson's paper.
--
--   **Normal cone.** For a subset $C$ of a real inner-product space $E$ and a point $x\in E$, the normal-cone operator is
--   $$\partial\psi_C(x)=\begin{cases}\{y\in E:\ \langle y,c-x\rangle\le 0\ \text{for all } c\in C\}, & x\in C,\\ \emptyset, & x\notin C.\end{cases}$$
--
--   **Strong regularity.** Let $a\in E$, let $A:E\to E$ be a continuous linear map, let $z_0\in E$ and $\lambda\in\mathbb R$, and write $T(z)=a+A(z-z_0)+\partial\psi_C(z)$. The data $(C,a,A,z_0)$ are *strongly regular with Lipschitz constant* $\lambda$ if there are neighbourhoods $U$ of $0$ and $V$ of $z_0$ and a map $s$ such that, for every $y\in U$:
--   1. $s(y)\in V$ and $y\in T(s(y))$;
--   2. $s(y)$ is the only $z\in V$ with $y\in T(z)$;
--
--   and $\|s(y_1)-s(y_2)\|\le\lambda\|y_1-y_2\|$ for all $y_1,y_2\in U$. A generalized equation $0\in F(z)+\partial\psi_C(z)$ is *strongly regular at* $z_0$ if $F$ is Fréchet differentiable at $z_0$ with derivative $F'(z_0)$ and the data $(C,F(z_0),F'(z_0),z_0)$ are strongly regular with some constant $\lambda$.
--
--   **The nonlinear program.** For $\theta:\mathbb R^n\to\mathbb R$, $g:\mathbb R^n\to\mathbb R^p$, $h:\mathbb R^n\to\mathbb R^q$, the gradient of the Lagrangian $\mathcal L(x,u,v)=\theta(x)+\langle u,g(x)\rangle+\langle v,h(x)\rangle$ in $x$ is
--   $$\mathcal L'(x,u,v)=\nabla\theta(x)+\sum_{i=1}^p u_i\nabla g_i(x)+\sum_{j=1}^q v_j\nabla h_j(x),$$
--   and $\mathcal L''=\mathcal L''(x_0,u_0,v_0)$ is the derivative at $x_0$ of $x\mapsto\mathcal L'(x,u_0,v_0)$. Triples $z=(x,u,v)$ live in $\mathbb R^{n}\times\mathbb R^p\times\mathbb R^q=\mathbb R^{n+p+q}$ with the Euclidean inner product. The KKT generalized equation (4.3) is
--   $$0\in F(x,u,v)+\partial\psi_{\mathbb R^n\times\mathbb R^p_+\times\mathbb R^q}(x,u,v),\qquad F(x,u,v)=\big(\mathcal L'(x,u,v),\,-g(x),\,-h(x)\big).$$
--
--   **Matrices.** For matrices $Q$ ($n\times n$), $H$ ($q\times n$), $G^+$ ($r\times n$), $G^0$ ($s\times n$), the matrix (4.5) and its Schur complement (4.6) are
--   $$K=\begin{bmatrix}Q&H^{T}&G^{+T}\\-H&0&0\\-G^{+}&0&0\end{bmatrix},\qquad S=\begin{bmatrix}G^0&0&0\end{bmatrix}K^{-1}\begin{bmatrix}G^{0T}\\0\\0\end{bmatrix}.$$
--   A square matrix $M$ is a *P-matrix* if every principal minor $\det M_{JJ}$, $J\ne\emptyset$, is positive, and *positive definite* if $\langle w,Mw\rangle>0$ for every $w\ne0$ (no symmetry required). At a point $(x_0,u_0,v_0)$ the data matrices are: $Q$, the matrix of $\mathcal L''$ in the standard basis; $H$, with rows $\nabla h_j(x_0)$; $G^+$, with rows $\nabla g_i(x_0)$ for $u_{0,i}>0$; $G^0$, with rows $\nabla g_i(x_0)$ for $g_i(x_0)=0=u_{0,i}$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The dual space is identified with the space through the inner product, as the paper does from §3 on. The normal cone carries the clause $x\in C$, so it is empty off $C$. The Lipschitz constant $\lambda$ is a real number, not an `NNReal`, and strong regularity at $z_0$ bundles the derivative as a `HasFDerivAt` witness. $\mathcal L''$ is Mathlib's `fderiv`; the theorems that use it carry the differentiability hypotheses that make it the true derivative. Mathlib's matrix inverse of a singular matrix is $0$, so $S$ is meaningful only when $K$ is nonsingular; every statement using $S$ assumes or concludes that.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 43 (normal-cone operator), p. 45 (DEFINITION), pp. 53–55, (4.1), (4.3), (4.5), (4.6); P-matrix p. 52

import Mathlib
import Definitions.Def_RobinsonSR_Reduction_Setting
import Definitions.Def_RobinsonSR_Schur_Setting

namespace RobinsonSR.NLP

open scoped Topology RealInnerProductSpace Matrix

/-! ### Generalized equations on a real inner-product space -/

/-- Strong regularity (DEFINITION, p. 45), stated on the data of the linearisation: `a` plays
`f(z₀)` and `A` plays `f′(z₀)`, so that `T z = a + A (z - z₀) + ∂ψ_C(z)`. The generalized equation
`0 ∈ f(z) + ∂ψ_C(z)` is strongly regular at `z₀` with associated Lipschitz constant `lam` if there
are neighbourhoods `U` of `0` and `V` of `z₀` such that the restriction to `U` of `T⁻¹ ∩ V` is a
single-valued function `s : U → V`, Lipschitzian on `U` with modulus `lam`: for every `y ∈ U`,
`s y ∈ V` solves `y ∈ T (s y)`, it is the only solution of `y ∈ T z` with `z ∈ V`, and
`‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖` for `y₁, y₂ ∈ U`. -/
def StronglyRegular {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : Set E) (a : E) (A : E →L[ℝ] E) (z0 : E) (lam : ℝ) : Prop :=
  ∃ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 z0, ∃ s : E → E,
    (∀ y ∈ U, s y ∈ V ∧ y - (a + A (s y - z0)) ∈ RobinsonSR.Reduction.normalCone C (s y) ∧
       ∀ z ∈ V, y - (a + A (z - z0)) ∈ RobinsonSR.Reduction.normalCone C z → z = s y) ∧
    ∀ y₁ ∈ U, ∀ y₂ ∈ U, ‖s y₁ - s y₂‖ ≤ lam * ‖y₁ - y₂‖

/-- The generalized equation `0 ∈ F(z) + ∂ψ_C(z)` is strongly regular at `z₀` (DEFINITION, p. 45):
`F` is Fréchet differentiable at `z₀`, with derivative `DF`, and the linearisation
`F(z₀) + DF (z - z₀) + ∂ψ_C(z)` is strongly regular at `z₀` for some Lipschitz constant `lam`. -/
def StronglyRegularAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → E) (C : Set E) (z0 : E) : Prop :=
  ∃ DF : E →L[ℝ] E, HasFDerivAt F DF z0 ∧ ∃ lam : ℝ, StronglyRegular C (F z0) DF z0 lam

/-! ### The nonlinear program (4.1) and its KKT generalized equation (4.3) -/

/-- The gradient of the Lagrangian `ℒ(x, u, v) = θ(x) + ⟨u, g(x)⟩ + ⟨v, h(x)⟩` in `x` (p. 54):
`ℒ′(x, u, v) = ∇θ(x) + ∑ᵢ uᵢ ∇gᵢ(x) + ∑ⱼ vⱼ ∇hⱼ(x)`. -/
noncomputable def lagGrad {n p q : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (x : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin p)) (v : EuclideanSpace ℝ (Fin q)) :
    EuclideanSpace ℝ (Fin n) :=
  gradient θ x + ∑ i, u i • gradient (fun y => g y i) x + ∑ j, v j • gradient (fun y => h y j) x

/-- The Hessian of the Lagrangian in `x` at `(x₀, u₀, v₀)`, `ℒ″ = ℒ″(x₀, u₀, v₀)` (p. 54): the
Fréchet derivative at `x₀` of `x ↦ ℒ′(x, u₀, v₀)`. -/
noncomputable def lagHess {n p q : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (x0 : EuclideanSpace ℝ (Fin n)) (u0 : EuclideanSpace ℝ (Fin p)) (v0 : EuclideanSpace ℝ (Fin q)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  fderiv ℝ (fun x => lagGrad θ g h x u0 v0) x0

/-- The space `ℝⁿ × ℝᵖ × ℝ^q` of triples `z = (x, u, v)`, with the Euclidean norm and inner product
of `ℝ^{n+p+q}`. -/
abbrev KKTSpace (n p q : ℕ) : Type := EuclideanSpace ℝ (Fin n ⊕ (Fin p ⊕ Fin q))

/-- The `x`-component of `z = (x, u, v)`. -/
def xPart {n p q : ℕ} (z : KKTSpace n p q) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => z (Sum.inl i))

/-- The `u`-component of `z = (x, u, v)`. -/
def uPart {n p q : ℕ} (z : KKTSpace n p q) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 (fun i => z (Sum.inr (Sum.inl i)))

/-- The `v`-component of `z = (x, u, v)`. -/
def vPart {n p q : ℕ} (z : KKTSpace n p q) : EuclideanSpace ℝ (Fin q) :=
  WithLp.toLp 2 (fun j => z (Sum.inr (Sum.inr j)))

/-- The triple `(x, u, v)` as a point of `ℝⁿ × ℝᵖ × ℝ^q`. -/
def mk {n p q : ℕ} (x : EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin p))
    (v : EuclideanSpace ℝ (Fin q)) : KKTSpace n p q :=
  WithLp.toLp 2 (Sum.elim (fun i => x i) (Sum.elim (fun i => u i) (fun j => v j)))

/-- The single-valued part of the generalized equation (4.3):
`F(x, u, v) = (ℒ′(x, u, v), −g(x), −h(x))`. -/
noncomputable def kktMap {n p q : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q)) :
    KKTSpace n p q → KKTSpace n p q :=
  fun z => mk (lagGrad θ g h (xPart z) (uPart z) (vPart z)) (-g (xPart z)) (-h (xPart z))

/-- The set `ℝⁿ × ℝᵖ₊ × ℝ^q` of (4.3): triples whose `u`-component is componentwise nonnegative. -/
def kktCone (n p q : ℕ) : Set (KKTSpace n p q) :=
  {z | ∀ i, 0 ≤ uPart z i}

/-! ### Matrices of §3–§4 -/

/-- `M` is a P-matrix (p. 52): every principal minor of `M` is positive, i.e. for every nonempty
index set `J` the principal submatrix `M[J, J]` has positive determinant. -/
def IsPMatrix {ι : Type*} [DecidableEq ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ J : Finset ι, J.Nonempty →
    0 < (M.submatrix (fun i : J => (i : ι)) (fun i : J => (i : ι))).det

/-- The matrix (4.5),
`[ℒ″ Hᵀ G⁺ᵀ; −H 0 0; −G⁺ 0 0]`, with `Q` playing `ℒ″`, `H` the `q × n` and `Gp` the `r × n` matrix. -/
def kktMatrix {ιn ιq ιr : Type*} (Q : Matrix ιn ιn ℝ) (H : Matrix ιq ιn ℝ) (Gp : Matrix ιr ιn ℝ) :
    Matrix (ιn ⊕ (ιq ⊕ ιr)) (ιn ⊕ (ιq ⊕ ιr)) ℝ :=
  Matrix.fromBlocks Q (Matrix.fromCols Hᵀ Gpᵀ) (Matrix.fromRows (-H) (-Gp)) 0

/-- The row block `[G⁰ 0 0]` of (4.6). -/
def zeroRowBlock {ιn ιq ιr ιs : Type*} (G0 : Matrix ιs ιn ℝ) :
    Matrix ιs (ιn ⊕ (ιq ⊕ ιr)) ℝ :=
  Matrix.fromCols G0 0

/-- The Schur complement (4.6): `S = [G⁰ 0 0] (4.5)⁻¹ [G⁰ 0 0]ᵀ`. It is meaningful only when the
matrix (4.5) is nonsingular (Mathlib's `⁻¹` of a singular matrix is `0`). -/
noncomputable def schurS {ιn ιq ιr ιs : Type*} [Fintype ιn] [Fintype ιq] [Fintype ιr]
    [DecidableEq ιn] [DecidableEq ιq] [DecidableEq ιr]
    (Q : Matrix ιn ιn ℝ) (H : Matrix ιq ιn ℝ) (Gp : Matrix ιr ιn ℝ) (G0 : Matrix ιs ιn ℝ) :
    Matrix ιs ιs ℝ :=
  zeroRowBlock (ιq := ιq) (ιr := ιr) G0 * (kktMatrix Q H Gp)⁻¹ *
    (zeroRowBlock (ιq := ιq) (ιr := ιr) G0)ᵀ

/-- The matrix of `ℒ″` in the standard basis: entry `(i, j)` is the `i`-th coordinate of
`ℒ″ eⱼ`, so that `hessMatrix … *ᵥ y = ℒ″ y`. -/
noncomputable def hessMatrix {n p q : ℕ} (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (x0 : EuclideanSpace ℝ (Fin n)) (u0 : EuclideanSpace ℝ (Fin p)) (v0 : EuclideanSpace ℝ (Fin q)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => lagHess θ g h x0 u0 v0 (EuclideanSpace.single j 1) i

/-- The Jacobian `H = h′(x₀)`: the `q × n` matrix whose `j`-th row is `∇hⱼ(x₀)`. -/
noncomputable def eqJacobian {n q : ℕ} (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (x0 : EuclideanSpace ℝ (Fin n)) : Matrix (Fin q) (Fin n) ℝ :=
  Matrix.of fun j k => gradient (fun x => h x j) x0 k

/-- The Jacobian of the inequality constraints with index in `{i | P i}`: the matrix whose row `i`
is `∇gᵢ(x₀)`. With `P i := 0 < u₀ᵢ` it is `G⁺`, with `P i := gᵢ(x₀) = 0 ∧ u₀ᵢ = 0` it is `G⁰`. -/
noncomputable def ineqJacobian {n p : ℕ} (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (x0 : EuclideanSpace ℝ (Fin n)) (P : Fin p → Prop) : Matrix {i // P i} (Fin n) ℝ :=
  Matrix.of fun i k => gradient (fun x => g x i) x0 k

end RobinsonSR.NLP


