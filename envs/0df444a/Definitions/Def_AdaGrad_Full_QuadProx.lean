-- Prove2me | Definitions.Def_AdaGrad_Full_QuadProx
-- name    : AdaGrad_Full_QuadProx
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:57:01.649317+00:00
-- url     : https://prove2.me/theorems/c307e73d-d304-4eb9-a6e6-216bdabe72df
-- title:
--   Quadratic proximal functions, their Bregman divergences and dual norms, and the updates (3) and (4)
-- statement:
--   Online convex optimization over a closed convex set $\mathcal X\subseteq\mathbb R^d$ (with the Euclidean inner product $\langle\cdot,\cdot\rangle$). In round $t=1,2,\dots$ the learner plays $x_t$, receives a convex loss $f_t$ and observes a subgradient $g_t\in\partial f_t(x_t)$; $\varphi$ is a fixed convex regularizer. This file defines:
--
--   1. (the **regret** (2), $R_\phi(T)=\sum_{t=1}^T[f_t(x_t)+\varphi(x_t)-f_t(x^*)-\varphi(x^*)]$, is the shared definition `AdaGrad.Diag.regret`, imported here);
--   2. for a $d\times d$ matrix $H$, the bilinear form $\langle y,Hz\rangle$, the **quadratic proximal function** $\psi(y)=\tfrac12\langle y,Hy\rangle$ and its **Bregman divergence** $B_\psi(y,z)=\tfrac12\langle y-z,H(y-z)\rangle$;
--   3. the **pseudo-inverse** $A^\dagger$ of a symmetric matrix $A$ (invert the nonzero eigenvalues, keep the zero ones) and the **squared dual norm** $\|v\|_{\psi^*}^2=\langle v,H^\dagger v\rangle$;
--   4. $T$ rounds of the **primal-dual subgradient update (3)** with proximal functions $\psi_t(x)=\tfrac12\langle x,H_tx\rangle$: for $t=1,\dots,T$, $g_t\in\partial f_t(x_t)$ and
--   $$x_{t+1}\in\operatorname*{argmin}_{x\in\mathcal X}\Big\{\eta\Big\langle\tfrac1t\textstyle\sum_{\tau=1}^t g_\tau,x\Big\rangle+\eta\varphi(x)+\tfrac1t\psi_t(x)\Big\};$$
--   5. $T$ rounds of the **composite mirror descent update (4)**: for $t=1,\dots,T$, $g_t\in\partial f_t(x_t)$ and
--   $$x_{t+1}\in\operatorname*{argmin}_{x\in\mathcal X}\big\{\eta\langle g_t,x\rangle+\eta\varphi(x)+B_{\psi_t}(x,x_t)\big\}.$$
--
--   These are the objects every regret bound of the paper is stated in; the run predicates do not fix the matrices $H_t$, so they serve both the general Propositions 2 and 3 and full-matrix AdaGrad.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin d)`, so `‖·‖` is the Euclidean norm. Rounds are 1-based. The argmin is a predicate (`x (t+1) ∈ X` and `IsMinOn`), not a function: it need not be unique, and a run need not exist for every data. The pseudo-inverse is the continuous functional calculus applied to $\lambda\mapsto\lambda^{-1}$ with $0^{-1}=0$; Mathlib's matrix inverse (which is $0$ on singular matrices) is not used for it. $f_t$ and $\varphi$ are real-valued; the constraint is carried by $\mathcal X$. The subgradient relation is the published `ShorNonsmooth.AlmostDiff.IsSubgradient`.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2122 (notation, Bregman divergence), p. 2123, (2), (3), (4), p. 2135 (dual norm)

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient
import Definitions.Def_AdaGrad_Diag_Setup

namespace AdaGrad.Full

open ShorNonsmooth.AlmostDiff
open scoped InnerProductSpace

/-- The bilinear form `⟨y, M z⟩` of a real `d × d` matrix `M` on `ℝ^d` with its Euclidean inner
product (`M` acts on `ℝ^d` as the usual matrix–vector product). -/
noncomputable def mInner {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (y z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⟪y, Matrix.toEuclideanLin M z⟫_ℝ

/-- The quadratic proximal function `ψ(y) = ½ ⟨y, H y⟩` of a matrix `H` (Figure 2, p. 2134:
`ψ_t(x) = ½⟨x, H_t x⟩`). -/
noncomputable def psi {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2) * mInner H y y

/-- The Bregman divergence (p. 2122) of the quadratic proximal function `psi H` for a symmetric `H`:
`B_ψ(y, z) = ψ(y) − ψ(z) − ⟨∇ψ(z), y − z⟩ = ½ ⟨y − z, H (y − z)⟩`. -/
noncomputable def bregman {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (y z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2) * mInner H (y - z) (y - z)

/-- The (Moore–Penrose) pseudo-inverse `A†` of a symmetric matrix `A`, computed by the continuous
functional calculus applied to `λ ↦ λ⁻¹` (with Lean's `0⁻¹ = 0`): it inverts the nonzero
eigenvalues and keeps the zero ones. It is the ordinary inverse when `A` is invertible. (Mathlib's
`A⁻¹` is `0` for a singular `A` and is *not* used for possibly singular matrices.) For a
non-symmetric `A` the functional calculus returns `0`; it is only applied to symmetric matrices. -/
noncomputable def pinv {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  cfc (fun x : ℝ => x⁻¹) A

/-- The squared dual norm `‖v‖²_{ψ*} = ⟨v, H† v⟩` of the quadratic proximal function
`ψ(y) = ½⟨y, H y⟩` for a positive semidefinite `H` (p. 2135: `‖x‖²_{ψ*_t} = ⟨x, (δI + S_t)⁻¹ x⟩`).
It is the dual (semi)norm when `v` lies in the range of `H`; the theorems using it assume this. -/
noncomputable def dualNormSq {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  mInner (pinv H) v v

/-- `T` rounds of the **primal-dual subgradient update (3)** (p. 2123) with the quadratic proximal
functions `ψ_t = psi (H t)`: for every round `t = 1, …, T`, `g_t` is a subgradient of `f_t` at
`x_t`, and `x_{t+1} ∈ X` minimizes `η⟨(1/t) ∑_{τ=1}^t g_τ, y⟩ + ηϕ(y) + (1/t) ψ_t(y)` over `y ∈ X`.
The argmin is a predicate: it need not be unique, and the run need not exist for every data. -/
def IsQuadPrimalDualRun {d : ℕ} (η : ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T,
    IsSubgradient (f t) (x t) (g t) ∧ x (t + 1) ∈ X ∧
      IsMinOn (fun y => η * ⟪(1 / (t : ℝ)) • ∑ τ ∈ Finset.Icc 1 t, g τ, y⟫_ℝ + η * ϕ y
        + (1 / (t : ℝ)) * psi (H t) y) X (x (t + 1))

/-- `T` rounds of the **composite mirror descent update (4)** (p. 2123) with the quadratic proximal
functions `ψ_t = psi (H t)`: for every round `t = 1, …, T`, `g_t` is a subgradient of `f_t` at
`x_t`, and `x_{t+1} ∈ X` minimizes `η⟨g_t, y⟩ + ηϕ(y) + B_{ψ_t}(y, x_t)` over `y ∈ X`.
The argmin is a predicate: it need not be unique, and the run need not exist for every data. -/
def IsQuadMirrorDescentRun {d : ℕ} (η : ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (H : ℕ → Matrix (Fin d) (Fin d) ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 T,
    IsSubgradient (f t) (x t) (g t) ∧ x (t + 1) ∈ X ∧
      IsMinOn (fun y => η * ⟪g t, y⟫_ℝ + η * ϕ y + bregman (H t) y (x t)) X (x (t + 1))

end AdaGrad.Full


