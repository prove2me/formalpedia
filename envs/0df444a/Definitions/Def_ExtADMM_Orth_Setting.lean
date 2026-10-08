-- Prove2me | Definitions.Def_ExtADMM_Orth_Setting
-- name    : ExtADMM_Orth_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:27.136933+00:00
-- url     : https://prove2.me/theorems/2c4ef26c-6495-4ab7-9c5a-b984f44bb5e3
-- title:
--   (1.1), (1.6), (2.4)–(2.13) — the three-block problem and reordered ADMM setting
-- statement:
--   This definition file fixes the objects of §1 and §2.2 of the paper.
--
--   **The problem (1.1).** For $i=1,2,3$ let $\mathcal X_i\subseteq\mathbb R^{n_i}$, $A_i\in\mathbb R^{p\times n_i}$, $\theta_i:\mathbb R^{n_i}\to\mathbb R$, and $b\in\mathbb R^p$. The program is
--
--   $$\min\ \theta_1(x_1)+\theta_2(x_2)+\theta_3(x_3)\quad\text{s.t.}\quad A_1x_1+A_2x_2+A_3x_3=b,\ \ x_i\in\mathcal X_i .$$
--
--   The standing assumptions (p. 1) are: each $\mathcal X_i$ is closed and convex, each $\theta_i$ is convex, and the solution set of (1.1) is nonempty (some feasible point has objective value at most that of every feasible point).
--
--   **The augmented Lagrangian (1.6)** with penalty $\beta$ and residual $r(x)=A_1x_1+A_2x_2+A_3x_3-b$ is
--
--   $$\mathcal L_{\mathcal A}(x_1,x_2,x_3,\lambda)=\sum_{i=1}^3\theta_i(x_i)-\lambda^Tr(x)+\frac\beta2\|r(x)\|^2 .$$
--
--   **A run of the reordered scheme (2.4)** is a sequence $(x_1^k,x_2^k,x_3^k,\lambda^k)_{k\ge0}$ such that, for every $k$: $x_2^{k+1}$ minimises $\mathcal L_{\mathcal A}(x_1^k,\cdot,x_3^k,\lambda^k)$ over $\mathcal X_2$; $x_3^{k+1}$ minimises $\mathcal L_{\mathcal A}(x_1^k,x_2^{k+1},\cdot,\lambda^k)$ over $\mathcal X_3$; $\lambda^{k+1}=\lambda^k-\beta(A_1x_1^k+A_2x_2^{k+1}+A_3x_3^{k+1}-b)$; and $x_1^{k+1}$ minimises $\mathcal L_{\mathcal A}(\cdot,x_2^{k+1},x_3^{k+1},\lambda^{k+1})$ over $\mathcal X_1$.
--
--   **The variational inequality (2.5).** With $w=(x_1,x_2,x_3,\lambda)$, $\theta(u)=\sum_i\theta_i(x_i)$, $\Omega=\mathcal X_1\times\mathcal X_2\times\mathcal X_3\times\mathbb R^p$ and the affine map $F(w)=(-A_1^T\lambda,-A_2^T\lambda,-A_3^T\lambda,\,A_1x_1+A_2x_2+A_3x_3-b)$, the set $\Omega^*$ consists of the $w^*\in\Omega$ with $\theta(u)-\theta(u^*)+(w-w^*)^TF(w^*)\ge0$ for all $w\in\Omega$.
--
--   **Auxiliary objects.** $v=(x_1,x_3,\lambda)$; the matrices $Q$ of (2.9) and $H$ of (2.11),
--
--   $$Q=\begin{pmatrix}-\beta A_1^TA_1&0&A_1^T\\0&\beta A_2^TA_3&0\\0&0&0\\A_1&0&-\frac1\beta I\end{pmatrix},\qquad H=\begin{pmatrix}\beta A_1^TA_1&0&-A_1^T\\0&\beta A_3^TA_3&0\\-A_1&0&\frac1\beta I\end{pmatrix},$$
--
--   with $\|v\|_H^2=v^THv$; the vector $\beta PA_3d_3=\beta(A_1^TA_3d_3,A_2^TA_3d_3,A_3^TA_3d_3,0)$; the point $\tilde w^k=(x_1^{k+1},x_2^{k+1},x_3^{k+1},\lambda^{k+1}-\beta A_3(x_3^k-x_3^{k+1}))$ of (2.13); its average $\tilde w_t=\frac1{t+1}\sum_{k=0}^t\tilde w^k$ of (2.31); and full column rank of $[A_1,A_2]$, i.e. injectivity of $(u_1,u_2)\mapsto A_1u_1+A_2u_2$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Vectors are `Fin n → ℝ`; every Euclidean square $\|r\|^2$ is the dot product $r\cdot r$ (Mathlib's norm on `Fin n → ℝ` is the sup norm and is not used). $H$ is only positive semidefinite, so $\|\cdot\|_H^2$ is a seminorm square given by the expanded bilinear form, not a `Norm`. "Argmin" is read as "is a minimiser": the run predicate does not assume uniqueness or use a default-valued argmin. The paper's "closed convex" $\theta_i$ are real valued on all of $\mathbb R^{n_i}$, hence continuous, so "closed" adds nothing. The paper uses $\Omega$ and $\Omega^*$ without defining them; they are pinned here as the standard He–Yuan notation. The blocks $x_1,x_2,x_3$ are separate Lean fields; $x_2^0$ is never read by (2.4).
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 1–7, (1.1), (1.6), (2.4), (2.5), (2.9), (2.11), (2.13)

import Mathlib

set_option autoImplicit false

noncomputable section

namespace ExtADMM.Orth


/-- The three-block convex program (1.1), with real-valued objectives. -/
structure Problem (n1 n2 n3 p : ℕ) where
  A1 : Matrix (Fin p) (Fin n1) ℝ
  A2 : Matrix (Fin p) (Fin n2) ℝ
  A3 : Matrix (Fin p) (Fin n3) ℝ
  b : Fin p → ℝ
  θ1 : (Fin n1 → ℝ) → ℝ
  θ2 : (Fin n2 → ℝ) → ℝ
  θ3 : (Fin n3 → ℝ) → ℝ
  X1 : Set (Fin n1 → ℝ)
  X2 : Set (Fin n2 → ℝ)
  X3 : Set (Fin n3 → ℝ)

structure Pt (n1 n2 n3 p : ℕ) where
  x1 : Fin n1 → ℝ
  x2 : Fin n2 → ℝ
  x3 : Fin n3 → ℝ
  lam : Fin p → ℝ

instance {n1 n2 n3 p : ℕ} : Sub (Pt n1 n2 n3 p) where
  sub a b := ⟨a.x1 - b.x1, a.x2 - b.x2, a.x3 - b.x3, a.lam - b.lam⟩

instance {n1 n2 n3 p : ℕ} : Add (Pt n1 n2 n3 p) where
  add a b := ⟨a.x1 + b.x1, a.x2 + b.x2, a.x3 + b.x3, a.lam + b.lam⟩

instance {n1 n2 n3 p : ℕ} : Zero (Pt n1 n2 n3 p) where
  zero := ⟨0, 0, 0, 0⟩

/-- The essential variables v = (x₁,x₃,λ) of p. 4. -/
structure V (n1 n3 p : ℕ) where
  x1 : Fin n1 → ℝ
  x3 : Fin n3 → ℝ
  lam : Fin p → ℝ

instance {n1 n3 p : ℕ} : Sub (V n1 n3 p) where
  sub a b := ⟨a.x1 - b.x1, a.x3 - b.x3, a.lam - b.lam⟩

/-- The four-block Euclidean pairing in (2.5). -/
def pair {n1 n2 n3 p : ℕ} (d g : Pt n1 n2 n3 p) : ℝ :=
  dotProduct d.x1 g.x1 + dotProduct d.x2 g.x2 + dotProduct d.x3 g.x3 +
    dotProduct d.lam g.lam

namespace Problem

variable {n1 n2 n3 p : ℕ} (P : Problem n1 n2 n3 p)

def residual (x1 : Fin n1 → ℝ) (x2 : Fin n2 → ℝ) (x3 : Fin n3 → ℝ) : Fin p → ℝ :=
  P.A1.mulVec x1 + P.A2.mulVec x2 + P.A3.mulVec x3 - P.b

def objective (x1 : Fin n1 → ℝ) (x2 : Fin n2 → ℝ) (x3 : Fin n3 → ℝ) : ℝ :=
  P.θ1 x1 + P.θ2 x2 + P.θ3 x3

/-- The standing assumptions on p. 1, including existence of a primal solution. -/
def Standing : Prop :=
  Convex ℝ P.X1 ∧ IsClosed P.X1 ∧
  Convex ℝ P.X2 ∧ IsClosed P.X2 ∧
  Convex ℝ P.X3 ∧ IsClosed P.X3 ∧
  ConvexOn ℝ Set.univ P.θ1 ∧ ConvexOn ℝ Set.univ P.θ2 ∧
  ConvexOn ℝ Set.univ P.θ3 ∧
  ∃ x1 ∈ P.X1, ∃ x2 ∈ P.X2, ∃ x3 ∈ P.X3,
    P.residual x1 x2 x3 = 0 ∧
    ∀ y1 ∈ P.X1, ∀ y2 ∈ P.X2, ∀ y3 ∈ P.X3,
      P.residual y1 y2 y3 = 0 →
      P.objective x1 x2 x3 ≤ P.objective y1 y2 y3

/-- The augmented Lagrangian (1.6); the multiplier enters with a minus sign. -/
def augLag (β : ℝ) (x1 : Fin n1 → ℝ) (x2 : Fin n2 → ℝ)
    (x3 : Fin n3 → ℝ) (lam : Fin p → ℝ) : ℝ :=
  P.objective x1 x2 x3 - dotProduct lam (P.residual x1 x2 x3) +
    β / 2 * dotProduct (P.residual x1 x2 x3) (P.residual x1 x2 x3)

/-- A run of the reordered four-step scheme (2.4). The initial x₂⁰ is unused. -/
def IsRun24 (β : ℝ) (x1 : ℕ → Fin n1 → ℝ) (x2 : ℕ → Fin n2 → ℝ)
    (x3 : ℕ → Fin n3 → ℝ) (lam : ℕ → Fin p → ℝ) : Prop :=
  ∀ k : ℕ,
    (x2 (k + 1) ∈ P.X2 ∧
      ∀ y ∈ P.X2, P.augLag β (x1 k) (x2 (k + 1)) (x3 k) (lam k) ≤
        P.augLag β (x1 k) y (x3 k) (lam k)) ∧
    (x3 (k + 1) ∈ P.X3 ∧
      ∀ y ∈ P.X3, P.augLag β (x1 k) (x2 (k + 1)) (x3 (k + 1)) (lam k) ≤
        P.augLag β (x1 k) (x2 (k + 1)) y (lam k)) ∧
    lam (k + 1) = lam k - β • P.residual (x1 k) (x2 (k + 1)) (x3 (k + 1)) ∧
    (x1 (k + 1) ∈ P.X1 ∧
      ∀ y ∈ P.X1, P.augLag β (x1 (k + 1)) (x2 (k + 1)) (x3 (k + 1)) (lam (k + 1)) ≤
        P.augLag β y (x2 (k + 1)) (x3 (k + 1)) (lam (k + 1)))

/-- The paper's Ω, made explicit as the product of the three constraint sets and ℝᵖ. -/
def Omega : Set (Pt n1 n2 n3 p) :=
  {w | w.x1 ∈ P.X1 ∧ w.x2 ∈ P.X2 ∧ w.x3 ∈ P.X3}

def theta (w : Pt n1 n2 n3 p) : ℝ := P.objective w.x1 w.x2 w.x3

/-- The affine skew map F of (2.5c). -/
def F (w : Pt n1 n2 n3 p) : Pt n1 n2 n3 p :=
  ⟨-(P.A1.transpose.mulVec w.lam), -(P.A2.transpose.mulVec w.lam),
    -(P.A3.transpose.mulVec w.lam),
    P.residual w.x1 w.x2 w.x3⟩

/-- Ω* is the solution set of VI(Ω,F,θ), equation (2.5a). -/
def OmegaStar : Set (Pt n1 n2 n3 p) :=
  {ws | ws ∈ P.Omega ∧
    ∀ w ∈ P.Omega, 0 ≤ P.theta w - P.theta ws + pair (w - ws) (P.F ws)}

/-- vᵏ for a run, and the projection v* of a point of Ω*. -/
def v (_P : Problem n1 n2 n3 p) (x1 : ℕ → Fin n1 → ℝ) (x3 : ℕ → Fin n3 → ℝ)
    (lam : ℕ → Fin p → ℝ) (k : ℕ) : V n1 n3 p := ⟨x1 k, x3 k, lam k⟩

def vs (_P : Problem n1 n2 n3 p) (w : Pt n1 n2 n3 p) : V n1 n3 p :=
  ⟨w.x1, w.x3, w.lam⟩

/-- wᵏ for a run. -/
def w (_P : Problem n1 n2 n3 p) (x1 : ℕ → Fin n1 → ℝ) (x2 : ℕ → Fin n2 → ℝ)
    (x3 : ℕ → Fin n3 → ℝ) (lam : ℕ → Fin p → ℝ)
    (k : ℕ) : Pt n1 n2 n3 p := ⟨x1 k, x2 k, x3 k, lam k⟩

/-- H of (2.11), expanded blockwise: [βA₁ᵀA₁ 0 −A₁ᵀ; 0 βA₃ᵀA₃ 0; −A₁ 0 β⁻¹I]. -/
def Hform (β : ℝ) (a b : V n1 n3 p) : ℝ :=
  β * dotProduct (P.A1.mulVec a.x1) (P.A1.mulVec b.x1) -
    dotProduct (P.A1.mulVec a.x1) b.lam - dotProduct a.lam (P.A1.mulVec b.x1) +
    β⁻¹ * dotProduct a.lam b.lam +
    β * dotProduct (P.A3.mulVec a.x3) (P.A3.mulVec b.x3)

/-- The square of the paper's H seminorm. -/
def Hsq (β : ℝ) (a : V n1 n3 p) : ℝ := P.Hform β a a

/-- Q(vᵏ−vᵏ⁺¹), using the matrix Q of (2.9). -/
def Qmul (β : ℝ) (d : V n1 n3 p) : Pt n1 n2 n3 p :=
  ⟨-β • (P.A1.transpose.mulVec (P.A1.mulVec d.x1)) + P.A1.transpose.mulVec d.lam,
    β • (P.A2.transpose.mulVec (P.A3.mulVec d.x3)), 0,
    P.A1.mulVec d.x1 - β⁻¹ • d.lam⟩

/-- βPA₃d₃ of (2.10)–(2.11). -/
def PA3 (β : ℝ) (d3 : Fin n3 → ℝ) : Pt n1 n2 n3 p :=
  ⟨β • (P.A1.transpose.mulVec (P.A3.mulVec d3)),
    β • (P.A2.transpose.mulVec (P.A3.mulVec d3)),
    β • (P.A3.transpose.mulVec (P.A3.mulVec d3)), 0⟩

/-- The auxiliary point w̃ᵏ of (2.13). -/
def wtilde (β : ℝ) (x1 : ℕ → Fin n1 → ℝ) (x2 : ℕ → Fin n2 → ℝ)
    (x3 : ℕ → Fin n3 → ℝ) (lam : ℕ → Fin p → ℝ) (k : ℕ) : Pt n1 n2 n3 p :=
  ⟨x1 (k + 1), x2 (k + 1), x3 (k + 1),
    lam (k + 1) - β • (P.A3.mulVec (x3 k - x3 (k + 1)))⟩

/-- The ergodic average w̃_t of (2.31), with all four blocks averaged. -/
def wbar (β : ℝ) (x1 : ℕ → Fin n1 → ℝ) (x2 : ℕ → Fin n2 → ℝ)
    (x3 : ℕ → Fin n3 → ℝ) (lam : ℕ → Fin p → ℝ) (t : ℕ) : Pt n1 n2 n3 p :=
  ⟨(1 / ((t : ℝ) + 1)) • ∑ k ∈ Finset.range (t + 1), (P.wtilde β x1 x2 x3 lam k).x1,
   (1 / ((t : ℝ) + 1)) • ∑ k ∈ Finset.range (t + 1), (P.wtilde β x1 x2 x3 lam k).x2,
   (1 / ((t : ℝ) + 1)) • ∑ k ∈ Finset.range (t + 1), (P.wtilde β x1 x2 x3 lam k).x3,
   (1 / ((t : ℝ) + 1)) • ∑ k ∈ Finset.range (t + 1), (P.wtilde β x1 x2 x3 lam k).lam⟩

/-- Full column rank of the block matrix [A₁,A₂], expressed by its joint map. -/
def Blocks12Injective : Prop :=
  Function.Injective (fun z : (Fin n1 → ℝ) × (Fin n2 → ℝ) =>
    P.A1.mulVec z.1 + P.A2.mulVec z.2)

end Problem
end ExtADMM.Orth


