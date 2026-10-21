-- Prove2me | Definitions.Def_YeIPA_Center_AnalyticCenter
-- name    : YeIPA_Center_AnalyticCenter
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:20.742131+00:00
-- url     : https://prove2.me/theorems/af16ed14-a9f3-4d05-b3e6-640316808fa0
-- title:
--   The polytope $\Omega$, its analytic center, the potentials $\mathcal B,\mathcal P,\psi_n$, the proximity measures $\eta_d,\eta_p,\eta$ and the Newton steps
-- statement:
--   Fix a real $m\times n$ matrix $A$ and $c\in\mathbb R^n$. Vector inequalities are componentwise, $e$ is the all-ones vector, and for a vector $x$ we write $X=\operatorname{diag}(x)$ (likewise $S=\operatorname{diag}(s)$). $\|\cdot\|$ is the Euclidean norm and $\|v\|_\infty=\max_j|v_j|$. This module defines the objects of Chapter 3 of Ye's *Interior Point Algorithms*:
--
--   1. The **slack** $s=c-A^Ty$ of $y\in\mathbb R^m$, and the polytope $\Omega=\{y: c-A^Ty\ge0\}$. The **standing assumptions** of the chapter are: $A$ has rank $m$, $n>m$, and $\Omega$ is bounded with nonempty interior.
--   2. An **interior point** $(y,s)$ of $\Omega$: $s=c-A^Ty$ and $s>0$. An **interior point of** $\mathcal X_\Omega=\{x: Ax=0,\ x\ge0\}$: $Ax=0$ and $x>0$.
--   3. The **potentials**
--   $$\mathcal B(y)=\sum_{j=1}^n\log s_j,\qquad \mathcal P(x)=n\log(c^Tx)-\sum_{j=1}^n\log x_j,\qquad \psi_n(x,s)=n\log(x^Ts)-\sum_{j=1}^n\log(x_js_j).$$
--   4. The **analytic center** $(y^a,s^a)$: an interior point of $\Omega$ maximizing $\mathcal B$ over all interior points of $\Omega$. The **primal potential minimizer with $c^Tx^a=n$**: an interior point $x^a$ of $\mathcal X_\Omega$ with $c^Tx^a=n$ minimizing $\mathcal P$ over all interior points of $\mathcal X_\Omega$.
--   5. The **proximity measures**
--   $$\eta_d(s)=\|p(s)\|,\quad p(s)=-S^{-1}A^T(AS^{-2}A^T)^{-1}AS^{-1}e;\qquad \eta_p(x)=\|p(x)\|,\quad p(x)=(I-XA^T(AX^2A^T)^{-1}AX)(Xc-e);\qquad \eta(x,s)=\|Xs-e\|.$$
--   6. The **dual Newton step** $s^+=s+d_s$ with $d_s=A^T(AS^{-2}A^T)^{-1}AS^{-1}e$, and the **primal Newton step** $x^+=x+d_x$ with $d_x=-X(I-XA^T(AX^2A^T)^{-1}AX)(Xc-e)$.
--   7. The **primal-dual Newton system** at $(x,s)$: directions $(d_x,d_y,d_s)$ with
--   $$Sd_x+Xd_s=e-Xs,\qquad Ad_x=0,\qquad -A^Td_y-d_s=0.$$
--   8. With $\min(v)=\min_jv_j$, the quantity $\|(XS)^{-1/2}(e-Xs)\|$ and, for a constant $\alpha$, the **step size**
--   $$\theta=\frac{\alpha\sqrt{\min(Xs)}}{\|(XS)^{-1/2}(e-Xs)\|}.$$
--
--   **Formalization Note** Vectors are functions `Fin n → ℝ`, so indices $1,\dots,n$ become $0,\dots,n-1$; matrices are `Matrix (Fin m) (Fin n) ℝ`. The Euclidean norm is written out as `norm2` because Mathlib's norm on `Fin n → ℝ` is the sup norm; $\|\cdot\|_\infty$ is `normInf`, with value $0$ when $n=0$. The potential $\mathcal B$ is written as a function of the slack vector $s$. Matrix inverses are Mathlib's `⁻¹`, which equals $0$ for a singular matrix; under the standing assumptions every matrix inverted here is positive definite at the points where the theorems evaluate it. The analytic center and the primal minimizer are defined by their extremal property (pp. 49, 61), not by the optimality conditions. The standing assumptions are bundled as `StandingAssumptions A c` and are a hypothesis of every theorem; no definition assumes them.
-- source:
--   Ye, Interior Point Algorithms: Theory and Analysis, Wiley 1997, p. 48 (standing assumptions), p. 49 ((2.1), analytic center), p. 59 (X_Ω, (2.8)), p. 61 (primal analytic center), p. 81 (Ω, S_Ω), pp. 82–83 ((3.1)–(3.7)), p. 88 ((3.9)), p. 95 ((3.13)), p. 102 ((3.15)), p. 104 ((3.17))

import Mathlib

open Matrix

namespace YeIPA.Center

/-!
# The analytic center of `Ω = {y : c − Aᵀy ≥ 0}`, its proximity measures and Newton steps

Ye, *Interior Point Algorithms: Theory and Analysis*, Wiley 1997: Ω, `S_Ω` p. 81; the potential
`B` (2.1) and the analytic center p. 49; `X_Ω` and the primal potential `P` (2.8) p. 59; the
primal analytic center p. 61; the proximity measures (3.1)–(3.7) pp. 82–83; the dual Newton
step (3.9) p. 88; the primal Newton step (3.13) p. 95; the primal-dual Newton system (3.15)
p. 102; the step size (3.17) p. 104.

`A : Matrix (Fin m) (Fin n) ℝ`, `c : Fin n → ℝ`. The book's indices `1, …, n` are `0, …, n-1`
here. Vector inequalities are componentwise; `e` is the all-ones vector; `X = diag(x)`,
`S = diag(s)`.
-/

variable {m n : ℕ}

/-- The all-ones vector `e ∈ ℝⁿ`. -/
def ones (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- The Euclidean norm `‖v‖ = (∑ⱼ vⱼ²)^{1/2}`. -/
noncomputable def norm2 (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ j, v j ^ 2)

/-- The max-norm `‖v‖_∞ = maxⱼ |vⱼ|` (equal to `0` when `n = 0`). -/
noncomputable def normInf (v : Fin n → ℝ) : ℝ := ⨆ j, |v j|

/-- `min(v) = minⱼ vⱼ` (p. 104; used with `n ≥ 1`). -/
noncomputable def vmin (v : Fin n → ℝ) : ℝ := ⨅ j, v j

/-- The slack vector `s = c − Aᵀy` (p. 49). -/
def slack (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ) : Fin n → ℝ :=
  c - Aᵀ *ᵥ y

/-- The standing assumptions of Chapters 2–3 (p. 48, p. 81): `A` has rank `m`, `n > m`, and
`Ω = {y ∈ ℝᵐ : c − Aᵀy ≥ 0}` is bounded and has a nonempty interior. -/
def StandingAssumptions (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) : Prop :=
  A.rank = m ∧ m < n ∧ Bornology.IsBounded {y : Fin m → ℝ | ∀ j, 0 ≤ slack A c y j} ∧
    ∃ y : Fin m → ℝ, ∀ j, 0 < slack A c y j

/-- `(y, s)` is an interior point of `Ω` (or `S_Ω`): `s = c − Aᵀy` and `s > 0`. -/
def IsDualInterior (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (y : Fin m → ℝ)
    (s : Fin n → ℝ) : Prop :=
  s = slack A c y ∧ ∀ j, 0 < s j

/-- `x` is an interior point of `X_Ω = {x ∈ ℝⁿ : Ax = 0, x ≥ 0}` (p. 59): `Ax = 0` and `x > 0`. -/
def IsPrimalInterior (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) : Prop :=
  A *ᵥ x = 0 ∧ ∀ j, 0 < x j

/-- The dual potential function `B(y) = ∑ⱼ log sⱼ`, `s = c − Aᵀy` (2.1), written on the slack. -/
noncomputable def dualPotential (s : Fin n → ℝ) : ℝ := ∑ j, Real.log (s j)

/-- The primal potential function `P(x) = n log(cᵀx) − ∑ⱼ log xⱼ` (2.8), p. 82. -/
noncomputable def primalPotential (c : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  (n : ℝ) * Real.log (c ⬝ᵥ x) - ∑ j, Real.log (x j)

/-- The primal-dual potential function `ψ_n(x, s) = n log(xᵀs) − ∑ⱼ log(xⱼ sⱼ)`, p. 83. -/
noncomputable def pdPotential (x s : Fin n → ℝ) : ℝ :=
  (n : ℝ) * Real.log (x ⬝ᵥ s) - ∑ j, Real.log (x j * s j)

/-- `(yᵃ, sᵃ)` is the analytic center of `Ω` (p. 49): an interior point of `Ω` that maximizes
`B` over the interior points of `Ω`. -/
def IsAnalyticCenter (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (ya : Fin m → ℝ)
    (sa : Fin n → ℝ) : Prop :=
  IsDualInterior A c ya sa ∧
    ∀ y s, IsDualInterior A c y s → dualPotential s ≤ dualPotential sa

/-- `xᵃ` is the primal potential minimizer with `cᵀxᵃ = n` (pp. 61, 84): an interior point of
`X_Ω` with `cᵀxᵃ = n` that minimizes `P` over all interior points of `X_Ω`. -/
def IsPrimalPotentialMinimizer (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (xa : Fin n → ℝ) : Prop :=
  IsPrimalInterior A xa ∧ c ⬝ᵥ xa = n ∧
    ∀ x, IsPrimalInterior A x → primalPotential c xa ≤ primalPotential c x

/-- `S⁻¹ = diag(1/s₁, …, 1/sₙ)`. -/
noncomputable def diagInv (s : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun j => (s j)⁻¹)

/-- The dual proximity vector (3.2): `p(s) = −S⁻¹Aᵀ(AS⁻²Aᵀ)⁻¹AS⁻¹e`. -/
noncomputable def dualProxVec (A : Matrix (Fin m) (Fin n) ℝ) (s : Fin n → ℝ) : Fin n → ℝ :=
  -((diagInv s * Aᵀ * (A * diagInv s * diagInv s * Aᵀ)⁻¹ * A * diagInv s) *ᵥ ones n)

/-- The dual proximity measure (3.1): `η_d(s) = ‖p(s)‖`. -/
noncomputable def etaD (A : Matrix (Fin m) (Fin n) ℝ) (s : Fin n → ℝ) : ℝ :=
  norm2 (dualProxVec A s)

/-- The primal proximity vector (3.4): `p(x) = (I − XAᵀ(AX²Aᵀ)⁻¹AX)(Xc − e)`. -/
noncomputable def primalProxVec (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  (1 - diagonal x * Aᵀ * (A * diagonal x * diagonal x * Aᵀ)⁻¹ * A * diagonal x) *ᵥ
    (diagonal x *ᵥ c - ones n)

/-- The primal proximity measure (3.5): `η_p(x) = ‖p(x)‖`. -/
noncomputable def etaP (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  norm2 (primalProxVec A c x)

/-- The primal-dual proximity measure (3.7): `η(x, s) = ‖Xs − e‖`. -/
noncomputable def eta (x s : Fin n → ℝ) : ℝ :=
  norm2 (fun j => x j * s j - 1)

/-- The dual Newton direction (3.9): `d_s = Aᵀ(AS⁻²Aᵀ)⁻¹AS⁻¹e`. -/
noncomputable def dualNewtonDir (A : Matrix (Fin m) (Fin n) ℝ) (s : Fin n → ℝ) : Fin n → ℝ :=
  (Aᵀ * (A * diagInv s * diagInv s * Aᵀ)⁻¹ * A * diagInv s) *ᵥ ones n

/-- The dual Newton update (p. 88): `s⁺ = s + d_s`. -/
noncomputable def dualNewtonStep (A : Matrix (Fin m) (Fin n) ℝ) (s : Fin n → ℝ) : Fin n → ℝ :=
  s + dualNewtonDir A s

/-- The primal Newton direction (3.13): `d_x = −X(I − XAᵀ(AX²Aᵀ)⁻¹AX)(Xc − e)`. -/
noncomputable def primalNewtonDir (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  -((diagonal x * (1 - diagonal x * Aᵀ * (A * diagonal x * diagonal x * Aᵀ)⁻¹ * A *
      diagonal x)) *ᵥ (diagonal x *ᵥ c - ones n))

/-- The primal Newton update (p. 95): `x⁺ = x + d_x`. -/
noncomputable def primalNewtonStep (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  x + primalNewtonDir A c x

/-- `(d_x, d_y, d_s)` solves the primal-dual Newton system (3.15) at `(x, s)`:
`S d_x + X d_s = e − Xs`, `A d_x = 0`, `−Aᵀd_y − d_s = 0`. -/
def IsPDNewtonDir (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ) (dx : Fin n → ℝ)
    (dy : Fin m → ℝ) (ds : Fin n → ℝ) : Prop :=
  (∀ j, s j * dx j + x j * ds j = 1 - x j * s j) ∧ A *ᵥ dx = 0 ∧ -(Aᵀ *ᵥ dy) - ds = 0

/-- `‖(XS)^{-1/2}(e − Xs)‖`, the norm in (3.17). -/
noncomputable def scaledResidual (x s : Fin n → ℝ) : ℝ :=
  norm2 (fun j => (1 - x j * s j) / Real.sqrt (x j * s j))

/-- The step size (3.17): `θ = α √min(Xs) / ‖(XS)^{-1/2}(e − Xs)‖`. -/
noncomputable def pdStepSize (α : ℝ) (x s : Fin n → ℝ) : ℝ :=
  α * Real.sqrt (vmin (fun j => x j * s j)) / scaledResidual x s

end YeIPA.Center


