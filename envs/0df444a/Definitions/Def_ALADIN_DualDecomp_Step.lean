-- Prove2me | Definitions.Def_ALADIN_DualDecomp_Step
-- name    : ALADIN_DualDecomp_Step
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:46:48.775933+00:00
-- url     : https://prove2.me/theorems/f25d0fc8-c757-495f-ba18-609113d401cc
-- title:
--   Algorithm 2 steps 3–5 (C*ᵢ, gᵢ, the KKT system of QP (3.3), λ⁺), the dual gradient (A.3), M from (A.6) and the dual Newton step (A.4)
-- statement:
--   Let $(f,h,A,b)$ be an instance of problem (1.1), $\lambda\in\mathbb R^m$ the current dual iterate, and $(y_i,\kappa_i)$ the step-1 outputs.
--
--   1. **Active-constraint Jacobian** (step 3): $C^*_i\in\mathbb R^{n_h\times n}$ has $j$-th row $\nabla (h_i)_j(y_i)^\top$ if $(h_i(y_i))_j = 0$ and the zero row otherwise.
--   2. **Modified gradient** (step 3): for a Jacobian approximation $C_i\in\mathbb R^{n_h\times n}$, $g_i = \nabla f_i(y_i) + (C^*_i - C_i)^\top\kappa_i$.
--   3. **KKT system of the coupled QP** (3.3) (step 4). For Hessian approximations $H_i\in\mathbb R^{n\times n}$ and $\mu > 0$, the QP is
--   $$\min_{\Delta y, s}\ \sum_{i=1}^N\Big\{\tfrac12\Delta y_i^\top H_i\Delta y_i + g_i^\top\Delta y_i\Big\} + \lambda^\top s + \frac{\mu}{2}\|s\|_2^2\quad\text{s.t.}\quad \sum_{i=1}^N A_i(y_i+\Delta y_i) = b + s\ \mid\ \lambda_{\mathrm{QP}},\qquad C_i\Delta y_i = 0\ \mid\ \nu_i.$$
--   A quadruple $(\Delta y, s, \lambda_{\mathrm{QP}}, \nu)$ **solves its KKT system** if
--   $$H_i\Delta y_i + g_i + A_i^\top\lambda_{\mathrm{QP}} + C_i^\top\nu_i = 0\ \ (\forall i),\qquad \lambda + \mu s - \lambda_{\mathrm{QP}} = 0,$$
--   $$\sum_{i=1}^N A_i(y_i+\Delta y_i) = b + s,\qquad C_i\Delta y_i = 0\ \ (\forall i).$$
--   The sign of $\lambda_{\mathrm{QP}}$ is that of footnote 4 (p. 1110), whose $s$-stationarity reads $\lambda + \mu s - \lambda^+ = 0$, and of the Lagrangian in the proof of Lemma 5.
--   4. **Dual update** (step 5): $\lambda^+ = \lambda + \alpha_3(\lambda_{\mathrm{QP}} - \lambda)$.
--   5. **Dual gradient formula** (A.3): $\nabla V(\lambda) = \sum_{i=1}^N A_i y_i - b$.
--   6. **Scaling matrix** (A.6), corrected:
--   $$M = -\sum_{i=1}^N A_i\Big[H_i^{-1} - H_i^{-1}C_i^\top\big[C_iH_i^{-1}C_i^\top\big]^{-1}C_iH_i^{-1}\Big]A_i^\top.$$
--   7. **Dual Newton step** (A.4): $\lambda^+_{\mathrm{DD}} = \lambda - \alpha\big(M - \tfrac1\mu I\big)^{-1}\nabla V(\lambda)$.
--
--   These are the two sides of Lemma 5 and the intermediate objects of its proof.
--
--   **Formalization Note** (A.6) as printed has $[C_iH_iC_i^\top]^\dagger$; this is a typo for $[C_iH_i^{-1}C_i^\top]^\dagger$, cf. (A.5) on the same page (with this bracket Lemma 5 holds; with the printed one it fails, e.g. for $N=1$, $H_1=\mathrm{diag}(1,2)$, $C_1=(1,1)$, $A_1=I$). When $C_i$ has full row rank and $H_i\succ 0$ the bracket is invertible, so the pseudo-inverse is the matrix inverse, written `⁻¹`. $\nabla V(\lambda)$ is defined by the formula (A.3), not as a derivative of the dual function $V$; that (A.3) is the gradient of $V$ is a cited fact the lemma does not use. The QP (3.3) enters only through its KKT system; since it is a convex QP with linear constraints when $H_i\succ 0$ and $\mu>0$, these conditions are necessary and sufficient for optimality. Mathlib's `⁻¹` returns $0$ on a singular matrix, so every statement using an inverse also asserts or assumes invertibility.
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), p. 1108, Algorithm 2 steps 3–5, (3.3); p. 1110, footnote 4; pp. 1122–1123, (A.3), (A.4), (A.6)

import Mathlib
import Definitions.Def_ALADIN_DualDecomp_Problem

namespace ALADIN.DualDecomp

open Matrix

variable {N n m nh : ℕ}

/-- The matrix `C*ᵢ` of Algorithm 2, step 3 (p. 1108): its `j`-th row is `∂/∂x (hᵢ(x))ⱼ` at `x = yᵢ`
if the `j`-th constraint is active (`(hᵢ(yᵢ))ⱼ = 0`), and `0` otherwise. -/
noncomputable def Cstar (P : Problem N n m nh) (i : Fin N) (yi : Fin n → ℝ) :
    Matrix (Fin nh) (Fin n) ℝ :=
  fun j k => if P.h i yi j = 0 then grad (fun z => P.h i z j) yi k else 0

/-- The modified gradient of Algorithm 2, step 3 (p. 1108):
`gᵢ = ∇fᵢ(yᵢ) + (C*ᵢ − Cᵢ)ᵀ κᵢ`. -/
noncomputable def modGrad (P : Problem N n m nh) (i : Fin N) (yi : Fin n → ℝ) (κi : Fin nh → ℝ)
    (Ci : Matrix (Fin nh) (Fin n) ℝ) : Fin n → ℝ :=
  grad (P.f i) yi + (Cstar P i yi - Ci)ᵀ *ᵥ κi

/-- `(Δy, s, λ_QP, ν)` solves the KKT system of the coupled QP (3.3) of Algorithm 2, step 4 (p. 1108),
`min_{Δy,s} ∑ᵢ {½ Δyᵢᵀ Hᵢ Δyᵢ + gᵢᵀ Δyᵢ} + λᵀ s + (μ/2)‖s‖²₂`
s.t. `∑ᵢ Aᵢ (yᵢ + Δyᵢ) = b + s | λ_QP`, `Cᵢ Δyᵢ = 0 | νᵢ`,
with Lagrangian `… + λ_QPᵀ(∑ᵢ Aᵢ(yᵢ + Δyᵢ) − b − s) + ∑ᵢ νᵢᵀ Cᵢ Δyᵢ`
(the sign convention of footnote 4, p. 1110: stationarity in `s` reads `λ + μ s − λ_QP = 0`):
1. `Hᵢ Δyᵢ + gᵢ + Aᵢᵀ λ_QP + Cᵢᵀ νᵢ = 0` for every `i`;
2. `λ + μ s − λ_QP = 0`;
3. `∑ᵢ Aᵢ (yᵢ + Δyᵢ) = b + s`;
4. `Cᵢ Δyᵢ = 0` for every `i`.
Here `gᵢ = modGrad P i yᵢ κᵢ Cᵢ`. -/
def QPKKT (P : Problem N n m nh) (lam : Fin m → ℝ) (y : Fin N → Fin n → ℝ)
    (κ : Fin N → Fin nh → ℝ) (C : Fin N → Matrix (Fin nh) (Fin n) ℝ)
    (H : Fin N → Matrix (Fin n) (Fin n) ℝ) (μ : ℝ)
    (Δy : Fin N → Fin n → ℝ) (s : Fin m → ℝ) (lamQP : Fin m → ℝ) (ν : Fin N → Fin nh → ℝ) :
    Prop :=
  (∀ i, H i *ᵥ Δy i + modGrad P i (y i) (κ i) (C i) + (P.A i)ᵀ *ᵥ lamQP + (C i)ᵀ *ᵥ ν i = 0) ∧
  lam + μ • s - lamQP = 0 ∧
  ∑ i, P.A i *ᵥ (y i + Δy i) = P.b + s ∧
  (∀ i, C i *ᵥ Δy i = 0)

/-- The dual update of Algorithm 2, step 5 (p. 1108): `λ⁺ = λ + α₃ (λ_QP − λ)`. -/
def lamPlus {m : ℕ} (lam : Fin m → ℝ) (α₃ : ℝ) (lamQP : Fin m → ℝ) : Fin m → ℝ :=
  lam + α₃ • (lamQP - lam)

/-- The formula (A.3) (p. 1122) for the dual gradient: `∇V(λ) = ∑ᵢ Aᵢ yᵢ − b`, where `y` is the
solution of the decoupled problems (A.2). Here it is a formula in `y`, not a derivative. -/
def gradV (P : Problem N n m nh) (y : Fin N → Fin n → ℝ) : Fin m → ℝ :=
  ∑ i, P.A i *ᵥ y i - P.b

/-- The reduced inverse `Hᵢ⁻¹ − Hᵢ⁻¹ Cᵢᵀ [Cᵢ Hᵢ⁻¹ Cᵢᵀ]⁻¹ Cᵢ Hᵢ⁻¹` occurring in (A.5)/(A.6), p. 1123
(with the corrected bracket `[Cᵢ Hᵢ⁻¹ Cᵢᵀ]`; see `Mmat`). -/
noncomputable def reducedInv (Hi : Matrix (Fin n) (Fin n) ℝ) (Ci : Matrix (Fin nh) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Hi⁻¹ - Hi⁻¹ * Ciᵀ * (Ci * Hi⁻¹ * Ciᵀ)⁻¹ * Ci * Hi⁻¹

/-- The scaling matrix (A.6), p. 1123, **corrected**:
`M = − ∑ᵢ Aᵢ [Hᵢ⁻¹ − Hᵢ⁻¹ Cᵢᵀ [Cᵢ Hᵢ⁻¹ Cᵢᵀ]⁻¹ Cᵢ Hᵢ⁻¹] Aᵢᵀ`.
(A.6) as printed has `[Cᵢ Hᵢ Cᵢᵀ]^†`; this is a typo for `[Cᵢ Hᵢ⁻¹ Cᵢᵀ]^†`, cf. (A.5). When `Cᵢ` has full
row rank and `Hᵢ ≻ 0` the bracket is invertible, so its pseudo-inverse is its inverse. -/
noncomputable def Mmat (P : Problem N n m nh) (C : Fin N → Matrix (Fin nh) (Fin n) ℝ)
    (H : Fin N → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  -∑ i, P.A i * reducedInv (H i) (C i) * (P.A i)ᵀ

/-- The (inexact) dual Newton step (A.4), p. 1122: `λ⁺_DD = λ − α (M − (1/μ) I)⁻¹ ∇V(λ)`. -/
noncomputable def lamDD {m : ℕ} (lam : Fin m → ℝ) (α μ : ℝ) (M : Matrix (Fin m) (Fin m) ℝ)
    (gV : Fin m → ℝ) : Fin m → ℝ :=
  lam - α • ((M - μ⁻¹ • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ *ᵥ gV)

end ALADIN.DualDecomp


