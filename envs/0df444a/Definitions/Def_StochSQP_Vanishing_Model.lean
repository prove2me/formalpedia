-- Prove2me | Definitions.Def_StochSQP_Vanishing_Model
-- name    : StochSQP_Vanishing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:23.322881+00:00
-- url     : https://prove2.me/theorems/25804064-aec2-4083-8f0c-ddffff76c181
-- title:
--   §2–§3 and Algorithm 1, pp. 4–10 — equality-constrained problem, Assumptions 1 and 3, runs of the stochastic SQP algorithm, condition (28)
-- statement:
--   This file sets up the equality-constrained problem and the stochastic sequential quadratic optimization (SQP) algorithm of Berahas, Curtis, O'Neill and Robinson.
--
--   **Problem.** For $m \le n$ and functions $f : \mathbb R^n \to \mathbb R$, $c : \mathbb R^n \to \mathbb R^m$, the problem is
--   $$\min_{x \in \mathbb R^n} f(x) \quad \text{s.t.} \quad c(x) = 0 .$$
--   Write $J(x) = \nabla c(x)^T$ for the constraint Jacobian, $J(x)^T$ for its transpose (adjoint), $\nabla f$ for the gradient, and $c_k = c(x_k)$, $J_k = J(x_k)$ along a sequence of iterates. The merit function is $\phi(x,\tau) = \tau f(x) + \|c(x)\|_2$ (10), and the model reduction is
--   $$\Delta l(x,\tau,g,d) = -\tau g^T d + \|c(x)\|_2 - \|c(x) + J(x) d\|_2 \qquad (13).$$
--
--   **Parameters** (Require line of Algorithm 1): $L, \Gamma > 0$; $\tau_{-1}, \chi_{-1}, \zeta_{-1}, \xi_{-1} > 0$; $\omega > 0$; $\epsilon_v \in (0,1]$; $\sigma, \epsilon_\tau, \epsilon_\zeta, \epsilon_\xi, \eta \in (0,1)$; $\epsilon_\chi > 0$; $\theta \ge 0$.
--
--   **Runs.** A run is a family of sequences $(x_k, g_k, v_k, u_k, y_k, d_k, H_k, \beta_k, \tau_k, \chi_k, \zeta_k, \xi_k, \alpha_k)_{k \in \mathbb N}$ such that, for every $k$:
--   1. $\beta_k \in (0,1]$, and the run does not terminate: it is not the case that $\|J_k^T c_k\|_2 = 0$ and $\|c_k\|_2 > 0$;
--   2. the normal step $v_k$ lies in $\mathrm{Range}(J_k^T)$, satisfies $\|v_k\|_2 \le \omega \|J_k^T c_k\|_2$ (feasibility for (5)) and the Cauchy decrease condition (6), $\|c_k\|_2 - \|c_k + J_k v_k\|_2 \ge \epsilon_v(\|c_k\|_2 - \|c_k + \alpha_k^C J_k v_k^C\|_2)$ with $v_k^C = -J_k^T c_k$ and $\alpha_k^C$ the minimizer of $\tfrac12\|c_k + \alpha J_k v_k^C\|_2^2$ over $\alpha \in [0,\omega]$;
--   3. $(u_k, y_k)$ solves (9): $H_k u_k + J_k^T y_k = -(g_k + H_k v_k)$, $J_k u_k = 0$; and $d_k = v_k + u_k$;
--   4. if $d_k = 0$: $\tau_k = \tau_{k-1}$, $(\chi_k,\zeta_k) = (\chi_{k-1},\zeta_{k-1})$, $\xi_k = \xi_{k-1}$, $\alpha_k = 1$;
--   5. if $d_k \ne 0$: $\tau_k$ by (11)–(12), $(\chi_k, \zeta_k)$ by (15)–(16), $\xi_k$ by (17)–(18), and $\alpha_k = \mathrm{Proj}_k(\alpha_k^{\rm suff})$ by (21)–(22);
--   6. $x_{k+1} = x_k + \alpha_k d_k$.
--
--   In (11)–(12): $\tau_k^{\rm trial} = \infty$ if $g_k^T d_k + u_k^T H_k u_k \le 0$, otherwise $\tau_k^{\rm trial} = (1-\sigma)(\|c_k\|_2 - \|c_k + J_k d_k\|_2)/(g_k^T d_k + u_k^T H_k u_k)$; $\tau_k = \tau_{k-1}$ if $\tau_{k-1} \le \tau_k^{\rm trial}$, else $\tau_k = \min\{(1-\epsilon_\tau)\tau_{k-1}, \tau_k^{\rm trial}\}$. In (15)–(16): if $\|u_k\|_2^2 \ge \chi_{k-1}\|v_k\|_2^2$ and $\tfrac12 d_k^T H_k d_k < \tfrac14 \zeta_{k-1}\|u_k\|_2^2$, then $(\chi_k,\zeta_k) = ((1+\epsilon_\chi)\chi_{k-1}, (1-\epsilon_\zeta)\zeta_{k-1})$, else they are unchanged. The direction is *tangentially dominated* if $\|u_k\|_2^2 \ge \chi_k \|v_k\|_2^2$. In (17)–(18), $\xi_k^{\rm trial} = \Delta l(x_k,\tau_k,g_k,d_k)/(\tau_k\|d_k\|_2^2)$ if tangentially dominated and $\Delta l(x_k,\tau_k,g_k,d_k)/\|d_k\|_2^2$ otherwise, and $\xi_k$ is updated from $\xi_{k-1}$ as $\tau_k$ is. In (21)–(22),
--   $$\alpha_k^{\rm suff} = \min\Big\{\frac{2(1-\eta)\beta_k \Delta l(x_k,\tau_k,g_k,d_k)}{(\tau_k L + \Gamma)\|d_k\|_2^2}, 1\Big\},$$
--   and $\alpha_k$ is its projection onto $[\ell_k, \ell_k + \theta\beta_k^2]$, where $\ell_k = 2(1-\eta)\beta_k\xi_k\tau_k/(\tau_k L + \Gamma)$ if tangentially dominated and $\ell_k = 2(1-\eta)\beta_k\xi_k/(\tau_k L + \Gamma)$ otherwise.
--
--   **Assumption 1.** $X \subseteq \mathbb R^n$ is open and convex (it is used with every iterate in $X$), $m \le n$, $f$ and $c$ are continuously differentiable and bounded over $X$, $\nabla f$ is Lipschitz with constant $L$ and bounded over $X$, and $J$ is Lipschitz with constant $\Gamma$ (operator norm) and bounded over $X$.
--
--   **Assumption 3.** Each $H_k$ is symmetric, $\|H_k\|_2 \le \kappa_H$, and $u^T H_k u \ge \zeta\|u\|_2^2$ for all $u \in \mathrm{Null}(J_k)$, with $\kappa_H, \zeta > 0$.
--
--   **Condition (28).** $\beta_k \in (0,1]$ and $2(1-\eta)\beta_k\xi_k\max\{\tau_k,1\}/(\tau_k L + \Gamma) \in (0,1]$ for all $k$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** The model is pathwise: a run is any family of sequences satisfying lines 2–19 of Algorithm 1; there is no probability space, and $g_k$ is an arbitrary vector (the stochastic gradient), so the requirement that $g_k$ satisfy Assumption 2 is not part of the run; statements that need it bound $\|g_k - \nabla f(x_k)\|_2$ explicitly. The expectation structure $f = \mathbb E[F(\cdot,\iota)]$ is not modelled. Assumption 3's clause "$H_k$ is chosen independently from $g_k$" is a probabilistic statement and is dropped. Condition (6) is stated without naming $\alpha_k^C$: since $\alpha_k^C$ minimizes $\tfrac12\|c_k + \alpha J_k v_k^C\|_2^2$ over $[0,\omega]$, (6) is equivalent to $\|c_k\|_2 - \|c_k + J_k v_k\|_2 \ge \epsilon_v(\|c_k\|_2 - \|c_k + a J_k v_k^C\|_2)$ for every $a \in [0,\omega]$, which is how it is encoded (and which avoids an argmin that is not unique when $J_k v_k^C = 0$). The infinite trial values of lines 9, 11 and (11) are encoded by branching, never by a real number. Initial values $\tau_{-1}, \chi_{-1}, \zeta_{-1}, \xi_{-1}$ are parameters, and `prev s s₀ k` denotes $s_{k-1}$ with $s_{-1} = s_0$; $\xi_{-1} > 0$ is required although the Require line omits $\xi_{-1}$. The constant $\Gamma$ is the Lipschitz constant of $J$ (Assumption 1 and (19)); the Require line's "a Lipschitz constant for $c$" is read accordingly. "Continuously differentiable over $X$" is `ContDiffOn ℝ 1` on $X$, and the Lipschitz conditions are imposed on $X$. Matrix norms are operator norms between Euclidean spaces.
-- source:
--   Berahas, Curtis, O'Neill & Robinson, arXiv:2106.13015v2, pp. 4–10, §2 problem (1), Assumption 1 (p. 4), Assumption 3 (p. 6), §3 (5)–(6), (9)–(18), (21)–(22) (pp. 5–9), Algorithm 1 (p. 10), condition (28) (p. 15)

import Mathlib

namespace StochSQP.Vanishing

open scoped InnerProductSpace RealInnerProductSpace

/-- The Euclidean space `ℝⁿ` with the norm `‖·‖₂`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Problem (1), p. 4: minimize `f(x)` subject to `c(x) = 0`, with `f : ℝⁿ → ℝ`, `c : ℝⁿ → ℝᵐ`. -/
structure Problem (n m : ℕ) where
  f : E n → ℝ
  c : E n → E m

variable {n m : ℕ}

/-- The constraint Jacobian `J(x) = ∇c(x)ᵀ`, as a linear map `ℝⁿ → ℝᵐ`. -/
noncomputable def Problem.J (P : Problem n m) (x : E n) : E n →L[ℝ] E m := fderiv ℝ P.c x

/-- The transposed Jacobian `J(x)ᵀ : ℝᵐ → ℝⁿ` (the adjoint of `J(x)`). -/
noncomputable def Problem.Jt (P : Problem n m) (x : E n) : E m →L[ℝ] E n :=
  ContinuousLinearMap.adjoint (P.J x)

/-- The gradient `∇f(x)`. -/
noncomputable def Problem.grad (P : Problem n m) (x : E n) : E n := gradient P.f x

/-- The parameters of Algorithm 1 (Require line, p. 10). `τ₀ χ₀ ζ₀ ξ₀` stand for
`τ_{-1}, χ_{-1}, ζ_{-1}, ξ_{-1}`; `εv … εξ` for `ϵ_v … ϵ_ξ`. -/
structure Params where
  L : ℝ
  Γ : ℝ
  τ₀ : ℝ
  χ₀ : ℝ
  ζ₀ : ℝ
  ξ₀ : ℝ
  ω : ℝ
  εv : ℝ
  σ : ℝ
  ετ : ℝ
  εχ : ℝ
  εζ : ℝ
  εξ : ℝ
  η : ℝ
  θ : ℝ

/-- The parameter ranges of the Require line of Algorithm 1 (p. 10), with `ξ_{-1} > 0`. -/
def Params.Valid (A : Params) : Prop :=
  0 < A.L ∧ 0 < A.Γ ∧ 0 < A.τ₀ ∧ 0 < A.χ₀ ∧ 0 < A.ζ₀ ∧ 0 < A.ξ₀ ∧ 0 < A.ω ∧
  0 < A.εv ∧ A.εv ≤ 1 ∧ 0 < A.σ ∧ A.σ < 1 ∧ 0 < A.ετ ∧ A.ετ < 1 ∧ 0 < A.εχ ∧
  0 < A.εζ ∧ A.εζ < 1 ∧ 0 < A.εξ ∧ A.εξ < 1 ∧ 0 < A.η ∧ A.η < 1 ∧ 0 ≤ A.θ

/-- `prev s s₀ k` is `s_{k-1}`, with `s_{-1} = s₀`. -/
def prev (s : ℕ → ℝ) (s₀ : ℝ) : ℕ → ℝ
  | 0 => s₀
  | k + 1 => s k

/-- The model reduction (13): `Δl(x, τ, g, d) = -τ gᵀd + ‖c(x)‖₂ - ‖c(x) + J(x) d‖₂`. -/
noncomputable def deltaL (P : Problem n m) (x : E n) (τ : ℝ) (g d : E n) : ℝ :=
  -τ * ⟪g, d⟫_ℝ + ‖P.c x‖ - ‖P.c x + P.J x d‖

/-- The merit function (10): `φ(x, τ) = τ f(x) + ‖c(x)‖₂`. -/
noncomputable def merit (P : Problem n m) (x : E n) (τ : ℝ) : ℝ := τ * P.f x + ‖P.c x‖

/-- Projection of `a` onto the interval `[lo, hi]`. -/
noncomputable def proj (lo hi a : ℝ) : ℝ := max lo (min a hi)

/-- The sequences produced by a run of Algorithm 1: iterates `x_k`, stochastic gradients `g_k`,
normal steps `v_k`, tangential steps `u_k`, multipliers `y_k`, search directions `d_k`, matrices
`H_k`, and the scalar sequences `β_k, τ_k, χ_k, ζ_k, ξ_k, α_k`. -/
structure Run (n m : ℕ) where
  x : ℕ → E n
  g : ℕ → E n
  v : ℕ → E n
  u : ℕ → E n
  d : ℕ → E n
  y : ℕ → E m
  H : ℕ → (E n →L[ℝ] E n)
  β : ℕ → ℝ
  τ : ℕ → ℝ
  χ : ℕ → ℝ
  ζ : ℕ → ℝ
  ξ : ℕ → ℝ
  α : ℕ → ℝ

/-- The search direction of iteration `k` is tangentially dominated: `‖u_k‖₂² ≥ χ_k ‖v_k‖₂²`
(as in (17) and (22)). Its negation is "normally dominated". -/
def Run.TangDom (R : Run n m) (k : ℕ) : Prop := R.χ k * ‖R.v k‖ ^ 2 ≤ ‖R.u k‖ ^ 2

/-- Rules (11)–(12) for the merit parameter, in an iteration with `d_k ≠ 0`. When
`g_kᵀd_k + u_kᵀH_k u_k ≤ 0` the trial value is `∞` and `τ_k = τ_{k-1}`. -/
def tauRule (P : Problem n m) (A : Params) (R : Run n m) (k : ℕ) : Prop :=
  (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ ≤ 0 → R.τ k = prev R.τ A.τ₀ k) ∧
  (0 < ⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ →
    let t := (1 - A.σ) * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.d k)‖) /
      (⟪R.g k, R.d k⟫_ℝ + ⟪R.u k, R.H k (R.u k)⟫_ℝ)
    (prev R.τ A.τ₀ k ≤ t → R.τ k = prev R.τ A.τ₀ k) ∧
    (t < prev R.τ A.τ₀ k → R.τ k = min ((1 - A.ετ) * prev R.τ A.τ₀ k) t))

/-- Condition (15): `‖u_k‖₂² ≥ χ_{k-1}‖v_k‖₂²` and `½ d_kᵀH_k d_k < ¼ ζ_{k-1}‖u_k‖₂²`. -/
def Cond15 (A : Params) (R : Run n m) (k : ℕ) : Prop :=
  prev R.χ A.χ₀ k * ‖R.v k‖ ^ 2 ≤ ‖R.u k‖ ^ 2 ∧
  (1 / 2 : ℝ) * ⟪R.d k, R.H k (R.d k)⟫_ℝ < (1 / 4 : ℝ) * prev R.ζ A.ζ₀ k * ‖R.u k‖ ^ 2

/-- Rule (16) for `(χ_k, ζ_k)`. -/
def chiZetaRule (A : Params) (R : Run n m) (k : ℕ) : Prop :=
  (Cond15 A R k →
    R.χ k = (1 + A.εχ) * prev R.χ A.χ₀ k ∧ R.ζ k = (1 - A.εζ) * prev R.ζ A.ζ₀ k) ∧
  (¬ Cond15 A R k → R.χ k = prev R.χ A.χ₀ k ∧ R.ζ k = prev R.ζ A.ζ₀ k)

/-- The trial value (17): `Δl(x_k, τ_k, g_k, d_k)/(τ_k‖d_k‖₂²)` if tangentially dominated,
`Δl(x_k, τ_k, g_k, d_k)/‖d_k‖₂²` otherwise (used only when `d_k ≠ 0`). -/
noncomputable def xiTrial (P : Problem n m) (R : Run n m) (k : ℕ) : ℝ :=
  if R.χ k * ‖R.v k‖ ^ 2 ≤ ‖R.u k‖ ^ 2 then
    deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) / (R.τ k * ‖R.d k‖ ^ 2)
  else
    deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) / ‖R.d k‖ ^ 2

/-- Rule (18) for `ξ_k`. -/
def xiRule (P : Problem n m) (A : Params) (R : Run n m) (k : ℕ) : Prop :=
  (prev R.ξ A.ξ₀ k ≤ xiTrial P R k → R.ξ k = prev R.ξ A.ξ₀ k) ∧
  (xiTrial P R k < prev R.ξ A.ξ₀ k →
    R.ξ k = min ((1 - A.εξ) * prev R.ξ A.ξ₀ k) (xiTrial P R k))

/-- The trial step size (21):
`α_k^suff = min{2(1-η)β_k Δl(x_k,τ_k,g_k,d_k)/((τ_k L + Γ)‖d_k‖₂²), 1}`. -/
noncomputable def alphaSuff (P : Problem n m) (A : Params) (R : Run n m) (k : ℕ) : ℝ :=
  min (2 * (1 - A.η) * R.β k * deltaL P (R.x k) (R.τ k) (R.g k) (R.d k) /
    ((R.τ k * A.L + A.Γ) * ‖R.d k‖ ^ 2)) 1

/-- The lower end of the projection interval in (22). -/
noncomputable def projLo (A : Params) (R : Run n m) (k : ℕ) : ℝ :=
  if R.χ k * ‖R.v k‖ ^ 2 ≤ ‖R.u k‖ ^ 2 then
    2 * (1 - A.η) * R.β k * R.ξ k * R.τ k / (R.τ k * A.L + A.Γ)
  else
    2 * (1 - A.η) * R.β k * R.ξ k / (R.τ k * A.L + A.Γ)

/-- The upper end of the projection interval in (22): the lower end plus `θβ_k²`. -/
noncomputable def projHi (A : Params) (R : Run n m) (k : ℕ) : ℝ :=
  projLo A R k + A.θ * R.β k ^ 2

/-- Rule (22): `α_k = Proj_k(α_k^suff)`. -/
def alphaRule (P : Problem n m) (A : Params) (R : Run n m) (k : ℕ) : Prop :=
  R.α k = proj (projLo A R k) (projHi A R k) (alphaSuff P A R k)

/-- Condition (6) on the normal step, without naming `α_k^C`: since `α_k^C` minimizes
`½‖c_k + α J_k v_k^C‖₂²` over `α ∈ [0, ω]`, (6) is equivalent to
`‖c_k‖₂ - ‖c_k + J_k v_k‖₂ ≥ ϵ_v(‖c_k‖₂ - ‖c_k + a J_k v_k^C‖₂)` for every `a ∈ [0, ω]`,
where `v_k^C = -J_kᵀc_k`. -/
def cauchyCond (P : Problem n m) (A : Params) (R : Run n m) (k : ℕ) : Prop :=
  ∀ a ∈ Set.Icc (0 : ℝ) A.ω,
    A.εv * (‖P.c (R.x k)‖ - ‖P.c (R.x k) + a • P.J (R.x k) (-(P.Jt (R.x k) (P.c (R.x k))))‖) ≤
      ‖P.c (R.x k)‖ - ‖P.c (R.x k) + P.J (R.x k) (R.v k)‖

/-- A (non-terminating) run of Algorithm 1 (p. 10): for every `k ∈ ℕ`, lines 2–19 hold. -/
def IsRun (P : Problem n m) (A : Params) (R : Run n m) : Prop :=
  ∀ k : ℕ,
    -- Require line: β_k ∈ (0, 1]
    (0 < R.β k ∧ R.β k ≤ 1) ∧
    -- lines 2–4: the run never terminates
    ¬ (‖P.Jt (R.x k) (P.c (R.x k))‖ = 0 ∧ 0 < ‖P.c (R.x k)‖) ∧
    -- line 6: v_k ∈ Range(J_kᵀ), feasible for (5), and (6)
    R.v k ∈ LinearMap.range (P.Jt (R.x k) : E m →ₗ[ℝ] E n) ∧
    ‖R.v k‖ ≤ A.ω * ‖P.Jt (R.x k) (P.c (R.x k))‖ ∧
    cauchyCond P A R k ∧
    -- line 7: (u_k, y_k) solves (9), d_k = v_k + u_k
    R.H k (R.u k) + P.Jt (R.x k) (R.y k) = -(R.g k + R.H k (R.v k)) ∧
    P.J (R.x k) (R.u k) = 0 ∧
    R.d k = R.v k + R.u k ∧
    -- lines 8–12
    (R.d k = 0 → R.τ k = prev R.τ A.τ₀ k ∧ R.χ k = prev R.χ A.χ₀ k ∧
      R.ζ k = prev R.ζ A.ζ₀ k ∧ R.ξ k = prev R.ξ A.ξ₀ k ∧ R.α k = 1) ∧
    -- lines 13–17
    (R.d k ≠ 0 → tauRule P A R k ∧ chiZetaRule A R k ∧ xiRule P A R k ∧ alphaRule P A R k) ∧
    -- line 19
    R.x (k + 1) = R.x k + R.α k • R.d k

/-- Assumption 1 (p. 4) on an open convex set `X` (which, where used, contains every iterate):
`f`, `c` continuously differentiable and bounded over `X`, `∇f` Lipschitz with constant `L` and
bounded over `X`, `J` Lipschitz with constant `Γ` and bounded over `X`, and `m ≤ n`. -/
def Assumption1 (P : Problem n m) (L Γ : ℝ) (X : Set (E n)) : Prop :=
  IsOpen X ∧ Convex ℝ X ∧ m ≤ n ∧
  ContDiffOn ℝ 1 P.f X ∧ ContDiffOn ℝ 1 P.c X ∧
  BddAbove (P.f '' X) ∧ BddBelow (P.f '' X) ∧
  (∀ x ∈ X, ∀ y ∈ X, ‖P.grad x - P.grad y‖ ≤ L * ‖x - y‖) ∧
  Bornology.IsBounded (P.grad '' X) ∧
  Bornology.IsBounded (P.c '' X) ∧
  (∀ x ∈ X, ∀ y ∈ X, ‖P.J x - P.J y‖ ≤ Γ * ‖x - y‖) ∧
  Bornology.IsBounded (P.J '' X)

/-- Assumption 3 (p. 6), pathwise: each `H_k` is symmetric with `‖H_k‖₂ ≤ κ_H`, and
`uᵀH_k u ≥ ζ‖u‖₂²` for all `u ∈ Null(J_k)`. -/
def Assumption3 (P : Problem n m) (R : Run n m) (κH ζH : ℝ) : Prop :=
  0 < κH ∧ 0 < ζH ∧ ∀ k : ℕ, IsSelfAdjoint (R.H k) ∧ ‖R.H k‖ ≤ κH ∧
    ∀ w ∈ LinearMap.ker (P.J (R.x k) : E n →ₗ[ℝ] E m), ζH * ‖w‖ ^ 2 ≤ ⟪w, R.H k w⟫_ℝ

/-- Condition (28), p. 15: `β_k ∈ (0, 1]` and
`2(1-η)β_k ξ_k max{τ_k, 1}/(τ_k L + Γ) ∈ (0, 1]` for all `k`. -/
def Cond28 (A : Params) (R : Run n m) : Prop :=
  ∀ k : ℕ, (0 < R.β k ∧ R.β k ≤ 1) ∧
    0 < 2 * (1 - A.η) * R.β k * R.ξ k * max (R.τ k) 1 / (R.τ k * A.L + A.Γ) ∧
    2 * (1 - A.η) * R.β k * R.ξ k * max (R.τ k) 1 / (R.τ k * A.L + A.Γ) ≤ 1

end StochSQP.Vanishing


