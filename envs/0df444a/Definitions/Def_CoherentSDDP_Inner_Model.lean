-- Prove2me | Definitions.Def_CoherentSDDP_Inner_Model
-- name    : CoherentSDDP_Inner_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:01.439828+00:00
-- url     : https://prove2.me/theorems/1291de00-95fc-4cbb-9881-dae10cb84c3f
-- title:
--   (1), (2), (8), (13), pp. 3–17 — the stagewise-independent multistage LP, inner approximations 𝒬̂ₜ, the bound y, the policy π̂ and its nested risk-adjusted cost v(π̂)
-- statement:
--   This file sets up the multistage stochastic linear program of Philpott, de Matos and Finardi together with the inner-approximation objects of §§3.2 and 4.
--
--   **The model (1)–(2).** There are $T$ stages $t=1,\dots,T$. Decisions are $x_t\in\mathbb R^n$; $A_t,E_t$ are $m\times n$ matrices and $c_t\in\mathbb R^n$. Stage 1 is deterministic with data $A_1,b_1,c_1$. For $t\ge2$ the outcome $\omega_t$ ranges over a finite set $\Omega_t$, stagewise independently, and the right-hand side is $b_t(\omega_t)$. Each stage $t\ge2$ carries a one-step risk measure $\rho_t$ acting on random costs $\Omega_t\to\mathbb R$, extended to $\mathbb R\cup\{+\infty\}$ as $\bar\rho_t$. The feasible set of stage $t$ is
--   $$
--   \mathcal X_t(\omega_t)=\{x_t\ge0:\ A_tx_t=b_t(\omega_t)-E_tx_{t-1}\}.
--   $$
--
--   **Inner approximations.** For each $s=2,\dots,T$ there are $J_{s-1}$ points $x^1_{s-1},\dots,x^{J_{s-1}}_{s-1}\in\mathbb R^n$ and numbers $q^1_s,\dots,q^{J_{s-1}}_s\in\mathbb R\cup\{\pm\infty\}$. With $\Lambda_{s-1}$ the simplex of weights $\lambda\ge0$, $\sum_j\lambda^j=1$, the inner approximation is
--   $$
--   \hat{\mathcal Q}_s(x)=\min\Big\{\sum_{j}\lambda^jq^j_s:\ \sum_j\lambda^jx^j_{s-1}=x,\ \lambda\in\Lambda_{s-1}\Big\},
--   $$
--   equal to $+\infty$ when $x$ is not a convex combination of the points, and $\hat{\mathcal Q}_{T+1}\equiv0$.
--
--   **The stage problem (13) and the bound (8).** The policy's stage problem is
--   $$
--   q_t(x_{t-1},\omega_t)=\min\{c_t^\top x_t+\hat{\mathcal Q}_{t+1}(x_t):\ x_t\in\mathcal X_t(\omega_t)\},
--   $$
--   ($+\infty$ if infeasible), and the upper bound of step 5 of the Inner Approximation Algorithm is
--   $$
--   y=\min\{c_1^\top x_1+\hat{\mathcal Q}_2(x_1):\ A_1x_1=b_1\},
--   $$
--   which is (8) after the minimization over $\lambda$ is absorbed into $\hat{\mathcal Q}_2$.
--
--   **The bounds.** The numbers $q^j_s$ are *upper bounds* when $q^j_s\ge\bar\rho_s\big(q_s(x^j_{s-1},\omega_s)\big)$ for every $s=2,\dots,T$ and every $j$: each $q^j_s$ dominates the risk-adjusted optimal value of the stage problem (13) at the point $x^j_{s-1}$, which is what the Upper Bound Computation (U) of §5 computes.
--
--   **The policy $\hat\pi$ and its cost.** A policy $\hat\pi$ consists of actions $\hat x_t(x_{t-1},\omega_t)$ for $t=2,\dots,T$ and a first-stage action $\hat x_1$. It is *defined by the inner approximation* when, at every state $x_{t-1}$ and outcome $\omega_t$ with $\mathcal X_t(\omega_t)\neq\emptyset$, the action $\hat x_t(x_{t-1},\omega_t)$ is a minimizer of (13), and $\hat x_1$ is a minimizer of (8). The risk-adjusted cost of the policy over stages $t,\dots,T$ is defined backwards by
--   $$
--   \hat v_t(x_{t-1},\omega_t)=c_t^\top\hat x_t+\bar\rho_{t+1}\big(\hat v_{t+1}(\hat x_t,\omega_{t+1})\big),\qquad \hat x_t=\hat x_t(x_{t-1},\omega_t),
--   $$
--   with no future term at $t=T$ and $\hat v_t=+\infty$ when $\mathcal X_t(\omega_t)=\emptyset$. The nested risk-adjusted cost of the policy is $v(\hat\pi)=c_1^\top\hat x_1+\bar\rho_2\big(\hat v_2(\hat x_1,\omega_2)\big)$.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`, matrix–vector products use `mulVec`, and all stages share $n$ and $m$, as on p. 4. The probabilities of $\Omega_t$ are not part of the model: they enter only through $\rho_t$. Points and bounds are indexed by the stage $s$ of the Bellman function they define: `pts s j` is $x^j_{s-1}$, `qv s j` is $q^j_s$, `J s` is $J_{s-1}$. Minima are `EReal` infima ($+\infty$ on an empty set); attainment is a separate statement. In the weighted sums a zero weight times $+\infty$ counts as $0$, the linear-programming convention. Following (8) as printed, $y$ has no constraint $x_1\ge0$. The stage problem includes $x_t\ge0$, as in (13); the multiplier form (7) omits it, and the two agree whenever the points $x^j_t$ are nonnegative. The terminal convention is the first option on p. 4, $\rho_{T+1}(Q_{T+1})=0$. The policy is any selection with the minimizing property, not a particular argmin; at an infeasible state its action is unconstrained and never used. The upper-bound property is the form the proof of Proposition 5 uses (p. 17) and (U) computes (p. 18); p. 16 words it as a bound on the true value $\rho_{t+1}(Q_{t+1})$, which does not suffice for the proof.
-- source:
--   Philpott, de Matos & Finardi, On Solving Multistage Stochastic Programs with Coherent Risk Measures, authors' manuscript of 13 August 2012 (Operations Research, 2013), pp. 3–4, (1), (2), 𝒳_t; p. 8, Λ_t and 𝒬̂_{t+1}; p. 9, Inner Approximation Algorithm steps 1 and 5, (8); p. 11, the policy π̂; pp. 16–17, proof of Proposition 5, v̂_t and (13); p. 18, Upper Bound Computation (U)

import Mathlib
import Definitions.Def_CoherentSDDP_Inner_Basic

namespace CoherentSDDP.Inner

open Matrix

/-- The data of the multistage stochastic linear program (1)–(2) (§2, pp. 3–4) with stagewise
independent noise. Stages are `t = 1, …, T`; stage 1 is deterministic (`A₁ b₁ c₁`), and for
`t ≥ 2` the outcome `ω_t` ranges over `Ω t`, the right-hand side is `b t ω_t`, and the one-step
risk measure is `ρ t`, acting on random costs `Ω t → ℝ`. All decisions lie in `ℝⁿ` and all
constraint systems have `m` rows. -/
structure Model (n m : ℕ) (Ω : ℕ → Type) where
  /-- The number of stages `T`. -/
  T : ℕ
  /-- First-stage constraint matrix `A₁`. -/
  A₁ : Matrix (Fin m) (Fin n) ℝ
  /-- First-stage right-hand side `b₁`. -/
  b₁ : Fin m → ℝ
  /-- First-stage cost vector `c₁`. -/
  c₁ : Fin n → ℝ
  /-- Stage-`t` recourse matrix `A_t`. -/
  A : ℕ → Matrix (Fin m) (Fin n) ℝ
  /-- Stage-`t` technology matrix `E_t`, linking `x_{t-1}` to stage `t`. -/
  E : ℕ → Matrix (Fin m) (Fin n) ℝ
  /-- Random right-hand side `b_t(ω_t)`. -/
  b : (t : ℕ) → Ω t → Fin m → ℝ
  /-- Stage-`t` cost vector `c_t`. -/
  c : ℕ → Fin n → ℝ
  /-- One-step risk measure `ρ_t` on random costs at stage `t`. -/
  ρ : (t : ℕ) → (Ω t → ℝ) → ℝ

variable {n m : ℕ} {Ω : ℕ → Type}

/-- The feasible set `𝒳_t(ω) = {x_t ≥ 0 : A_t x_t = b_t(ω) − E_t x_{t−1}}` of the stage problem
(2), p. 4. -/
def Model.feas (M : Model n m Ω) (t : ℕ) (xprev : Fin n → ℝ) (ω : Ω t) : Set (Fin n → ℝ) :=
  {x | 0 ≤ x ∧ M.A t *ᵥ x = M.b t ω - M.E t *ᵥ xprev}

/-- The points and upper bounds defining the inner approximations (§3.2, pp. 7–8; §4, p. 16).
**Index convention:** everything is indexed by the stage `s` of the Bellman function `𝒬̂_s` it
defines. `J s` is the paper's `J_{s−1}`, `pts s j` is the point `x^j_{s−1}` and `qv s j` is the
bound `q^j_s`, for `s = 2, …, T`. -/
structure InnerData (n : ℕ) where
  /-- Number of points `J_{s−1}`. -/
  J : ℕ → ℕ
  /-- The points `x^j_{s−1}`. -/
  pts : (s : ℕ) → Fin (J s) → Fin n → ℝ
  /-- The bounds `q^j_s ∈ ℝ ∪ {±∞}`. -/
  qv : (s : ℕ) → Fin (J s) → EReal

/-- The inner approximation `𝒬̂_s(x) = min {Σ_j λ^j q^j_s : Σ_j λ^j x^j_{s−1} = x, λ ∈ Λ_{s−1}}`
(p. 8), an extended-real infimum (`+∞` when `x` is not a convex combination of the points), with
the terminal convention `𝒬̂_{T+1} ≡ 0` (Inner Approximation Algorithm, step 1, p. 9). -/
noncomputable def Qhat (M : Model n m Ω) (D : InnerData n) (s : ℕ) (x : Fin n → ℝ) : EReal :=
  if M.T < s then 0 else
    ⨅ w ∈ stdSimplex ℝ (Fin (D.J s)), ⨅ (_ : ∑ j, w j • D.pts s j = x),
      ∑ j, ((w j : ℝ) : EReal) * D.qv s j

/-- The stage problem (13) of the inner-approximation policy (p. 11, p. 17):
`q_t(x_{t−1}, ω_t) = min {c_tᵀ x_t + 𝒬̂_{t+1}(x_t) : x_t ∈ 𝒳_t(ω_t)}`, an extended-real infimum
(`+∞` when the stage problem is infeasible). -/
noncomputable def qstage (M : Model n m Ω) (D : InnerData n) (t : ℕ) (xprev : Fin n → ℝ)
    (ω : Ω t) : EReal :=
  ⨅ x ∈ M.feas t xprev ω, ((M.c t ⬝ᵥ x : ℝ) : EReal) + Qhat M D (t + 1) x

/-- The upper bound (8), p. 9: `y = min {c₁ᵀ x₁ + Σ_j λ^j q^j_2 : A₁x₁ = b₁, Σ_j λ^j x^j_1 = x₁,
λ ∈ Λ₁}`, written as `min_{A₁x₁ = b₁} c₁ᵀx₁ + 𝒬̂₂(x₁)`. As printed, (8) has no constraint
`x₁ ≥ 0`. -/
noncomputable def y (M : Model n m Ω) (D : InnerData n) : EReal :=
  ⨅ x, ⨅ (_ : M.A₁ *ᵥ x = M.b₁), ((M.c₁ ⬝ᵥ x : ℝ) : EReal) + Qhat M D 2 x

/-- The bounds `q^j_s` are upper bounds on the risk-adjusted optimal value of (13) at the points:
`q^j_s ≥ ρ̄_s(q_s(x^j_{s−1}, ω_s))` for `s = 2, …, T` and every `j`. This is the form used in the
proof of Proposition 5 (p. 17) and computed (with equality) by the Upper Bound Computation (U),
p. 18. -/
def UpperBounds (M : Model n m Ω) (D : InnerData n) : Prop :=
  ∀ s, 2 ≤ s → s ≤ M.T → ∀ j,
    riskE (M.ρ s) (fun ω => qstage M D s (D.pts s j) ω) ≤ D.qv s j

/-- `(xhat, x1hat)` is a policy `π̂` defined by the inner approximation (p. 11, p. 17):
for `2 ≤ t ≤ T`, at every state `x_{t−1}` and outcome `ω_t` whose stage problem is feasible, the
action `x̂_t(x_{t−1}, ω_t)` is feasible and minimizes `c_tᵀ x_t + 𝒬̂_{t+1}(x_t)` over
`𝒳_t(ω_t)`; and the first-stage action `x̂₁` solves (8). -/
def IsInnerPolicy (M : Model n m Ω) (D : InnerData n)
    (xhat : (t : ℕ) → (Fin n → ℝ) → Ω t → Fin n → ℝ) (x1hat : Fin n → ℝ) : Prop :=
  (∀ t, 2 ≤ t → t ≤ M.T → ∀ (xprev : Fin n → ℝ) (ω : Ω t), (M.feas t xprev ω).Nonempty →
    xhat t xprev ω ∈ M.feas t xprev ω ∧
    ∀ x ∈ M.feas t xprev ω,
      ((M.c t ⬝ᵥ xhat t xprev ω : ℝ) : EReal) + Qhat M D (t + 1) (xhat t xprev ω) ≤
        ((M.c t ⬝ᵥ x : ℝ) : EReal) + Qhat M D (t + 1) x) ∧
  M.A₁ *ᵥ x1hat = M.b₁ ∧ ((M.c₁ ⬝ᵥ x1hat : ℝ) : EReal) + Qhat M D 2 x1hat = y M D

open Classical in
/-- The actual risk-adjusted cost `v̂_t(x_{t−1}, ω_t)` of the policy over stages `t, …, T`
(proof of Proposition 5, p. 16): `v̂_t = c_tᵀ x̂_t + ρ̄_{t+1}(v̂_{t+1}(x̂_t, ω_{t+1}))` with
`x̂_t = x̂_t(x_{t−1}, ω_t)`, and no future term after stage `T`. An infeasible stage problem
costs `+∞`. -/
noncomputable def vhat (M : Model n m Ω) (xhat : (t : ℕ) → (Fin n → ℝ) → Ω t → Fin n → ℝ)
    (t : ℕ) (xprev : Fin n → ℝ) (ω : Ω t) : EReal :=
  if (M.feas t xprev ω).Nonempty then
    ((M.c t ⬝ᵥ xhat t xprev ω : ℝ) : EReal) +
      (if _h : t < M.T then
        riskE (M.ρ (t + 1)) (fun ω' => vhat M xhat (t + 1) (xhat t xprev ω) ω')
      else 0)
  else ⊤
termination_by M.T - t

/-- The risk-adjusted cost `v(π̂) = c₁ᵀ x̂₁ + ρ̄₂(v̂₂(x̂₁, ω₂))` of the policy evaluated at the
first-stage action `x̂₁` (p. 17). -/
noncomputable def vpi (M : Model n m Ω) (xhat : (t : ℕ) → (Fin n → ℝ) → Ω t → Fin n → ℝ)
    (x1hat : Fin n → ℝ) : EReal :=
  ((M.c₁ ⬝ᵥ x1hat : ℝ) : EReal) + riskE (M.ρ 2) (fun ω => vhat M xhat 2 x1hat ω)

end CoherentSDDP.Inner


