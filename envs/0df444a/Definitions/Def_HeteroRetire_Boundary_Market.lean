-- Prove2me | Definitions.Def_HeteroRetire_Boundary_Market
-- name    : HeteroRetire_Boundary_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:46.432258+00:00
-- url     : https://prove2.me/theorems/790c4d3b-a334-4631-b5e5-d71357c83b0c
-- title:
--   §2 and (13) — deterministic market, mandatory retirement and standing assumptions
-- statement:
--   The market has a mandatory retirement age $T>0$ and a later consumption horizon $\bar T>T$. At each time $t\in[0,\bar T]$ it specifies the interest rate $r(t)$, discount rate $\rho(t)$, income $I(t)$, labor cost $L(t)$, excess return vector $\mu(t)$, volatility matrix $\sigma(t)$, and market price of risk $\vartheta(t)$.
--
--   The standing conditions require $n\ge1$ risky assets; positive, continuous and bounded scalar coefficients; componentwise positive, continuous and bounded excess returns; continuous volatility; uniform ellipticity of $\sigma\sigma^\top$; and
--   $$
--   \sigma(t)\vartheta(t)=\mu(t).
--   $$
--
--   The squared risk magnitude is $\|\vartheta(t)\|^2=\sum_i\vartheta_i(t)^2$. Assumption 18 asks, on an aged window $[T-\ell,T]$ with $0<\ell\le T$, for
--   $$
--   \frac{I'(t)}{I(t)}\le\rho(t)\le\frac{L'(t)}{L(t)}.
--   $$
--
--   These definitions fix the coefficient and horizon conventions used by every retirement statement.
--
--   **Formalization Note** The derivatives at the window endpoints are within derivatives. Positivity of $\mu$ is read componentwise. The additional condition used only for Theorem 19 requires $\rho-r$ and $\|\vartheta\|^2$ to be constant on the aged window; this repairs the time shift in the printed proof.
-- source:
--   Jang, Xu, Zheng, Optimal Investment, Heterogeneous Consumption and Best Time for Retirement, arXiv:2008.00392v2, pp. 6–7, 11–12, 18, (13), Assumption 18

import Mathlib

namespace HeteroRetire.Boundary

open Set

/-- The deterministic market coefficients and retirement horizons of §2, pp. 6–7,
and the market price of risk of (13), pp. 11–12. -/
structure Market (n : ℕ) where
  T : ℝ
  Tbar : ℝ
  r : ℝ → ℝ
  rho : ℝ → ℝ
  I : ℝ → ℝ
  L : ℝ → ℝ
  mu : ℝ → Fin n → ℝ
  sigma : ℝ → Matrix (Fin n) (Fin n) ℝ
  theta : ℝ → Fin n → ℝ

/-- Positivity, continuity and boundedness on the consumption horizon, p. 7. -/
def PosContBdd (f : ℝ → ℝ) (Tbar : ℝ) : Prop :=
  (∀ t ∈ Icc 0 Tbar, 0 < f t) ∧
  ContinuousOn f (Icc 0 Tbar) ∧
  BddAbove (f '' Icc 0 Tbar)

/-- The paper's standing assumptions, including σθ=μ from (13). -/
structure Market.Standing {n : ℕ} (M : Market n) : Prop where
  n_pos : 0 < n
  T_pos : 0 < M.T
  T_lt : M.T < M.Tbar
  r_regular : PosContBdd M.r M.Tbar
  rho_regular : PosContBdd M.rho M.Tbar
  I_regular : PosContBdd M.I M.Tbar
  L_regular : PosContBdd M.L M.Tbar
  mu_pos : ∀ t ∈ Icc 0 M.Tbar, ∀ i, 0 < M.mu t i
  mu_cont : ∀ i, ContinuousOn (fun t => M.mu t i) (Icc 0 M.Tbar)
  mu_bdd : ∀ i, BddAbove ((fun t => M.mu t i) '' Icc 0 M.Tbar)
  sigma_cont : ∀ i j, ContinuousOn (fun t => M.sigma t i j) (Icc 0 M.Tbar)
  elliptic : ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 M.Tbar, ∀ z : Fin n → ℝ,
    C⁻¹ * (∑ i, z i * z i) ≤
      (∑ i, z i * ((M.sigma t * (M.sigma t).transpose).mulVec z) i) ∧
      (∑ i, z i * ((M.sigma t * (M.sigma t).transpose).mulVec z) i) ≤
        C * (∑ i, z i * z i)
  theta_eq : ∀ t ∈ Icc 0 M.Tbar, (M.sigma t).mulVec (M.theta t) = M.mu t

/-- The variance rate of the scalar stochastic integral θᵀdB in (13). -/
def varianceRate {n : ℕ} (M : Market n) (t : ℝ) : ℝ :=
  ∑ i, (M.theta t i) ^ 2

/-- Assumption 18, p. 18. Derivatives within the aged interval make the displayed
ratios meaningful at its endpoints. -/
def Assumption18 {n : ℕ} (M : Market n) (ell : ℝ) (I' L' : ℝ → ℝ) : Prop :=
  0 < ell ∧ ell ≤ M.T ∧
  ∀ t ∈ Icc (M.T - ell) M.T,
    HasDerivWithinAt M.I (I' t) (Icc (M.T - ell) M.T) t ∧
    HasDerivWithinAt M.L (L' t) (Icc (M.T - ell) M.T) t ∧
    I' t / M.I t ≤ M.rho t ∧ M.rho t ≤ L' t / M.L t

/-- Correction to Theorem 19: the generator in (25) is time invariant on the
aged interval, as required by the time shift on p. 39. -/
def ConstOnAged {n : ℕ} (M : Market n) (ell : ℝ) : Prop :=
  ∃ a v : ℝ, ∀ t ∈ Icc (M.T - ell) M.T,
    M.rho t - M.r t = a ∧ varianceRate M t = v

end HeteroRetire.Boundary


