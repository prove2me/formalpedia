-- Prove2me | Definitions.Def_FinMarkup_Wedge_Model
-- name    : FinMarkup_Wedge_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T20:37:58.264296+00:00
-- url     : https://prove2.me/theorems/b0935062-ba66-45db-99b3-eec1d3fbe173
-- title:
--   §2 and Appendix A.1 — firm demand, customer and cash drifts, pricing objective, markup and wedge
-- statement:
--   Fix one firm at one instant. Let $\eta$ be its within-industry demand elasticity, $\epsilon$ the industry elasticity, $\beta$ its customer-accumulation rate, $\rho$ customer-base depreciation, $A$ productivity, $R$ the rental rate of capital, $r$ the risk-free rate, and $\lambda$ the cash-carrying cost. At a firm price $P>0$, industry price index $P_t>0$, customer base $M>0$, and cash balance $W$, demand is
--
--   $$C(P)=M(P/P_t)^{-\eta}P_t^{-\epsilon}.$$
--
--   The expected customer-base and cash drifts per unit time in the liquidity-hoarding region are
--
--   $$g_M(P)=\beta C(P)-\rho M,\qquad g_W(P)=(P-R/A)P^{-\eta}P_t^{\eta-\epsilon}M+(r-\lambda)W.$$
--
--   Given marginal values $\mu$ of customer base and $\nu$ of liquidity, the price-dependent Hamiltonian is $H(P)=\mu g_M(P)+\nu g_W(P)$. A price is optimal when it globally maximizes $H$ over positive prices. The price-to-marginal-cost markup and its wedge are
--
--   $$\Lambda(P)=\frac{P}{R/A},\qquad \Omega=\frac{\beta A}{R}\frac{\mu}{\nu}.$$
--
--   These definitions isolate the pricing part of the firm's dynamic problem and are shared by the proposition and the appendix milestones.
--
--   **Formalization Note** The model is evaluated for one firm and one instant, treating $P_t,M,W,\mu,\nu$ as given reals. It records the deterministic expected drifts per unit time; Brownian noise and the separate payout control are absent from the price objective. The standing predicate requires $1<\epsilon<\eta$, $\beta\ge0$, $A>0$, and $R>0$. Demand and markup have their intended interpretation only at positive prices; later statements impose $P,P_t,M>0$ and $\nu>0$ where needed.
-- source:
--   Dou & Ji, External Financing and Customer Capital: A Financial Theory of Markups, SSRN 2574953 (version of May 11, 2020), pp. 6–10 (PDF 7–11), (2.4), (2.5), (2.7), (2.9)–(2.11), (3.2), and p. 33 (PDF 34), (A.1), (A.3)

import Mathlib

namespace FinMarkup.Wedge

/-- Parameters of the monopolistically competitive firm in Section 2. -/
structure Params where
  eta : ℝ
  eps : ℝ
  beta : ℝ
  rho : ℝ
  A : ℝ
  R : ℝ
  r : ℝ
  lam : ℝ

/-- Elasticities, customer accumulation, productivity, and rental cost. -/
def Params.Standing (m : Params) : Prop :=
  1 < m.eps ∧ m.eps < m.eta ∧ 0 ≤ m.beta ∧ 0 < m.A ∧ 0 < m.R

/-- (2.4): demand for one firm's product at positive prices. -/
noncomputable def demand (m : Params) (Pt M p : ℝ) : ℝ :=
  M * (p / Pt) ^ (-m.eta) * Pt ^ (-m.eps)

/-- (A.1): expected customer-base drift per unit time. -/
noncomputable def driftM (m : Params) (Pt M p : ℝ) : ℝ :=
  m.beta * demand m Pt M p - m.rho * M

/-- (A.3): expected cash drift per unit time in the liquidity-hoarding region. -/
noncomputable def driftW (m : Params) (Pt M W p : ℝ) : ℝ :=
  (p - m.R / m.A) * p ^ (-m.eta) * Pt ^ (m.eta - m.eps) * M +
    (m.r - m.lam) * W

/-- The price-dependent part of the firm's HJB objective, using the marginal values
of customer base and liquidity as weights. -/
noncomputable def hamiltonian (m : Params) (Pt M W mu nu p : ℝ) : ℝ :=
  mu * driftM m Pt M p + nu * driftW m Pt M W p

/-- A price is globally optimal among positive prices. -/
def IsOptimalPrice (m : Params) (Pt M W mu nu p : ℝ) : Prop :=
  0 < p ∧ ∀ p' : ℝ, 0 < p' →
    hamiltonian m Pt M W mu nu p' ≤ hamiltonian m Pt M W mu nu p

/-- (2.7): the ratio of price to marginal cost. -/
noncomputable def markup (m : Params) (p : ℝ) : ℝ := p / (m.R / m.A)

/-- (3.2): the markup wedge, with the ratio `mu / nu`. -/
noncomputable def wedge (m : Params) (mu nu : ℝ) : ℝ :=
  m.beta * m.A / m.R * (mu / nu)

end FinMarkup.Wedge


