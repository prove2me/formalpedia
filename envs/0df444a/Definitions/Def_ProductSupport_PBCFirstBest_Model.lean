-- Prove2me | Definitions.Def_ProductSupport_PBCFirstBest_Model
-- name    : ProductSupport_PBCFirstBest_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:47.160658+00:00
-- url     : https://prove2.me/theorems/4bc530fa-e6c8-4e0f-8401-e7a11477febb
-- title:
--   §3–§5.2 — two-type performance-based product-support model
-- statement:
--   The model has two customer types, with failure rates $0<\lambda_L<\lambda_H$, reservation payoffs $0<M_H<M_L$, and prior probabilities $\beta$ and $1-\beta$. A supplier chooses an uptime price $v$ and repair rate $\mu$. Revenue per unit uptime is $r>0$, capacity costs $c\mu$ with $c>0$, and expected materials cost is $c_r\lambda$ with $c_r\geq0$.
--
--   For a type with failure rate $\lambda$, the expected uptime and the two payoffs are
--   $$
--   A(\lambda,\mu)=1-\frac{\lambda}{\mu},\qquad
--   \pi_c^P=(r-v)A(\lambda,\mu),\qquad
--   \pi_s^P=vA(\lambda,\mu)-c_r\lambda-c\mu.
--   $$
--   A menu specifies one contract for each type. It is feasible when all four prices and repair rates are strictly positive, each customer's own-contract payoff reaches her reservation payoff, and neither type gains by taking the other's contract. The supplier maximizes the prior-weighted sum of her two type-specific payoffs.
--
--   The first-best repair rate is $\mu^0_\tau=\sqrt{r\lambda_\tau/c}$, its binding-IR price is $v^0_\tau=r-M_\tau\mu^0_\tau/(\mu^0_\tau-\lambda_\tau)$, and $\Pi^0_\tau$ denotes joint profit at that rate. Condition (10) compares $M_L/M_H$ with two ratios of first-best rates.
--
--   **Formalization Note** Payoffs use the paper's closed-form expectation in (B.39). Division is only interpreted under the positive-rate and nonzero-denominator hypotheses of the theorems that use it. The standing predicate includes $M_H>0$ to give condition (10) its intended domain.
-- source:
--   Li, Mishra & Netessine, Contracting for Product Support under Information Asymmetry, SSRN 2881356 (author version of Management Science, doi:10.1287/mnsc.2022.4606), pp. 7–18 (PDF 7–18), §§3–5.2, problems (2) and (9); supplement p. 9 (PDF 42), (B.39)

import Mathlib

namespace ProductSupport.PBCFirstBest

noncomputable section

structure Params where
  r : ℝ
  c : ℝ
  cr : ℝ
  lamL : ℝ
  lamH : ℝ
  β : ℝ
  ML : ℝ
  MH : ℝ

def Params.Standing (P : Params) : Prop :=
  0 < P.r ∧ 0 < P.c ∧ 0 ≤ P.cr ∧ 0 < P.lamL ∧ P.lamL < P.lamH ∧
  0 < P.β ∧ P.β < 1 ∧ 0 < P.MH ∧ P.MH < P.ML

def uptime (lam mu : ℝ) : ℝ := 1 - lam / mu

structure Contract where
  v : ℝ
  mu : ℝ

def custPayoff (P : Params) (lam : ℝ) (k : Contract) : ℝ :=
  (P.r - k.v) * uptime lam k.mu

def suppPayoff (P : Params) (lam : ℝ) (k : Contract) : ℝ :=
  k.v * uptime lam k.mu - P.cr * lam - P.c * k.mu

def scProfit (P : Params) (lam mu : ℝ) : ℝ :=
  P.r * uptime lam mu - P.cr * lam - P.c * mu

structure Menu where
  L : Contract
  H : Contract

def Menu.Feasible (P : Params) (m : Menu) : Prop :=
  0 < m.L.v ∧ 0 < m.L.mu ∧ 0 < m.H.v ∧ 0 < m.H.mu ∧
  P.ML ≤ custPayoff P P.lamL m.L ∧
  P.MH ≤ custPayoff P P.lamH m.H ∧
  custPayoff P P.lamL m.H ≤ custPayoff P P.lamL m.L ∧
  custPayoff P P.lamH m.L ≤ custPayoff P P.lamH m.H

def objective (P : Params) (m : Menu) : ℝ :=
  P.β * suppPayoff P P.lamL m.L +
  (1 - P.β) * suppPayoff P P.lamH m.H

def mu0 (P : Params) (lam : ℝ) : ℝ := Real.sqrt (P.r * lam / P.c)

def vBinding (P : Params) (lam M mu : ℝ) : ℝ :=
  P.r + M * mu / (lam - mu)

def v0 (P : Params) (lam M : ℝ) : ℝ :=
  P.r - M * mu0 P lam / (mu0 P lam - lam)

def Pi0 (P : Params) (lam : ℝ) : ℝ := scProfit P lam (mu0 P lam)

def fbMenu (P : Params) : Menu :=
  ⟨⟨v0 P P.lamL P.ML, mu0 P P.lamL⟩,
   ⟨v0 P P.lamH P.MH, mu0 P P.lamH⟩⟩

def Cond10 (P : Params) : Prop :=
  (mu0 P P.lamH - P.lamL) / (mu0 P P.lamH - P.lamH) ≤ P.ML / P.MH ∧
  P.ML / P.MH ≤ (mu0 P P.lamL - P.lamL) / (mu0 P P.lamL - P.lamH)

end

end ProductSupport.PBCFirstBest


