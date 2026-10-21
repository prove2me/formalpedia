-- Prove2me | Definitions.Def_CapacityRights_Gatekeeper_Model
-- name    : CapacityRights_Gatekeeper_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:15.1834+00:00
-- url     : https://prove2.me/theorems/40f51eeb-f475-48a4-8e62-32ba2088f8d8
-- title:
--   Two-division stationary capacity and gatekeeper model
-- statement:
--   The model has two divisions and one stock of **fungible capacity**. The same joint probability law of the revenue shocks applies in every period; the shocks may be correlated across divisions. Division $i$ earns $R_i(q_i,\epsilon_i)-w_iq_i$ when it produces $q_i$ units. For installed capacity $k\ge 0$, production is chosen after the shocks, subject to $q_1,q_2\ge0$ and $q_1+q_2\le k$. The stand-alone maxima are $CM_i(k_i\mid w_i,\epsilon_i)$, and the maximum of the combined contribution margin is $CM(k\mid w,\epsilon)$.
--
--   The discount factor, annuity factor, user cost of capacity, and period-$t$ capital-charge coefficient are
--
--   $$
--   \gamma=(1+r)^{-1},\qquad A=\sum_{t=1}^{T}\gamma^t,\qquad c=v/A,\qquad z_t=d_t+r\left(1-\sum_{\tau=1}^{t-1}d_\tau\right).
--   $$
--
--   An annuity schedule has nonnegative depreciation fractions totaling one and $z_t=A^{-1}$ in every period. The efficient capacity $k^*$ is a maximizer over $k\ge0$ of $\sum_t\gamma^t\mathbb E[CM(k\mid w,\tilde\epsilon)]-vk$. The dedicated Division 1 capacity is defined by the corresponding stand-alone maximization. The output maxima are values of optimization problems, while predicates identify any maximizing output pair.
--
--   Under renegotiation, Division 1 receives share $\delta\in[0,1]$ of the trading surplus and Division 2 receives $1-\delta$. Their effective margins add to $CM$. A gatekeeper contract grants Division 2 rights to $k_2$ units in exchange for a fixed period payment $p$, with transfer price $TP_t=p+w_2q_{2t}$. Division 1 installs $k_1+k_2$ units and bears the capital charge on all of them. Its expected residual income and Division 2's expected profit are the period payoffs used in the best-response predicate. Efficient ex-post reallocation is represented by $CM$ in those payoffs.
--
--   **Formalization Note** The paper's concavity assumption is strengthened to strict concavity to support its uniqueness claims. Joint continuity, differentiability with continuous marginal revenue, compact shock support, make the value functions and their marginal values integrable on the supported probability law, so the real-valued expectations are well defined. A probability law replaces the paper's density functions. Output and capacity are nonnegative. The model uses one stationary law, so no separate independent time-indexed shocks are needed.
-- source:
--   Dutta & Reichelstein, Capacity Rights and Full Cost Transfer Pricing, CESifo Working Paper No. 7968 (November 2019), pp. 5–25 (PDF 8–28), §§2 and 4, equations (3), (10)–(16), (20)

import Mathlib

noncomputable section

namespace CapacityRights.Gatekeeper

open MeasureTheory

/-- Stationary two-division environment. The joint shock law permits correlation. -/
structure Env where
  μ : Measure (ℝ × ℝ)
  R1 : ℝ → ℝ → ℝ
  R2 : ℝ → ℝ → ℝ
  w1 : ℝ
  w2 : ℝ
  v : ℝ
  r : ℝ
  T : ℕ
  δ : ℝ
  a1 : ℝ
  b1 : ℝ
  a2 : ℝ
  b2 : ℝ

def shockBox (E : Env) : Set (ℝ × ℝ) :=
  Set.Icc E.a1 E.b1 ×ˢ Set.Icc E.a2 E.b2

def γ (E : Env) : ℝ := (1 + E.r)⁻¹

def annuityFactor (E : Env) : ℝ :=
  ∑ t ∈ Finset.Icc 1 E.T, γ E ^ t

def ucc (E : Env) : ℝ := E.v / annuityFactor E

def capCharge (E : Env) (d : ℕ → ℝ) (t : ℕ) : ℝ :=
  d t + E.r * (1 - ∑ τ ∈ Finset.Ico 1 t, d τ)

def IsAnnuity (E : Env) (d : ℕ → ℝ) : Prop :=
  (∀ t ∈ Finset.Icc 1 E.T, 0 ≤ d t) ∧
  (∑ t ∈ Finset.Icc 1 E.T, d t) = 1 ∧
  ∀ t ∈ Finset.Icc 1 E.T, capCharge E d t = (annuityFactor E)⁻¹

def margin1 (E : Env) (q e1 : ℝ) : ℝ := E.R1 q e1 - E.w1 * q

def margin2 (E : Env) (q e2 : ℝ) : ℝ := E.R2 q e2 - E.w2 * q

def CM1 (E : Env) (k e1 : ℝ) : ℝ :=
  sSup ((fun q => margin1 E q e1) '' Set.Icc 0 k)

def CM2 (E : Env) (k e2 : ℝ) : ℝ :=
  sSup ((fun q => margin2 E q e2) '' Set.Icc 0 k)

def CMtot (E : Env) (k : ℝ) (e : ℝ × ℝ) : ℝ :=
  sSup {x : ℝ | ∃ q1 q2 : ℝ, 0 ≤ q1 ∧ 0 ≤ q2 ∧ q1 + q2 ≤ k ∧
    x = margin1 E q1 e.1 + margin2 E q2 e.2}

def IsSoloOpt1 (E : Env) (k e1 q : ℝ) : Prop :=
  q ∈ Set.Icc 0 k ∧ margin1 E q e1 = CM1 E k e1

def IsJointOpt (E : Env) (k : ℝ) (e : ℝ × ℝ) (q1 q2 : ℝ) : Prop :=
  0 ≤ q1 ∧ 0 ≤ q2 ∧ q1 + q2 ≤ k ∧
  margin1 E q1 e.1 + margin2 E q2 e.2 = CMtot E k e

def marginal1 (E : Env) (k e1 : ℝ) : ℝ := derivWithin (fun x => CM1 E x e1) (Set.Ici 0) k

def S (E : Env) (k : ℝ) (e : ℝ × ℝ) : ℝ := derivWithin (fun x => CMtot E x e) (Set.Ici 0) k

def NPV (E : Env) (k : ℝ) : ℝ :=
  (∑ t ∈ Finset.Icc 1 E.T, γ E ^ t * ∫ e, CMtot E k e ∂E.μ) - E.v * k

def NPVded1 (E : Env) (k : ℝ) : ℝ :=
  (∑ t ∈ Finset.Icc 1 E.T, γ E ^ t * ∫ e, CM1 E k e.1 ∂E.μ) - E.v * k

def IsEfficient (E : Env) (k : ℝ) : Prop :=
  0 ≤ k ∧ ∀ k' : ℝ, 0 ≤ k' → NPV E k' ≤ NPV E k

def IsEfficientDed1 (E : Env) (k : ℝ) : Prop :=
  0 ≤ k ∧ ∀ k' : ℝ, 0 ≤ k' → NPVded1 E k' ≤ NPVded1 E k

def CMeff1 (E : Env) (k1 k2 : ℝ) (e : ℝ × ℝ) : ℝ :=
  (1 - E.δ) * CM1 E k1 e.1 + E.δ * (CMtot E (k1 + k2) e - CM2 E k2 e.2)

def CMeff2 (E : Env) (k1 k2 : ℝ) (e : ℝ × ℝ) : ℝ :=
  E.δ * CM2 E k2 e.2 + (1 - E.δ) * (CMtot E (k1 + k2) e - CM1 E k1 e.1)

def transferPrice (E : Env) (_k2 p q2 : ℝ) : ℝ := p + E.w2 * q2

def RI1 (E : Env) (d : ℕ → ℝ) (t : ℕ) (k1 k2 p : ℝ) : ℝ :=
  (∫ e, CMeff1 E k1 k2 e ∂E.μ) - capCharge E d t * E.v * (k1 + k2) + p

def Profit2 (E : Env) (k1 k2 p : ℝ) : ℝ :=
  (∫ e, CMeff2 E k1 k2 e ∂E.μ) - p

def IsBestResponse1 (E : Env) (d : ℕ → ℝ) (t : ℕ) (k2 p k1 : ℝ) : Prop :=
  0 ≤ k1 ∧ ∀ k1' : ℝ, 0 ≤ k1' → RI1 E d t k1' k2 p ≤ RI1 E d t k1 k2 p

def Env.Standing (E : Env) : Prop :=
  IsProbabilityMeasure E.μ ∧
  E.μ (shockBox E)ᶜ = 0 ∧
  E.a1 ≤ E.b1 ∧ E.a2 ≤ E.b2 ∧
  0 < E.v ∧ 0 ≤ E.r ∧ 1 ≤ E.T ∧ 0 ≤ E.δ ∧ E.δ ≤ 1 ∧
  Continuous (fun p : ℝ × ℝ => E.R1 p.1 p.2) ∧
  Continuous (fun p : ℝ × ℝ => E.R2 p.1 p.2) ∧
  Continuous (fun p : ℝ × ℝ => deriv (fun q => E.R1 q p.2) p.1) ∧
  Continuous (fun p : ℝ × ℝ => deriv (fun q => E.R2 q p.2) p.1) ∧
  (∀ e ∈ Set.Icc E.a1 E.b1,
    MonotoneOn (fun q => E.R1 q e) (Set.Ici 0) ∧
    StrictConcaveOn ℝ (Set.Ici 0) (fun q => E.R1 q e) ∧
    Differentiable ℝ (fun q => E.R1 q e) ∧
    E.w1 < deriv (fun q => E.R1 q e) 0) ∧
  (∀ e ∈ Set.Icc E.a2 E.b2,
    MonotoneOn (fun q => E.R2 q e) (Set.Ici 0) ∧
    StrictConcaveOn ℝ (Set.Ici 0) (fun q => E.R2 q e) ∧
    Differentiable ℝ (fun q => E.R2 q e) ∧
    E.w2 < deriv (fun q => E.R2 q e) 0) ∧
  (∀ q ≥ (0 : ℝ), MonotoneOn (fun e => deriv (fun x => E.R1 x e) q) (Set.Icc E.a1 E.b1)) ∧
  (∀ q ≥ (0 : ℝ), MonotoneOn (fun e => deriv (fun x => E.R2 x e) q) (Set.Icc E.a2 E.b2))

end CapacityRights.Gatekeeper


