-- Prove2me | Definitions.Def_QualityEncroach_FixedCost_Game
-- name    : QualityEncroach_FixedCost_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:02.123576+00:00
-- url     : https://prove2.me/theorems/d1549add-d4fb-4811-b703-7dcff82d5709
-- title:
--   §3.1 and §6.2, pp. 8, 20 — fixed-cost three-stage encroachment game
-- statement:
--   The manufacturer chooses wholesale price $w\in\mathbb R$, direct quality $u>0$, and retail-to-direct quality ratio $t>0$. The retailer then orders $q_R\ge0$, and the manufacturer chooses direct quantity $q_M\ge0$. Given the market-clearing prices $p_M,p_R$, their payoffs are
--
--   $$
--   \Pi_M=wq_R+(p_M-c)q_M-\max\{ku^2,k(tu)^2\},\qquad
--   \Pi_R=(p_R-w)q_R.
--   $$
--
--   The manufacturer pays $c\ge0$ per direct-channel unit and the fixed quality cost once. A strategy profile specifies actions after every possible observed history. Subgame perfection means each action is feasible and maximizes the mover's payoff, taking the profile's later actions into account.
--
--   This game supplies the equilibrium object for Proposition 6(i).
--
--   **Formalization Note** The order and direct rules are total functions, but optimality is required at every feasible history, on or off the path. The wholesale price is unrestricted, and inverse demand is used algebraically for nonnegative quantities.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, pp. 8, 20, §3.1 and §6.2

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Game

namespace QualityEncroach.FixedCost
noncomputable section

/-- The manufacturer pays `max (k*u²) (k*(t*u)²)` once, independently of sales,
and pays `c` for each direct-channel unit (§6.2, p. 20). -/
def mfrPayoff (k c : ℝ) (o : QualityEncroach.Differ.Outcome) : ℝ :=
  o.w * o.qR + (QualityEncroach.Differ.priceM o.u o.t o.qM o.qR - c) * o.qM -
    max (k * o.u ^ 2) (k * (o.t * o.u) ^ 2)

/-- Complete contingent strategies: the retailer sees `(w,u,t)` and the
manufacturer then sees `(w,u,t,qR)` (pp. 8, 20). -/
structure Profile where
  w : ℝ
  u : ℝ
  t : ℝ
  order : ℝ → ℝ → ℝ → ℝ
  direct : ℝ → ℝ → ℝ → ℝ → ℝ

def Profile.outcomeAtDirect (σ : Profile) (w u t qR : ℝ) : QualityEncroach.Differ.Outcome :=
  ⟨w, u, t, qR, σ.direct w u t qR⟩

def Profile.outcomeAtOrder (σ : Profile) (w u t : ℝ) : QualityEncroach.Differ.Outcome :=
  σ.outcomeAtDirect w u t (σ.order w u t)

def Profile.path (σ : Profile) : QualityEncroach.Differ.Outcome :=
  σ.outcomeAtOrder σ.w σ.u σ.t

/-- One-shot-deviation formulation of subgame perfection at every feasible
history, including histories off the path (pp. 8, 36). -/
structure IsSPE (k c : ℝ) (σ : Profile) : Prop where
  direct_nonneg : ∀ w u t qR : ℝ, 0 < u → 0 < t → 0 ≤ qR →
    0 ≤ σ.direct w u t qR
  direct_optimal : ∀ w u t qR qM : ℝ, 0 < u → 0 < t → 0 ≤ qR → 0 ≤ qM →
    mfrPayoff k c ⟨w, u, t, qR, qM⟩ ≤
      mfrPayoff k c (σ.outcomeAtDirect w u t qR)
  order_nonneg : ∀ w u t : ℝ, 0 < u → 0 < t → 0 ≤ σ.order w u t
  order_optimal : ∀ w u t qR : ℝ, 0 < u → 0 < t → 0 ≤ qR →
    QualityEncroach.Differ.retailerPayoff (σ.outcomeAtDirect w u t qR) ≤
      QualityEncroach.Differ.retailerPayoff (σ.outcomeAtOrder w u t)
  u_pos : 0 < σ.u
  t_pos : 0 < σ.t
  first_optimal : ∀ w u t : ℝ, 0 < u → 0 < t →
    mfrPayoff k c (σ.outcomeAtOrder w u t) ≤ mfrPayoff k c σ.path

end
end QualityEncroach.FixedCost


