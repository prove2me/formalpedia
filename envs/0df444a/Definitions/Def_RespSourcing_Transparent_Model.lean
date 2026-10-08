-- Prove2me | Definitions.Def_RespSourcing_Transparent_Model
-- name    : RespSourcing_Transparent_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:42.175376+00:00
-- url     : https://prove2.me/theorems/78e63df3-93aa-48ff-8a46-60ed3d290c8d
-- title:
--   §3–§4, Table 2 — transparent sourcing parameters, strategies, and expected profits
-- statement:
--   A buyer serves a market of unit size using a responsible supplier with marginal cost $c_R$ and a risky supplier with lower marginal cost $c_{NR}$. A violation at the risky supplier occurs with probability $\phi$ and incurs fixed penalty $c_{VP}$. Every consumer has baseline valuation $v$; a fraction $\theta$ values responsible sourcing by an additional $r$, and a fraction $\alpha$ of that group exits after a violation. The standing ranges are $0\le\theta,\alpha,\phi\le1$ and $c_{NR}<c_R$. Write $\Delta=c_R-c_{NR}$.
--
--   The four strategies are low-cost (LC), dual (DS), responsible niche (RN), and responsible mass market (RM). Their expected profits are defined by Table 2:
--
--   $$\begin{aligned}
--   \Pi^{LC}&=(1-\alpha\phi)\theta(v-c_{NR})+(1-\theta)(v-c_{NR})-\phi c_{VP},\\
--   \Pi^{DS}&=(1-\alpha\phi)\theta(v+r-c_R)+(1-\theta)(v-c_{NR})-\phi c_{VP},\\
--   \Pi^{RN}&=\theta(v+r-c_R),\\
--   \Pi^{RM}&=v-c_R.
--   \end{aligned}$$
--
--   A strategy is optimal when its expected profit is at least that of every one of these four strategies; ties are permitted. These definitions fix the comparison model for Proposition 1 and can be reused for the paper's later results.
--
--   **Formalization Note** The record has no proof fields. The paper supplies no sign conditions on $v$, $r$, or $c_{VP}$, so the standing predicate adds none.
-- source:
--   Guo, Lee & Swinney, Responsible Sourcing in Supply Chains, Management Science 62(9) (2016), pp. 2725–2730, §3, §4, Table 2; https://doi.org/10.1287/mnsc.2015.2256

import Mathlib

namespace RespSourcing.Transparent

/-- The eight parameters of the transparent sourcing model. -/
structure Params where
  v : ℝ
  r : ℝ
  θ : ℝ
  α : ℝ
  φ : ℝ
  cR : ℝ
  cNR : ℝ
  cVP : ℝ

/-- The standing parameter ranges in Section 3. -/
def Params.Standing (p : Params) : Prop :=
  0 ≤ p.θ ∧ p.θ ≤ 1 ∧ 0 ≤ p.α ∧ p.α ≤ 1 ∧
    0 ≤ p.φ ∧ p.φ ≤ 1 ∧ p.cNR < p.cR

/-- The responsible supplier's marginal cost premium. -/
def Params.Δ (p : Params) : ℝ := p.cR - p.cNR

/-- Low cost, dual, responsible niche, and responsible mass market sourcing. -/
inductive Strategy | LC | DS | RN | RM
  deriving DecidableEq

instance : Fintype Strategy :=
  ⟨{.LC, .DS, .RN, .RM}, by intro s; cases s <;> simp⟩

/-- The four expected profits in Table 2. -/
def profit (p : Params) : Strategy → ℝ
  | .LC => (1 - p.α * p.φ) * p.θ * (p.v - p.cNR) +
      (1 - p.θ) * (p.v - p.cNR) - p.φ * p.cVP
  | .DS => (1 - p.α * p.φ) * p.θ * (p.v + p.r - p.cR) +
      (1 - p.θ) * (p.v - p.cNR) - p.φ * p.cVP
  | .RN => p.θ * (p.v + p.r - p.cR)
  | .RM => p.v - p.cR

/-- A strategy earns at least as much as each of the four strategies. -/
def IsOptimal (p : Params) (s : Strategy) : Prop :=
  ∀ t : Strategy, profit p t ≤ profit p s

end RespSourcing.Transparent


