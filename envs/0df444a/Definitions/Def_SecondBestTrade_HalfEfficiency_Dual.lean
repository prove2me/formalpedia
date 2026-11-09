-- Prove2me | Definitions.Def_SecondBestTrade_HalfEfficiency_Dual
-- name    : SecondBestTrade_HalfEfficiency_Dual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:46.323146+00:00
-- url     : https://prove2.me/theorems/93da2e9b-893f-4959-93fa-97a4dbed5e14
-- title:
--   Definitions 5.1–5.2 and §5.2 — Flows, virtual types and generators
-- statement:
--   A multiplier vector $z=(\tau,\alpha,\beta)$ has $\tau\ge0$ and nonnegative flows from support types to support types or a separate null report. Write $\operatorname{out}_a(t)$ and $\operatorname{in}_a(t)$ for outgoing and incoming flow, including self flow in both. Usefulness means
--   $$\operatorname{out}_a(t)=\tau f_a(t)+\operatorname{in}_a(t).$$
--   For any nonnegative multiplier vector, an incident virtual coordinate is
--   $$\widetilde t_e=t_e-\frac{\sum_s\alpha_a(s,t)(s_e-t_e)}{(1+\tau)f_a(t)}.$$
--   The same minus-sign formula applies to seller costs. The off-diagonal generator is $Q_a(t,s)=\alpha_a(s,t)/((1+\tau)f_a(t))$ and the diagonal is minus the sum of its other row entries. Define $K_a(\theta)=\exp(\theta Q_a)$, $R_a=(I-Q_a)^{-1}$, $\kappa=\tau/(1+\tau)$, maximum virtual surplus $\widetilde H$, and $D(z)=(1+\tau)\mathbb E_\pi\widetilde H$.
--
--   The fixed-clock terminal law of agent $a$ is $f_aK_a(\theta)$; `conditionalSurplus` averages virtual surplus under the product of these laws using a shared buyer clock and a shared seller clock. These formulas compute the paper's dual objects without assuming usefulness, stochasticity, invertibility, recovery, density bounds or duality. Denominators are strictly positive by the market and multiplier domains.
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), Definitions 5.1–5.2, (5.2)–(5.8), §7, printed pp. 7–10, 13 (PDF pp. 8–11, 14)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Mechanisms

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Nonnegative multipliers, without usefulness built into the data. -/
structure Dual (N : Market) where
  tau : ℝ≥0
  flow : ∀ a, Ty N a → Option (Ty N a) → ℝ≥0

def outflow (N : Market) (z : Dual N) (a : Agent N) (t : Ty N a) : ℝ :=
  ∑ r, (z.flow a t r : ℝ)
def inflow (N : Market) (z : Dual N) (a : Agent N) (t : Ty N a) : ℝ :=
  ∑ s, (z.flow a s (some t) : ℝ)
def useful (N : Market) (z : Dual N) : Prop :=
  ∀ a t, outflow N z a t = (z.tau : ℝ) * N.mass a t + inflow N z a t

def virtual (N : Market) (z : Dual N) (a : Agent N) (t : Ty N a) (e : Trade N) : ℝ :=
  coord N a t e - (∑ s, (z.flow a s (some t) : ℝ) *
    (coord N a s e - coord N a t e)) / ((1 + (z.tau : ℝ)) * N.mass a t)
def virtualGain (N : Market) (z : Dual N) (v : Profile N) (e : Trade N) : ℝ :=
  virtual N z (.inl (N.buyer e)) (v (.inl (N.buyer e))) e -
    virtual N z (.inr (N.seller e)) (v (.inr (N.seller e))) e

def Hvirtual (N : Market) (z : Dual N) (v : Profile N) : ℝ :=
  maxSurplus N (virtualGain N z v)
def dualObjective (N : Market) (z : Dual N) : ℝ :=
  (1 + (z.tau : ℝ)) * expect N (Hvirtual N z)
def kappa (tau : ℝ) : ℝ := tau / (1 + tau)

noncomputable def generator (N : Market) (z : Dual N) (a : Agent N) :
    Matrix (Ty N a) (Ty N a) ℝ := by
  classical
  let rate := fun t s => (z.flow a s (some t) : ℝ) /
    ((1 + (z.tau : ℝ)) * N.mass a t)
  exact fun t s => if t = s then -(∑ r ∈ Finset.univ.erase t, rate t r) else rate t s

def transition (N : Market) (z : Dual N) (a : Agent N) (theta : ℝ) :
    Matrix (Ty N a) (Ty N a) ℝ := NormedSpace.exp (theta • generator N z a)
noncomputable def resolvent (N : Market) (z : Dual N) (a : Agent N) :
    Matrix (Ty N a) (Ty N a) ℝ := (1 - generator N z a)⁻¹

def terminalMass (N : Market) (z : Dual N) (a : Agent N) (theta : ℝ) (t : Ty N a) : ℝ :=
  ∑ s, N.mass a s * transition N z a theta s t

def conditionalSurplus (N : Market) (z : Dual N) (thetaB thetaS : ℝ) : ℝ :=
  ∑ v : Profile N,
    (∏ a, terminalMass N z a (Sum.elim (fun _ => thetaB) (fun _ => thetaS) a) (v a)) *
      Hvirtual N z v

end SecondBestTrade.HalfEfficiency


