-- Prove2me | Definitions.Def_FreePlayPremium_OptimalPolicies_Problem
-- name    : FreePlayPremium_OptimalPolicies_Problem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:28:03.196958+00:00
-- url     : https://prove2.me/theorems/45e48932-09f3-4067-bea7-7d48e733d847
-- title:
--   Problem (3): population dynamics, extended profit and global optimality
-- statement:
--   A problem has player parameters, horizon $T$, discount rate $r$, and advertising cost $C$. Its validity requires valid player parameters with $d\ne u$, $T>0$, $r\ge0$, and the stated advertising-cost conditions. The generic control system has state domain $[0,1]$, initial state zero, and controls $(a,p)\in[0,\infty)^2$. Write $R(p)=S(p)p$ and $B(p)=v+S(p)(1-S(p))(d-u)-S(p)p$. Its drift is
--   $$f(n,a,p)=(a+B(p)n-1)(1-n),$$
--   including $f(0,a,p)=a-1$. A feasible policy is an admissible integral trajectory with integrable discounted revenue and measurable discounted incremental cost. These guards are automatic from the model assumptions; infinite advertising expenditure remains allowed.
--   Define its extended profit by
--   $$J=\int_0^T[n(t)R(p(t))-C(0)]e^{-rt}\,dt-\int_0^T[C(a(t))-C(0)]e^{-rt}\,dt.$$
--   The second integral is the extended nonnegative Lebesgue integral, coerced into the extended reals. Since increasing $C$ makes its integrand nonnegative, this agrees with the original profit when finite and assigns $-\infty$ to infinite expenditure. Global optimality means feasibility and $J(z)\le J(q)$ for every feasible control/trajectory triple $z$. No co-state or path-shape assumption is included. Payment activity means $S(p)p>0$, so a free premium offer does not count as introduction of paid subscription.
-- source:
--   Mai and Hu (2022), Optimizing Free-to-Play Multiplayer Games with Premium Subscription, Management Science, https://doi.org/10.1287/mnsc.2022.4510, Eqs. (1)–(3), printed pp. 7, 9, 13–14 (PDF pp. 7, 9, 13–14); expanded drift Eq. (5), printed p. 34 (PDF p. 34)

import Definitions.Def_FreePlayPremium_OptimalPolicies_ScalarControl
import Definitions.Def_FreePlayPremium_OptimalPolicies_Players
import Definitions.Def_FreePlayPremium_OptimalPolicies_AdvertisingCost

open MeasureTheory Set

namespace FreePlayPremium.OptimalPolicies

/-- Problem (3) data; admissibility and parameter hypotheses are separate. -/
structure Problem where
  players : PlayerParameters
  horizon : ℝ
  discount : ℝ
  cost : ℝ → ℝ

def Problem.Valid (M : Problem) : Prop :=
  M.players.Valid ∧ M.players.down ≠ M.players.up ∧
  0 < M.horizon ∧ 0 ≤ M.discount ∧ AdvertisingCost M.cost

/-- The nonsingular state drift, Eq. (5), including the value a-1 at zero. -/
noncomputable def Problem.system (M : Problem) : ScalarControlSystem where
  horizon := M.horizon
  initial := 0
  states := Icc 0 1
  controls := {u | 0 ≤ u.1 ∧ 0 ≤ u.2}
  drift := fun n u =>
    (u.1 + averageUtilityWithoutFriction M.players (premiumShare M.players u.2) u.2 * n - 1) * (1 - n)

def ControlPath.advertising (q : ControlPath) (t : ℝ) : ℝ := (q.control t).1

def ControlPath.price (q : ControlPath) (t : ℝ) : ℝ := (q.control t).2

/-- Payment per active player: zero includes a free premium offer. -/
noncomputable def payment (P : PlayerParameters) (p : ℝ) : ℝ := premiumShare P p * p

noncomputable def Problem.discountedRevenue (M : Problem) (q : ControlPath) (t : ℝ) : ℝ :=
  q.state t * payment M.players (q.price t) * Real.exp (-M.discount * t)

/-- Subtracting C(0) makes expenditure nonnegative without assuming C(0)=0. -/
noncomputable def Problem.incrementalCost (M : Problem) (q : ControlPath) (t : ℝ) : ℝ :=
  (M.cost (q.advertising t) - M.cost 0) * Real.exp (-M.discount * t)

/-- Revenue integrability and cost measurability are automatic for the source data,
but explicit here to guard the integral conventions. Infinite expenditure is allowed. -/
def Problem.Feasible (M : Problem) (q : ControlPath) : Prop :=
  M.system.Admissible q ∧
  IntegrableOn (M.discountedRevenue q) (Icc 0 M.horizon) ∧
  AEMeasurable (M.incrementalCost q) (volume.restrict (Icc 0 M.horizon))

/-- Finite revenue minus the finite baseline cost and the extended nonnegative
incremental expenditure. Infinite expenditure gives minus infinity, never zero. -/
noncomputable def Problem.profit (M : Problem) (q : ControlPath) : EReal :=
  ((∫ t in Icc 0 M.horizon, M.discountedRevenue q t -
    M.cost 0 * Real.exp (-M.discount * t)) : ℝ) -
  ((∫⁻ t in Icc 0 M.horizon, ENNReal.ofReal (M.incrementalCost q t)) : EReal)

/-- Global maximization against every feasible policy, with no shape restriction. -/
def Problem.GloballyOptimal (M : Problem) (q : ControlPath) : Prop :=
  M.Feasible q ∧ ∀ z : ControlPath, M.Feasible z → M.profit z ≤ M.profit q

end FreePlayPremium.OptimalPolicies


