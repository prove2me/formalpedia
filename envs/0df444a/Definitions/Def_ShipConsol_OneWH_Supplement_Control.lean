-- Prove2me | Definitions.Def_ShipConsol_OneWH_Supplement_Control
-- name    : ShipConsol_OneWH_Supplement_Control
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:25:06.146016+00:00
-- url     : https://prove2.me/theorems/4a8b7d17-b299-4e20-b58f-67fba141a397
-- title:
--   DP (1), pp. 10–11 — finite-scenario control, policy evaluation and reachability
-- statement:
--   A finite-scenario cost control model has a state space S, an action space A, a finite disturbance space E, state- and time-dependent finite feasible action sets, a current cost c(s,a), a transition q(s,a,e), and disturbance weights p(e). For shipping instances these weights are nonnegative and sum to one, and the feasible sets are nonempty. Period t counts periods remaining. Define
--
--   $$V_0(s)=J_0^\pi(s)=0,\quad V_t(s)=\min_{a\in A_t(s)}\{c(s,a)+\sum_e p(e)V_{t-1}(q(s,a,e))\},$$
--   $$J_t^\pi(s)=c(s,\pi_t(s))+\sum_e p(e)J_{t-1}^\pi(q(s,\pi_t(s),e)).$$
--
--   Bellman optimality requires feasibility and attainment of this minimum. Reachability starts from the specified initial state and follows positive-probability disturbances under the selected policy. This reusable finite-scenario evaluator is separate from the shipping data; it assumes no threshold or all-or-none property. Its empty-action default zero is unused by the shipping instances.
-- source:
--   Wei, Kapuscinski & Jasin, Shipping Consolidation across Two Warehouses with Delivery Deadline and Expedited Options for E-commerce and Omni-channel Retailers, author's manuscript, SSRN 2920899 (M&SOM 2020, doi:10.1287/msom.2020.0903), pinned PDF sha256 2cc7647135cddd3db3d07ad21c65ac52502947d2dde5f337f3ab9948547f0a03, DP (1), pp. 10–11; footnote 24, p. 22

import Mathlib

namespace ShipConsol.OneWH.Supplement

/-- A finite-disturbance, finite-action cost control model. The state type need not be finite.
Time is periods remaining; all feasible action sets used below are nonempty. -/
structure ScenarioControl (S A E : Type) [Fintype E] where
  actions : ℕ → S → Finset A
  cost : S → A → ℝ
  next : S → A → E → S
  weight : E → ℝ

noncomputable def finiteMin {A : Type} (as : Finset A) (f : A → ℝ) : ℝ :=
  if h : as.Nonempty then as.inf' h f else 0

namespace ScenarioControl
variable {S A E : Type} [Fintype E]

noncomputable def value (M : ScenarioControl S A E) : ℕ → S → ℝ
  | 0, _ => 0
  | t + 1, s => finiteMin (M.actions (t + 1) s) fun a =>
      M.cost s a + ∑ e, M.weight e * value M t (M.next s a e)

noncomputable def evaluate (M : ScenarioControl S A E) (π : ℕ → S → A) : ℕ → S → ℝ
  | 0, _ => 0
  | t + 1, s => M.cost s (π (t + 1) s) +
      ∑ e, M.weight e * evaluate M π t (M.next s (π (t + 1) s) e)

def BellmanOptimal (M : ScenarioControl S A E) (t : ℕ) (s : S) (a : A) : Prop :=
  a ∈ M.actions t s ∧
    M.cost s a + (∑ e, M.weight e * M.value (t - 1) (M.next s a e)) = M.value t s

inductive Reachable (M : ScenarioControl S A E) (π : ℕ → S → A) (T : ℕ) (initial : S) :
    ℕ → S → Prop
  | initial : Reachable M π T initial T initial
  | step {t : ℕ} {s : S} (hs : Reachable M π T initial (t + 1) s)
      (ht : 1 ≤ t) (e : E) (he : 0 < M.weight e) :
      Reachable M π T initial t (M.next s (π (t + 1) s) e)

end ScenarioControl
end ShipConsol.OneWH.Supplement


