-- Prove2me | Definitions.Def_CalibeatBandit_lower_bound_models
-- name    : CalibeatBandit_lower_bound_models
-- status  : Definition
-- author  : @jasonhartline
-- created : 2026-11-15T14:13:11.072925+00:00
-- url     : https://prove2.me/theorems/50c5dbba-be5e-406f-a2e9-2d6ec81f479d
-- title:
--   Calibeating lower bounds: bandit histories and pricing benchmarks
-- statement:
--   A bandit history is the finite sequence of scalar rewards observed by a deterministic policy once its private seed is fixed. A pricing history records posted prices and observed revenues. Prices lie in the unit interval, demand is nonincreasing, and the benchmark maximizes cumulative payoff improvement over measurable remappings of reference prices.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice, STOC 2027 submission 1457, Sections 4 and 5

import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace CalibeatBandit

/-- The reward transcript before a round. The action at a fixed private seed
can be reconstructed from the previous observations. -/
def FeedbackHistory : ℕ → Type
  | 0 => Unit
  | t + 1 => FeedbackHistory t × ℝ

instance feedbackHistoryMeasurable (t : ℕ) : MeasurableSpace (FeedbackHistory t) :=
  match t with
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | t + 1 => @MeasurableSpace.prod (FeedbackHistory t) ℝ (feedbackHistoryMeasurable t) inferInstance

/-- A fixed private seed leaves a deterministic policy whose transcript
is obtained by feeding back one observed reward per round. -/
def feedbackHistory {A : Type*} (pick : (t : ℕ) → FeedbackHistory t → A) (y : ℕ → A → ℝ) :
    (t : ℕ) → FeedbackHistory t
  | 0 => ()
  | t + 1 =>
    let h := feedbackHistory pick y t
    (h, y t (pick t h))

end CalibeatBandit

namespace CalibeatBandit.Pricing

abbrev Price := Set.Icc (0 : ℝ) 1

structure Demand where
  toFun : Price → Price
  antitone : Antitone toFun

instance : CoeFun Demand (fun _ => Price → Price) := ⟨Demand.toFun⟩

def revenue (cost : Price) (demand : Demand) (p : Price) : ℝ :=
  ((p : ℝ) - cost) * demand p

/-- The best cumulative payoff improvement obtained by a measurable remapping
of the reference prices. Use the posted prices as the reference for swap regret
and the recommended prices for recommendation loss. -/
noncomputable def benchmark (T : ℕ) (cost : Price) (demand : ℕ → Demand)
    (reference posted : ℕ → Price) : ℝ :=
  sSup {g | ∃ f : Price → Price, Measurable f ∧
    g = ∑ t ∈ Finset.range T, (revenue cost (demand t) (f (reference t)) -
      revenue cost (demand t) (posted t))}

def zeroPrice : Price := ⟨0, by norm_num, by norm_num⟩

/-- A pricing rule with its private seed fixed maps its finite observation
history to the next price. Each observation contains the posted price and revenue. -/
abbrev PricingRule := (t : ℕ) → (Fin t → Price × ℝ) → Price

/-- Run a pricing rule using the revenue oracle at the price it proposes. -/
def pricingHistory (rule : PricingRule) (observe : ℕ → Price → ℝ) :
    (t : ℕ) → Fin t → Price × ℝ
  | 0 => Fin.elim0
  | t + 1 =>
    let history := pricingHistory rule observe t
    let p := rule t history
    Fin.lastCases (p, observe t p) history

end CalibeatBandit.Pricing


