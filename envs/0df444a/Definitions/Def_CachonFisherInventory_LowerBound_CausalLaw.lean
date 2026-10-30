-- Prove2me | Definitions.Def_CachonFisherInventory_LowerBound_CausalLaw
-- name    : CachonFisherInventory_LowerBound_CausalLaw
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T02:47:22.949731+00:00
-- url     : https://prove2.me/theorems/658bc909-4b02-4bfe-b7be-ff474fb93a1d
-- title:
--   Causal trajectory laws and extended average-cost criteria
-- statement:
--   A controlled trajectory consists of initial data S and a sequence of action/outcome pairs (A_t,D_t). Its pre-demand history at time t comprises the initial data, all earlier action/outcome pairs, and the current action. A causal law is a probability measure on trajectories for which each outcome D_t has a prescribed law ν and is independent of this complete pre-demand history. Coordinate and history maps are measurable. This strategic-measure representation includes randomized, history-dependent decisions: no stationarity, Markov property, finite memory, deterministic seed, or bound on the action space is required. In the countable inventory application it is equivalent to choosing randomized decision kernels at each finite history, independently of future exogenous demands.
--
--   The state recursion applies a deterministic transition to the preceding state, current action, and current outcome. Nonnegative expectations use nonnegative Lebesgue integrals, embedded into the extended reals. For a real random variable bounded below by a finite constant b, its expectation is E[(f-b)⁺]+b. This helper is used only where the concrete model implies f≥b; it does not assume that implication. The average criterion is limsup as T tends to infinity of (T+1)⁻¹ Σ_{t=0}^T E[c_t], allowing +∞. Thus the horizon is always positive and no real-valued nonintegrable integral is totalized to zero.
-- source:
--   Cachon and Fisher (2000), Supply Chain Inventory Management and the Value of Shared Information, Management Science 46(8), DOI 10.1287/mnsc.46.8.1032.12029, §3, p. 1035 (PDF p. 4); §5, pp. 1039–1040 (PDF pp. 8–9); explicit probability and time-average encoding

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CachonFisherInventory.LowerBound

/-- Initial data and an infinite sequence of decision/outcome pairs. -/
abbrev ControlTrace (S A D : Type) := S × (ℕ → A × D)

/-- The complete observable history just before outcome t, including decision t. -/
def controlHistory {S A D : Type} (t : ℕ) (w : ControlTrace S A D) :
    S × (Fin t → A × D) × A :=
  (w.1, (fun k => w.2 k.val), (w.2 t).1)

/-- Strategic measures for randomized nonanticipating control with exogenous iid outcomes.
No deterministic, Markov, stationarity or bounded-memory restriction is imposed. -/
def CausalLaw {S A D : Type} [MeasurableSpace S] [MeasurableSpace A]
    [MeasurableSpace D] (ν : Measure D) (μ : Measure (ControlTrace S A D)) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ t : ℕ,
    Measurable (fun w : ControlTrace S A D => (w.2 t).2) ∧
    Measurable (controlHistory (S := S) (A := A) (D := D) t) ∧
    μ.map (fun w => (w.2 t).2) = ν ∧
    IndepFun (fun w => (w.2 t).2) (controlHistory t) μ

/-- Deterministic state recursion driven by the random action/outcome coordinates. -/
def controlledState {S A D : Type} (next : S → A → D → S)
    (w : ControlTrace S A D) : ℕ → S
  | 0 => w.1
  | t + 1 => next (controlledState next w t) (w.2 t).1 (w.2 t).2

/-- Extended expectation of a nonnegative real function. -/
noncomputable def nonnegExpectation {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : EReal :=
  (∫⁻ w, ENNReal.ofReal (f w) ∂μ : ℝ≥0∞)

/-- For f ≥ b, integrate f-b nonnegatively, then restore the finite lower bound. -/
noncomputable def lowerExpectation {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (b : ℝ) (f : Ω → ℝ) : EReal :=
  nonnegExpectation μ (fun w => f w - b) + (b : EReal)

/-- Limsup of expected Cesàro averages over positive horizons. -/
noncomputable def averageValue (v : ℕ → EReal) : EReal :=
  Filter.limsup (fun T : ℕ => ((1 / (T + 1 : ℝ) : ℝ) : EReal) *
    ∑ t ∈ Finset.range (T + 1), v t) Filter.atTop

end CachonFisherInventory.LowerBound


