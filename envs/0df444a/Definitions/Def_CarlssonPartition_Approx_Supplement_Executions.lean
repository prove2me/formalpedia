-- Prove2me | Definitions.Def_CarlssonPartition_Approx_Supplement_Executions
-- name    : CarlssonPartition_Approx_Supplement_Executions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:20:28.537806+00:00
-- url     : https://prove2.me/theorems/9d667d5e-6dc2-4a21-8b20-d1abf34593fb
-- title:
--   Definition 1 and §3.2 — physical random executions, typical-order costs and spatial unbiasedness
-- statement:
--   Let a stationary independently marked renewal input have order locations $X_j$, nonnegative durations $S_j$ and arrival epochs $T_j$. A random fleet execution is an actual collection of capacity-feasible depot tours for each sample outcome. Its customer costs are computed from the visits:
--    $$
--    W_j=\text{service-start}_j-T_j,\qquad T^{\mathrm{del}}_j=W_j+S_j.
--    $$
--    Physical validity requires feasibility under both the stationary law and the Palm law and measurable costs under Palm probability. A separate arrival-shift compatibility predicate expresses stationarity of elapsed customer costs. Expected waiting and delivery times are nonnegative extended Palm integrals; stability means finite expected delivery time.
--
--    For a measurable spatial subset $Q$ of positive typical-order probability, conditional waiting is the restricted Palm expectation divided by that probability. Definition 1 is represented by
--    $$
--    E^0[W_0\mid X_0\in Q]=E^0[W_0],\qquad Q\subseteq R,\quad P^0(X_0\in Q)>0.
--    $$
--    A dedicated execution sends driver $i$ only to locations in district $R_i$, with no conditioning on zero-demand districts. These definitions connect physical schedules and actual stochastic customer costs. They do not yet define an admissible nonanticipative dispatch rule: physical validity and cost stationarity alone do not imply causality. No new theorem item assumes them to stand for a complete admissible policy.
--
--   Physical validity additionally requires measurable optional tour departures, returns, loaded order lists and service-start records, and jointly measurable trajectories in time and outcome. Measurability of customer costs alone is not used to certify random controls.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), Definition 1 p. 7 (PDF 8); §3.2 p. 9 (PDF 10); §3.3 p. 10 (PDF 11)

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Supplement_MarkedRenewal
import Definitions.Def_CarlssonPartition_Approx_Supplement_RoutingPaths

noncomputable section

namespace CarlssonPartition.Approx.Supplement

open MeasureTheory Filter
open scoped ENNReal NNReal

variable {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]

/-- Requests read from an actual stationary input, without rate rescaling. -/
def MarkedRenewal.request (A : MarkedRenewal Ω (V × ℝ≥0)) (ω : Ω) (j : ℤ) : Request V where
  arrival := A.palm.N.T j ω
  location := (A.mark j ω).1
  duration := (A.mark j ω).2

/-- A random physical fleet execution driven by an input. Its costs below are computed
from actual tours. Causality is a separate outstanding interface, not a field asserting
an arbitrary desired cost or policy existence. -/
structure Execution (A : MarkedRenewal Ω (V × ℝ≥0)) (m : ℕ) where
  schedule : Ω → RoutingSchedule V m

variable {A : MarkedRenewal Ω (V × ℝ≥0)} {m : ℕ}

/-- Each order's actual elapsed waiting and delivery times, computed from the schedule;
there is no independent function field that can be set equal to a desired leading term. -/
def Execution.waiting (E : Execution A m) (j : ℤ) (ω : Ω) : ℝ≥0∞ :=
  (E.schedule ω).waiting (A.request ω) j

def Execution.delivery (E : Execution A m) (j : ℤ) (ω : Ω) : ℝ≥0∞ :=
  (E.schedule ω).delivery (A.request ω) j

/-- Measurable physical controls, beyond measurability of the resulting scalar costs.
Tour slots record optional departures, returns, loaded order lists and service starts;
the trajectory is jointly measurable in time and the primitive outcome. -/
def Execution.MeasurableEvents (E : Execution A m) : Prop :=
  ∀ i n,
    MeasurableSet {ω | (E.schedule ω).tour i n ≠ none} ∧
    (∀ B : Set ℝ, MeasurableSet B →
      MeasurableSet {ω | ∃ t, (E.schedule ω).tour i n = some t ∧ t.departure ∈ B}) ∧
    (∀ B : Set ℝ, MeasurableSet B →
      MeasurableSet {ω | ∃ t, (E.schedule ω).tour i n = some t ∧ t.returned ∈ B}) ∧
    (∀ orders : List ℤ,
      MeasurableSet {ω | ∃ t, (E.schedule ω).tour i n = some t ∧ t.orders = orders}) ∧
    (∀ j : ℤ, ∀ B : Set ℝ, MeasurableSet B →
      MeasurableSet {ω | ∃ t, (E.schedule ω).tour i n = some t ∧
        ∃ r : Fin t.orders.length, t.orders.get r = j ∧ t.start r ∈ B}) ∧
    (∀ B : Set V, MeasurableSet B →
      MeasurableSet {z : ℝ × Ω | ∃ t, (E.schedule z.2).tour i n = some t ∧
        t.position z.1 ∈ B})

/-- Physical feasibility and measurable costs at stationary times and at typical orders.
Both laws are checked explicitly: a time-null failure need not be Palm-null. This
predicate alone makes no claim of nonanticipation or of existence of a feasible rule. -/
def Execution.Valid [PseudoMetricSpace V] (E : Execution A m) (x0 : V) (v : ℝ) (q : ℕ) : Prop :=
  E.MeasurableEvents ∧
  (∀ᵐ ω ∂A.palm.P,
    (E.schedule ω).Feasible x0 v q (A.request ω)) ∧
  (∀ᵐ ω ∂A.palm.P0,
    (E.schedule ω).Feasible x0 v q (A.request ω)) ∧
  (∀ j, AEMeasurable (E.waiting j) A.palm.P0 ∧
    AEMeasurable (E.delivery j) A.palm.P0)

/-- Arrival-shift compatibility of actual elapsed costs. A stationary execution must
use the same customer costs after recentering on any arrival. This is not causality. -/
def Execution.StationaryCosts (E : Execution A m) : Prop :=
  ∀ k : ℤ, ∀ᵐ ω ∂A.palm.P0,
    E.waiting 0 (A.palm.θ (A.palm.N.T k ω) ω) = E.waiting k ω ∧
    E.delivery 0 (A.palm.θ (A.palm.N.T k ω) ω) = E.delivery k ω

/-- Typical-order expected waiting and delivery times. All integrals are nonnegative
extended expectations, so unstable queues cannot acquire zero cost by nonintegrability. -/
def Execution.meanWaiting (E : Execution A m) : ℝ≥0∞ :=
  A.expected (E.waiting 0)

def Execution.meanDelivery (E : Execution A m) : ℝ≥0∞ :=
  A.expected (E.delivery 0)

/-- Stability of the execution's expected delivery time, separate from the primitive
workload inequality and from unbiasedness. No performance estimate is assumed here. -/
def Execution.Stable (E : Execution A m) : Prop := E.meanDelivery < ⊤

/-- Conditional expected waiting for a typical order in Q. It has its source meaning
only for positive-probability measurable Q; SpatiallyUnbiased enforces that domain. -/
def Execution.meanWaitingOn (E : Execution A m) (Q : Set V) : ℝ≥0∞ :=
  A.expectedOn (E.waiting 0) (Q ×ˢ Set.univ)

/-- Definition 1: every positive-probability spatial subset has the same conditional
expected waiting time as the whole region. Null spatial events are not conditioned on. -/
def Execution.SpatiallyUnbiased (E : Execution A m) (R : Set V) : Prop :=
  ∀ Q : Set V, MeasurableSet Q → Q ⊆ R →
    A.palm.P0 (A.mark 0 ⁻¹' (Q ×ˢ Set.univ)) ≠ 0 →
      E.meanWaitingOn Q = E.meanWaiting

/-- Dedicated execution: driver i serves only locations in district i. Zero-demand
and empty districts are permitted; this never conditions on their zero probabilities. -/
def Execution.DedicatedTo (E : Execution A m) (Rs : Fin m → Set V) : Prop :=
  ∀ᵐ ω ∂A.palm.P0, ∀ i n t,
    (E.schedule ω).tour i n = some t →
      ∀ j ∈ t.orders, (A.request ω j).location ∈ Rs i

end CarlssonPartition.Approx.Supplement


