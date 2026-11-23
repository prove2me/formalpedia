-- Prove2me | Definitions.Def_CarlssonPartition_Approx_Supplement_AdmissiblePolicies
-- name    : CarlssonPartition_Approx_Supplement_AdmissiblePolicies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:25:30.700892+00:00
-- url     : https://prove2.me/theorems/43c621ab-58ba-4351-a8bc-9fb20a9d2af1
-- title:
--   §3 — causal routing rules, independent randomization and physical policy realizations
-- statement:
--   A routing rule maps a complete request stream and an independent random seed to actual depot tours. At real time $t$, it observes arrived orders' epochs and locations and the completion or survival of services already begun. It cannot observe future arrivals, future locations or unrevealed service durations. Nonanticipation is tested on every counterfactual request path, not just almost surely on the realized input image.
--
--   Simultaneous physical decisions are ordered by natural-number stages at the same real epoch. A service start at stage $n$ is decided before revealing that service's zero/nonzero duration; its instantaneous completion is observable at stage $n+1$. A later same-time dispatch may react to it. Equality of observations through a stage forces equality of the physical decision prefix through that stage. Measurable physical controls, local finiteness of tours and finite tour capacities remain part of admissibility; no strictly positive service-time premise is introduced.
--
--   The measurable random seed is independent of the whole primitive sequence under stationary and Palm probability. Actual cost is the extended expectation of completion minus arrival, computed from the execution. Infima over the displayed admissible classes live in $[0,\infty]$, with value infinity for the empty class. They are not identified with the source's named Bertsimas–van Ryzin benchmark. Admissibility itself asserts neither finite cost nor optimality, unbiasedness or any asymptotic formula.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), §3 pp. 6–7 (PDF 7–8), §3.2 p. 9 (PDF 10), Definition 1 p. 7 (PDF 8)

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Supplement_Executions

noncomputable section

namespace CarlssonPartition.Approx.Supplement

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

variable {V U Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace V] [MeasurableSpace U]

/-- The deterministic input domain on which a routing rule must be causal. There are
infinitely many orders in either direction, with strictly increasing arrival epochs and
no finite accumulation. No stochastic law or performance assertion is part of this domain. -/
def IsRequestStream (r : ℤ → Request V) : Prop :=
  StrictMono (fun j => (r j).arrival) ∧
    Tendsto (fun j => (r j).arrival) atTop atTop ∧
    Tendsto (fun j => (r j).arrival) atBot atBot

/-- Only arrived orders' labels, epochs and locations are observed. Service durations
are deliberately absent, as are future arrival epochs and locations. -/
def arrivalHistory (r : ℤ → Request V) (t : ℝ) : Set (ℤ × ℝ × V) :=
  {z | (r z.1).arrival ≤ t ∧ z.2.1 = (r z.1).arrival ∧ z.2.2 = (r z.1).location}

/-- An actual loading/departure event. Internal tour-slot labels are not observations. -/
def RoutingSchedule.Loaded {m : ℕ} (p : RoutingSchedule V m)
    (i : Fin m) (d : ℝ) (orders : List ℤ) : Prop :=
  ∃ n tour, p.tour i n = some tour ∧ tour.departure = d ∧ tour.orders = orders

/-- An actual start of service, indexed by customer rather than internal tour slot. -/
def RoutingSchedule.Started {m : ℕ} (p : RoutingSchedule V m)
    (i : Fin m) (j : ℤ) (s : ℝ) : Prop :=
  ∃ n tour, p.tour i n = some tour ∧
    ∃ a : Fin tour.orders.length, tour.orders.get a = j ∧ tour.start a = s

/-- An actual return to the depot. -/
def RoutingSchedule.Returned {m : ℕ} (p : RoutingSchedule V m)
    (i : Fin m) (s : ℝ) : Prop :=
  ∃ n tour, p.tour i n = some tour ∧ tour.returned = s

/-- Actual in-tour position; outside every tour the vehicle is at the depot. -/
def RoutingSchedule.Occupies {m : ℕ} (p : RoutingSchedule V m)
    (i : Fin m) (s : ℝ) (x : V) : Prop :=
  ∃ n tour, p.tour i n = some tour ∧ s ∈ Set.Icc tour.departure tour.returned ∧
    tour.position s = x

/-- Equality of physical decisions and trajectories through t, ignoring arbitrary
slot labels and every part of a tour after t. This does not expose a future return time,
future service start, or the planned continuation of a trajectory. -/
def RoutingSchedule.SamePast {m : ℕ} (p p' : RoutingSchedule V m) (t : ℝ) : Prop :=
  (∀ i d orders, d ≤ t → (p.Loaded i d orders ↔ p'.Loaded i d orders)) ∧
  (∀ i j s, s ≤ t → (p.Started i j s ↔ p'.Started i j s)) ∧
  (∀ i s, s ≤ t → (p.Returned i s ↔ p'.Returned i s)) ∧
  (∀ i s x, s ≤ t → (p.Occupies i s x ↔ p'.Occupies i s x))

/-- Discrete physical decisions at a real epoch. Stages order simultaneous decisions;
they do not add positive time to instantaneous service. -/
inductive RoutingEvent (m : ℕ) where
  | load (driver : Fin m) (orders : List ℤ)
  | start (driver : Fin m) (customer : ℤ)
  | returned (driver : Fin m)

def RoutingSchedule.Occurs {m : ℕ} (p : RoutingSchedule V m)
    (e : RoutingEvent m) (t : ℝ) : Prop :=
  match e with
  | .load i orders => p.Loaded i t orders
  | .start i j => p.Started i j t
  | .returned i => p.Returned i t

/-- Counterfactual revealed service information immediately BEFORE stage n at time t,
using the first run's service starts. Earlier services reveal completion or survival.
A service started at t reveals its zero/nonzero duration only at a LATER stage than
its committed start. Consequently a zero-duration service can finish and trigger
another dispatch at t, but cannot be inspected before the decision to start it. -/
def sameServiceHistory {m : ℕ} (r r' : ℤ → Request V)
    (p : RoutingSchedule V m) (stage : RoutingEvent m → ℝ → ℕ)
    (t : ℝ) (n : ℕ) : Prop :=
  ∀ i j s, p.Started i j s →
    (s < t ∨ (s = t ∧ stage (.start i j) s < n)) →
    if ((r j).duration : ℝ) ≤ t - s
      then (r' j).duration = (r j).duration
      else t - s < ((r' j).duration : ℝ)

/-- A dispatch/routing rule acts on primitive paths and an independent random seed.
Costs are not fields. The rule is required below to work on counterfactual paths, not
only on the actual sample-space image where agreement of infinite pasts can be vacuous. -/
structure RoutingRule (V U : Type*) (m : ℕ) where
  run : (ℤ → Request V) → U → RoutingSchedule V m
  stage : (ℤ → Request V) → U → RoutingEvent m → ℝ → ℕ

/-- Equality of the physical past and of the same-time action prefix. Positions at t
are already determined by the continuous physical trajectory; future positions are
never compared. The internal stages themselves must agree for observed events, so
they cannot conceal dependence on unrevealed service. -/
def RoutingSchedule.SameStagedPast {m : ℕ} (p p' : RoutingSchedule V m)
    (stage stage' : RoutingEvent m → ℝ → ℕ) (t : ℝ) (n : ℕ) : Prop :=
  (∀ e s, s < t → (p.Occurs e s ↔ p'.Occurs e s)) ∧
  (∀ e k, k ≤ n →
    (p.Occurs e t ∧ stage e t = k ↔ p'.Occurs e t ∧ stage' e t = k)) ∧
  (∀ i s x, s ≤ t → (p.Occupies i s x ↔ p'.Occupies i s x))

/-- Strong pathwise nonanticipation: after identical arrived orders and service
observations, the entire physical prefix is identical. Future gaps, future locations,
unknown durations, future return times and a chosen target cost cannot enter a decision.
This predicate alone asserts neither feasibility nor the existence of a stationary run.
Every finite sequence of simultaneous start/completion/dispatch decisions can be ordered
by stages. At each stage the current decision is made before revealing its service.
Feasibility gives locally finite departures and finitely many visits per tour, excluding
infinitely many physical decisions at one epoch; positive service is not required. -/
def RoutingRule.Nonanticipative {m : ℕ} (π : RoutingRule V U m) : Prop :=
  ∀ r r' u t n, IsRequestStream r → IsRequestStream r' →
    arrivalHistory r t = arrivalHistory r' t →
    sameServiceHistory r r' (π.run r u) (π.stage r u) t n →
    (π.run r u).SameStagedPast (π.run r' u) (π.stage r u) (π.stage r' u) t n

/-- Realization of a rule on a marked renewal input. Randomization is measurable and
independent of the WHOLE primitive arrival/mark sequence under both time and Palm laws.
It therefore cannot provide a disguised copy of future input. A seed may encode an
entire presampled stream of internal random choices; its distribution is unrestricted. -/
structure PolicyRealization (A : MarkedRenewal Ω (V × ℝ≥0)) (U : Type*)
    [MeasurableSpace U] (m : ℕ) where
  rule : RoutingRule V U m
  seed : Ω → U
  seed_measurable : Measurable seed
  independent_time : IndepFun seed (fun ω => fun j : ℤ =>
    (A.palm.N.T j ω, A.mark j ω)) A.palm.P
  independent_palm : IndepFun seed (fun ω => fun j : ℤ =>
    (A.palm.N.T j ω, A.mark j ω)) A.palm.P0

/-- The execution is obtained by running the rule on actual requests. -/
def PolicyRealization.execution {A : MarkedRenewal Ω (V × ℝ≥0)} {m : ℕ}
    (π : PolicyRealization A U m) : Execution A m where
  schedule := fun ω => π.rule.run (A.request ω) (π.seed ω)

/-- A causal, physically valid stationary realization. No optimality, unbiasedness,
finite delay or formula for its cost is included in admissibility. Those are separate
properties below. No claimed source performance is built into this interface. -/
def PolicyRealization.Admissible [PseudoMetricSpace V]
    {A : MarkedRenewal Ω (V × ℝ≥0)} {m : ℕ}
    (π : PolicyRealization A U m) (x0 : V) (v : ℝ) (q : ℕ) : Prop :=
  π.rule.Nonanticipative ∧ π.execution.Valid x0 v q ∧ π.execution.StationaryCosts

/-- Actual typical-order delivery cost, retaining infinite expectation. -/
def PolicyRealization.cost {A : MarkedRenewal Ω (V × ℝ≥0)} {m : ℕ}
    (π : PolicyRealization A U m) : ℝ≥0∞ := π.execution.meanDelivery

/-- Dedicated policies restrict actual visits, rather than postulating district costs. -/
def PolicyRealization.DedicatedTo {A : MarkedRenewal Ω (V × ℝ≥0)} {m : ℕ}
    (π : PolicyRealization A U m) (Rs : Fin m → Set V) : Prop :=
  π.execution.DedicatedTo Rs

/-- Definition 1 is a property of the actual conditional expectations. -/
def PolicyRealization.SpatiallyUnbiased {A : MarkedRenewal Ω (V × ℝ≥0)} {m : ℕ}
    (π : PolicyRealization A U m) (R : Set V) : Prop :=
  π.execution.SpatiallyUnbiased R

/-- Infimum benchmark on the displayed realization space, with its seed and sample
space parameters explicit. This is not the paper's named BVR benchmark and is not
asserted to be attained. In the empty class its value is infinity, never real zero. -/
def flexibleValue [PseudoMetricSpace V] (A : MarkedRenewal Ω (V × ℝ≥0))
    (U : Type*) [MeasurableSpace U] (m : ℕ) (x0 : V) (v : ℝ) (q : ℕ) : ℝ≥0∞ :=
  ⨅ (π : PolicyRealization A U m) (_ : π.Admissible x0 v q), π.cost

/-- Dedicated infimum on the same realization space. Zero-demand districts are not
conditioned on, and the definition does not assert existence of a feasible policy. -/
def dedicatedValue [PseudoMetricSpace V] (A : MarkedRenewal Ω (V × ℝ≥0))
    (U : Type*) [MeasurableSpace U] (m : ℕ) (x0 : V) (v : ℝ) (q : ℕ)
    (Rs : Fin m → Set V) : ℝ≥0∞ :=
  ⨅ (π : PolicyRealization A U m) (_ : π.Admissible x0 v q)
    (_ : π.DedicatedTo Rs), π.cost

end CarlssonPartition.Approx.Supplement


