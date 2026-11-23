-- Prove2me | Definitions.Def_CarlssonPartition_Approx_Supplement_RoutingPaths
-- name    : CarlssonPartition_Approx_Supplement_RoutingPaths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:19:32.984805+00:00
-- url     : https://prove2.me/theorems/ef399349-9d8b-47b7-bed8-00eb97e6db09
-- title:
--   §3 — requests, capacity-feasible depot tours, physical fleet schedules and elapsed delivery costs
-- statement:
--   A realized request has an arrival time, a location in a metric space, and a finite nonnegative service duration. A depot tour records an ordered finite list of requests, its departure and return times, each service start, and an actual vehicle trajectory.
--
--    Feasibility requires no repeated order, between one and $q$ loaded orders, pickup after every loaded order has arrived, departure and return at the depot, speed at most $v$, and remaining at each customer's location throughout its on-site service. Visits follow the listed order. A fleet schedule assigns optional tours to each of $m$ vehicles, with no overlapping tours for one vehicle, exactly one visit to every order, and locally finite departures. Idle vehicles and empty tour slots are permitted.
--
--    The waiting and delivery costs of order $j$ are
--    $$
--    W_j=\text{service-start time}_j-\text{arrival time}_j,\qquad
--    T_j=W_j+S_j.
--    $$
--    Costs are extended nonnegative numbers; an unserved order has infinite waiting time. This is the physical execution layer. It deliberately makes no assertion of causality, stationarity, measurability of a random execution, or admissibility of a policy; those are outstanding obligations, not arbitrary fields assumed to supply the desired theorems.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), §3 pp. 6–7 (PDF 7–8), §3.2 p. 9 (PDF 10)

import Mathlib

noncomputable section

namespace CarlssonPartition.Approx.Supplement

open MeasureTheory Filter
open scoped ENNReal NNReal

/-- One realized order. Its nonnegative on-site duration is finite; no distributional
or uniform-moment assumption is built into this pathwise object. -/
structure Request (V : Type*) where
  arrival : ℝ
  location : V
  duration : ℝ≥0

/-- A realized depot tour, with its loaded order list, service epochs and actual trajectory.
Feasibility is a separate predicate, rather than a claimed performance property. -/
structure DepotTour (V : Type*) where
  orders : List ℤ
  departure : ℝ
  returned : ℝ
  start : Fin orders.length → ℝ
  position : ℝ → V

/-- Physical feasibility: all loaded orders have arrived, capacity is respected, the
vehicle starts and ends at the depot, moves at speed at most `v`, and remains at each
customer throughout on-site service. The list is the order of visits, with no repetition.
Idling is permitted, as it is for dispatching policies in the paper. -/
def DepotTour.Feasible {V : Type*} [PseudoMetricSpace V]
    (x0 : V) (v : ℝ) (q : ℕ) (requests : ℤ → Request V) (t : DepotTour V) : Prop :=
  t.orders.Nodup ∧ 0 < t.orders.length ∧ t.orders.length ≤ q ∧
  t.departure ≤ t.returned ∧
  (∀ j ∈ t.orders, (requests j).arrival ≤ t.departure) ∧
  t.position t.departure = x0 ∧ t.position t.returned = x0 ∧
  LipschitzOnWith (Real.toNNReal v) t.position (Set.Icc t.departure t.returned) ∧
  (∀ i : Fin t.orders.length,
    t.departure ≤ t.start i ∧
    t.start i + ((requests (t.orders.get i)).duration : ℝ) ≤ t.returned ∧
    (∀ s ∈ Set.Icc (t.start i)
      (t.start i + ((requests (t.orders.get i)).duration : ℝ)),
      t.position s = (requests (t.orders.get i)).location)) ∧
  (∀ i j : Fin t.orders.length, i < j →
    t.start i + ((requests (t.orders.get i)).duration : ℝ) ≤ t.start j)

/-- A fleet's complete realized collection of tours. Optional integer-indexed slots
allow idle vehicles, finitely many tours, and arbitrary past and future tours. -/
structure RoutingSchedule (V : Type*) (m : ℕ) where
  tour : Fin m → ℤ → Option (DepotTour V)

/-- Which driver and tour slot contains an order. -/
def RoutingSchedule.Serves {V : Type*} {m : ℕ}
    (p : RoutingSchedule V m) (slot : Fin m × ℤ) (j : ℤ) : Prop :=
  ∃ t, p.tour slot.1 slot.2 = some t ∧ j ∈ t.orders

/-- Every order is served exactly once; one driver's tours cannot overlap; departures
have no finite accumulation. This is pathwise feasibility, NOT nonanticipation or an
admissible policy. The latter still needs a stochastic observation/dispatch interface. -/
def RoutingSchedule.Feasible {V : Type*} [PseudoMetricSpace V] {m : ℕ}
    (x0 : V) (v : ℝ) (q : ℕ) (requests : ℤ → Request V)
    (p : RoutingSchedule V m) : Prop :=
  (∀ i n t, p.tour i n = some t → t.Feasible x0 v q requests) ∧
  (∀ i n k t u, n ≠ k → p.tour i n = some t → p.tour i k = some u →
    t.returned ≤ u.departure ∨ u.returned ≤ t.departure) ∧
  (∀ j : ℤ, ∃! slot : Fin m × ℤ, p.Serves slot j) ∧
  (∀ a b : ℝ, Set.Finite {slot : Fin m × ℤ |
    ∃ t, p.tour slot.1 slot.2 = some t ∧ t.departure ∈ Set.Icc a b})

/-- Elapsed time to the start of on-site service. A missing order has cost `⊤`;
feasibility gives a unique visit with nonnegative elapsed time. The infima live in
`ℝ≥0∞`, so empty sets cannot create a spurious zero waiting time. -/
def RoutingSchedule.waiting {V : Type*} {m : ℕ} (requests : ℤ → Request V)
    (p : RoutingSchedule V m) (j : ℤ) : ℝ≥0∞ :=
  ⨅ (i : Fin m) (n : ℤ) (t : DepotTour V) (_ : p.tour i n = some t)
    (r : Fin t.orders.length) (_ : t.orders.get r = j),
      ENNReal.ofReal (t.start r - (requests j).arrival)

/-- Delivery time includes on-site service. It is an extended nonnegative cost,
so infinite delays remain infinite before and after expectations. -/
def RoutingSchedule.delivery {V : Type*} {m : ℕ} (requests : ℤ → Request V)
    (p : RoutingSchedule V m) (j : ℤ) : ℝ≥0∞ :=
  p.waiting requests j + (requests j).duration

end CarlssonPartition.Approx.Supplement


