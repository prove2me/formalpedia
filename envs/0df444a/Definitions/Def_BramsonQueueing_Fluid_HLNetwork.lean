-- Prove2me | Definitions.Def_BramsonQueueing_Fluid_HLNetwork
-- name    : BramsonQueueing_Fluid_HLNetwork
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:20:46.816584+00:00
-- url     : https://prove2.me/theorems/fa96ae71-0f98-4c71-a122-ce9f8acc3956
-- title:
--   Primitive-driven head-of-the-line network realization
-- statement:
--   An HL network combines the open network data, its full ordered-job state space, independent primitives, and a general-state strong Markov family on a common primitive probability space. It records integer arrival and departure counts and all six queueing paths. For every initial state and every sample in $G$, the records obey routing conservation, queue conservation, cumulative work and station-effort identities, nonidling, and the residual-time updates. Service effort is the integral of the class service fractions. Class job lists evolve by aging initial jobs, appending arrivals, and removing the oldest departed jobs. Service fractions remain constant between events and are reset at events by a measurable discipline that depends on job ages, classes, and residuals, not the old service fractions.
--   The service-work prefix is computed from actual jobs: if the class starts nonempty its first job uses its residual service, and later jobs use fresh primitive draws; if it starts empty every arriving job uses a fresh draw. This follows the explicit construction on printed p.83. The empty-class boundary issue in the displayed (4.47) is documented in INSIGHTS.yaml. The definition contains no assumed fluid compactness, uniform integrability, drift estimate, or recurrence conclusion.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Section 4.1 construction, printed 81–85 / PDF 89–93; Section 4.3, printed 101–103 / PDF 109–111.

import Definitions.Def_BramsonQueueing_Fluid_HLState
import Definitions.Def_BramsonQueueing_Fluid_MarkovProcess
import Definitions.Def_BramsonQueueing_Fluid_Primitives
import Definitions.Def_BramsonQueueing_Fluid_FluidModel

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace BramsonQueueing.Fluid

/-- Cumulative work of the first n jobs to be served at a class. If initially
nonempty, the oldest job uses its residual service; otherwise all jobs use fresh
service times. In particular the zero-job cumulative work is exactly zero. -/
noncomputable def serviceWork {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r : PositiveIID Ω μ) (z : ℕ) (v : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  if z = 0 then renewalSum r n ω
  else if n = 0 then 0 else v + renewalSum r (n - 1) ω

noncomputable def externalCount {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r : PositiveIID Ω μ) (u t : ℝ≥0) (ω : Ω) : ℕ :=
  sSup {n : ℕ | n = 0 ∨ u + renewalSum r (n - 1) ω ≤ t}

/-- Under its strong-law hypothesis the set above is finite. The source's next
renewal epoch, after e external arrivals, is u plus e fresh increments. -/
noncomputable def arrivalAge (A : ℝ≥0 → ℕ) (t : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  t - sInf {s : ℝ≥0 | n ≤ A s}

variable {K J : ℕ} {d : NetworkData K J} {S Ω : Type*}
  [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace Ω]

/-- A source HL network as an axiomatic realization of its primitive-driven
evolution. Fields describe the construction and the system equations, never
fluid limits, recurrence, drift, integrability bounds, or stability. -/
structure HLNetwork (d : NetworkData K J) (S Ω : Type*)
    [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace Ω] where
  μ : Measure Ω
  primitives : PrimitiveTriple d Ω μ
  states : StatePresentation d S
  process : MarkovProcess S Ω
  common_law : ∀ x, process.law x = μ
  path : S → Ω → SixPath K J
  arrivals : S → Ω → ℝ≥0 → Fin K → ℕ
  departures : S → Ω → ℝ≥0 → Fin K → ℕ
  discipline : S → Fin K → ℝ≥0
  discipline_measurable : ∀ k, Measurable (fun x => discipline x k)
  discipline_without_old_rates : ∀ x y,
    (states.coordinates x).1.jobs = (states.coordinates y).1.jobs →
    (states.coordinates x).1.u = (states.coordinates y).1.u →
    (states.coordinates x).1.v = (states.coordinates y).1.v → discipline x = discipline y
  discipline_valid : ∀ x,
    ValidState d { (states.coordinates x).1 with r := discipline x }
  initial : ∀ x ω, PrimitiveGood primitives ω → process.X x 0 ω = x
  regular : ∀ x ω, PrimitiveGood primitives ω → FluidRegular (path x ω)
  cumulative_zero : ∀ x ω, PrimitiveGood primitives ω →
    (path x ω).A 0 = 0 ∧ (path x ω).D 0 = 0 ∧
    (path x ω).T 0 = 0 ∧ (path x ω).Y 0 = 0
  count_identification : ∀ x ω, PrimitiveGood primitives ω → ∀ t k,
    (path x ω).A t k = arrivals x ω t k ∧
    (path x ω).D t k = departures x ω t k ∧
    (path x ω).Z t k = queueCount (states.coordinates (process.X x t ω)).1 k
  path_measurable : ∀ x t,
    Measurable (fun ω => (path x ω).A t) ∧ Measurable (fun ω => (path x ω).D t) ∧
    Measurable (fun ω => (path x ω).T t) ∧ Measurable (fun ω => (path x ω).W t) ∧
    Measurable (fun ω => (path x ω).Y t) ∧ Measurable (fun ω => (path x ω).Z t)
  path_right_continuous : ∀ x ω, PrimitiveGood primitives ω → ∀ t,
    ContinuousWithinAt (fun s => (path x ω).A s) (Set.Ici t) t ∧
    ContinuousWithinAt (fun s => (path x ω).D s) (Set.Ici t) t
  effort_continuous : ∀ x ω, PrimitiveGood primitives ω →
    Continuous (path x ω).T ∧ Continuous (path x ω).Y
  flow : ∀ x ω, PrimitiveGood primitives ω → ∀ t k,
    (path x ω).Z t k = (path x ω).Z 0 k + (path x ω).A t k - (path x ω).D t k
  routing : ∀ x ω, PrimitiveGood primitives ω → ∀ t k,
    arrivals x ω t k =
      (if h : k ∈ d.external then
        externalCount (primitives.xi ⟨k, h⟩) ((states.coordinates x).1.u k) t ω
        else 0) +
      ∑ l, routingCount primitives l k (departures x ω t l) ω
  workload : ∀ x ω, PrimitiveGood primitives ω → ∀ t j,
    (path x ω).W t j =
      (∑ k ∈ Finset.univ.filter (fun k => d.station k = j),
        (serviceWork (primitives.gamma k) (queueCount (states.coordinates x).1 k)
          ((states.coordinates x).1.v k)
          (queueCount (states.coordinates x).1 k + arrivals x ω t k) ω : ℝ)) -
      ∑ k ∈ Finset.univ.filter (fun k => d.station k = j), (path x ω).T t k
  station_effort : ∀ x ω, PrimitiveGood primitives ω → ∀ t j,
    (∑ k ∈ Finset.univ.filter (fun k => d.station k = j), (path x ω).T t k) +
      (path x ω).Y t j = t
  nonidling : ∀ x ω, PrimitiveGood primitives ω → ∀ j s t, s ≤ t →
    (path x ω).Y s j < (path x ω).Y t j →
      ∃ u ∈ Set.Icc s t, (path x ω).W u j = 0
  cumulative_service : ∀ x ω, PrimitiveGood primitives ω → ∀ t k,
    (serviceWork (primitives.gamma k) (queueCount (states.coordinates x).1 k)
      ((states.coordinates x).1.v k) (departures x ω t k) ω : ℝ) ≤ (path x ω).T t k
  residual_service : ∀ x ω, PrimitiveGood primitives ω → ∀ t k,
    let st := (states.coordinates (process.X x t ω)).1
    if queueCount st k = 0 then
      (path x ω).T t k =
        (serviceWork (primitives.gamma k) (queueCount (states.coordinates x).1 k)
          ((states.coordinates x).1.v k) (departures x ω t k) ω : ℝ)
    else (st.v k : ℝ) =
      (serviceWork (primitives.gamma k) (queueCount (states.coordinates x).1 k)
        ((states.coordinates x).1.v k) (departures x ω t k + 1) ω : ℝ) - (path x ω).T t k
  residual_arrival : ∀ x ω, PrimitiveGood primitives ω → ∀ t
    (k : {k : Fin K // k ∈ d.external}),
    ((states.coordinates (process.X x t ω)).1.u k : ℝ) =
      ((states.coordinates x).1.u k : ℝ) +
      (renewalSum (primitives.xi k)
        (externalCount (primitives.xi k) ((states.coordinates x).1.u k) t ω) ω : ℝ) - t
  oldest_first : ∀ x ω, PrimitiveGood primitives ω → ∀ t k,
    (((states.coordinates (process.X x t ω)).1.jobs.filter (fun a => a.1 = k)).map
      Prod.snd) =
    (((((states.coordinates x).1.jobs.filter (fun a => a.1 = k)).map
      (fun a => a.2 + t)) ++
      (List.range (arrivals x ω t k)).map
        (fun n => arrivalAge (fun s => arrivals x ω s k) t (n + 1))).drop
          (departures x ω t k))
  service_allocation : ∀ x ω, PrimitiveGood primitives ω → ∀ t k,
    (path x ω).T t k = ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
      ((states.coordinates (process.X x s.toNNReal ω)).1.r k : ℝ)
  constant_rates_between_events : ∀ x ω, PrimitiveGood primitives ω → ∀ s t,
    s ≤ t → arrivals x ω s = arrivals x ω t → departures x ω s = departures x ω t →
      (states.coordinates (process.X x s ω)).1.r =
      (states.coordinates (process.X x t ω)).1.r
  update_rates_at_events : ∀ x ω, PrimitiveGood primitives ω → ∀ t : ℝ≥0,
    0 < t → (∀ s < t, arrivals x ω s ≠ arrivals x ω t ∨
      departures x ω s ≠ departures x ω t) →
    (states.coordinates (process.X x t ω)).1.r = discipline (process.X x t ω)

noncomputable def HLNetwork.size (n : HLNetwork d S Ω) (x : S) : ℝ≥0 :=
  stateSize (n.states.coordinates x).1

noncomputable def HLNetwork.uMass (n : HLNetwork d S Ω) (x : S) : ℝ≥0 :=
  ∑ k, (n.states.coordinates x).1.u k

noncomputable def HLNetwork.vMass (n : HLNetwork d S Ω) (x : S) : ℝ≥0 :=
  ∑ k, (n.states.coordinates x).1.v k

noncomputable def HLNetwork.zMass (n : HLNetwork d S Ω) (x : S) : ℝ≥0 :=
  (n.states.coordinates x).1.jobs.length

end BramsonQueueing.Fluid


