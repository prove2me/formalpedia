-- Prove2me | Definitions.Def_BramsonQueueing_FIFOKelly_Network
-- name    : BramsonQueueing_FIFOKelly_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:07:46.730992+00:00
-- url     : https://prove2.me/theorems/ed84987c-5ff4-4464-86fb-cb4d81728cc6
-- title:
--   General HL queueing networks and their six paths
-- statement:
--   An HL network combines the general parameters, independent primitives, a measurable service-allocation discipline, and a strong Markov process on the full ordered-job state space. Its state-space metric is (4.2); the space is locally compact and separable. On the common primitive strong-law event the process must follow the explicit event recursion for every initial state. The discipline depends on jobs and residual clocks, not the old allocation. Arrival and departure paths are counted from the trace, effort is the time integral of allocations, workload is cumulative required service minus effort, idleness is elapsed time minus station effort, and queue length counts the actual jobs. Initial residual service is charged only when an initial head job exists. FIFO selects the oldest job at each station. Condition (5.1) is petite minorization for every positive size sublevel. The network is defined without assuming any theorem about its fluid limits or invariant law.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9, printed 81–87, 101–103, 140, 147; PDF 89–95, 109–111, 148, 155

import Definitions.Def_BramsonQueueing_FIFOKelly_Trace
import Definitions.Def_BramsonQueueing_FIFOKelly_Markov
import Definitions.Def_BramsonQueueing_FIFOKelly_Fluid

namespace BramsonQueueing.FIFOKelly

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal

/-- The HL process of Section 4.1. The state space is identified with the
full ordered-job state space and carries exactly metric (4.2). The process
law is tied to the primitive-driven event recursion, independently of any
stationary distribution, recurrence, or fluid-limit assertion. -/
structure HLNetwork (K J : ℕ) (S Ω : Type) [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [LocallyCompactSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace Ω] where
  parameters : Parameters K J
  coordinates : S ≃ NetworkState parameters
  metric_eq : ∀ x y, dist x y = stateDistance (coordinates x).val (coordinates y).val
  process : MarkovFamily S Ω
  primitives : Primitives K Ω
  primitive_laws : PrimitiveLaws parameters primitives process.probability
  discipline : RawState K → Fin K → ℝ
  discipline_ignores_r : ∀ x y, x.jobs = y.jobs → x.u = y.u → x.v = y.v →
    discipline x = discipline y
  discipline_measurable : Measurable (fun x : S => discipline (coordinates x).val)
  trace : S → Ω → EventTrace K
  dynamics : ∀ ω, GoodPrimitives parameters primitives ω → ∀ x,
    RealizesTrace parameters primitives ω discipline (coordinates x).val
      (fun t => (coordinates (process.path x t ω)).val) (trace x ω)

noncomputable def eventIndex {K : ℕ} (e : EventTrace K) (t : ℝ) : ℕ :=
  sInf {n | ENNReal.ofReal t < e.time (n+1)}

/-- Initial head service is residual; all later services use the iid
sequence. An initially empty class has no residual job to count. -/
noncomputable def cumulativeService {K : ℕ} {Ω : Type} (U : Primitives K Ω)
    (ω : Ω) (x : RawState K) (k : Fin K) (n : ℕ) : ℝ :=
  if queueCount x k = 0 then ∑ i ∈ Finset.range n, U.draw 1 k i ω
  else if n = 0 then 0 else x.v k + ∑ i ∈ Finset.range (n-1), U.draw 1 k i ω

noncomputable def networkPaths {K J : ℕ} {S Ω : Type} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [LocallyCompactSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace Ω] (N : HLNetwork K J S Ω)
    (x : S) (ω : Ω) : SixPaths K J :=
  let e := N.trace x ω
  let q := fun t : ℝ => (N.coordinates (N.process.path x (Real.toNNReal t) ω)).val
  let c := fun t => e.counters (eventIndex e t)
  let a := fun t k => (c t).external k +
    ∑ l, routingCount N.primitives ω l k ((c t).departed l)
  let effort := fun t k => ∫ r in (0 : ℝ)..t, (q r).r k
  { A := fun t k => a t k
    D := fun t k => (c t).departed k
    T := effort
    W := fun t j => ∑ k, if N.parameters.data.p k = j then
      cumulativeService N.primitives ω (N.coordinates x).val k
        (queueCount (N.coordinates x).val k + a t k) - effort t k else 0
    Y := fun t j => t - ∑ k, if N.parameters.data.p k = j then effort t k else 0
    Z := fun t k => queueCount (q t) k }

def FIFOdiscipline {K J : ℕ} {S Ω : Type} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [LocallyCompactSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace Ω] (N : HLNetwork K J S Ω) : Prop :=
  ∀ x : S, ∀ k,
    N.discipline (N.coordinates x).val k =
      if (((N.coordinates x).val.jobs.find?
        (fun q => N.parameters.data.p q.1 = N.parameters.data.p k)).map Prod.fst) = some k
      then 1 else 0

def PetiteSublevels {K J : ℕ} {S Ω : Type} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] [LocallyCompactSpace S]
    [TopologicalSpace.SeparableSpace S] [MeasurableSpace Ω] (N : HLNetwork K J S Ω) : Prop :=
  ∀ κ : ℝ, 0 < κ → Petite N.process {x | stateSize (N.coordinates x).val ≤ κ}

end BramsonQueueing.FIFOKelly


