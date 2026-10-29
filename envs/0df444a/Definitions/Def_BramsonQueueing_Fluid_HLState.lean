-- Prove2me | Definitions.Def_BramsonQueueing_Fluid_HLState
-- name    : BramsonQueueing_Fluid_HLState
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:18:58.072013+00:00
-- url     : https://prove2.me/theorems/d1a8e7b0-538e-4330-943f-dc5fc7b11b13
-- title:
--   Full head-of-the-line state space and its size
-- statement:
--   A state records a finite ordered list of jobs, each with its class and nonnegative age since entry into that class. Lists have no upper bound on their length. Jobs are ordered by decreasing age, with ties ordered by class. Each external-arrival class has a strictly positive residual interarrival time; other arrival coordinates are zero. Each nonempty class has a strictly positive residual service time and a service fraction in $[0,1]$; both coordinates vanish at an empty class. Service fractions sum to one at each nonempty station. Only a class's oldest job receives its class's service fraction.
--   The metric sums the truncated coordinate differences of the ordered jobs, including their service fractions, and the ordinary absolute differences of the residual coordinates, exactly as in (4.2). The state size is
--   $$|x|=|z|+|u|+|v|.$$
--   A presentation is an equivalence from the state space to all valid coordinate states, preserving the metric and the measurable coordinate maps. Thus it cannot discard inconvenient initial states. The size is continuous. Padding a finite job list with zero coordinates is replaced by optional entries when evaluating the metric.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Section 4.1, printed 81–83 / PDF 89–91, equations (4.1)–(4.3).

import Definitions.Def_BramsonQueueing_Fluid_NetworkData

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace BramsonQueueing.Fluid

/-- Finite ordered job lists allow arbitrarily many jobs. Ages are times since
entry to the present class. The remaining coordinates are residual times and
the fractions of station effort assigned to each class's oldest job. -/
structure StateData (K : ℕ) where
  jobs : List (Fin K × ℝ≥0)
  u : Fin K → ℝ≥0
  v : Fin K → ℝ≥0
  r : Fin K → ℝ≥0

def queueCount {K : ℕ} (s : StateData K) (k : Fin K) : ℕ :=
  (s.jobs.filter (fun a => a.1 = k)).length

def ValidState {K J : ℕ} (d : NetworkData K J) (s : StateData K) : Prop :=
  s.jobs.Pairwise (fun a b => b.2 < a.2 ∨ (a.2 = b.2 ∧ a.1 ≤ b.1)) ∧
  (∀ k, (k ∈ d.external → 0 < s.u k) ∧ (k ∉ d.external → s.u k = 0)) ∧
  (∀ k, (queueCount s k = 0 → s.v k = 0 ∧ s.r k = 0) ∧
    (0 < queueCount s k → 0 < s.v k) ∧ s.r k ≤ 1) ∧
  (∀ j, (∃ k, d.station k = j ∧ 0 < queueCount s k) →
    ∑ k ∈ Finset.univ.filter (fun k => d.station k = j), s.r k = 1)

def stateSize {K : ℕ} (s : StateData K) : ℝ≥0 :=
  s.jobs.length + ∑ k, s.u k + ∑ k, s.v k

/-- Coordinates used by the source metric (4.2), including per-job service rates. -/
noncomputable def jobCoordinates {K : ℕ} (s : StateData K) (i : ℕ) : ℝ × ℝ × ℝ :=
  match s.jobs[i]? with
  | none => (0, 0, 0)
  | some a => ((a.1.val + 1 : ℕ), a.2,
      if ∃ b ∈ s.jobs.take i, b.1 = a.1 then 0 else s.r a.1)

noncomputable def stateDistance {K : ℕ} (s s' : StateData K) : ℝ :=
  (∑ i ∈ Finset.range (max s.jobs.length s'.jobs.length),
    min (|(jobCoordinates s i).1 - (jobCoordinates s' i).1| +
      |(jobCoordinates s i).2.1 - (jobCoordinates s' i).2.1| +
      |(jobCoordinates s i).2.2 - (jobCoordinates s' i).2.2|) 1) +
  (∑ k, |(s.u k : ℝ) - s'.u k|) + (∑ k, |(s.v k : ℝ) - s'.v k|)

/-- An arbitrary presentation of exactly the full state space (4.1)–(4.3).
The equivalence ensures no initial states or unbounded queues are omitted. -/
structure StatePresentation {K J : ℕ} (d : NetworkData K J) (S : Type*)
    [MetricSpace S] [MeasurableSpace S] where
  coordinates : S ≃ {s : StateData K // ValidState d s}
  metric : ∀ x y, dist x y = stateDistance (coordinates x).1 (coordinates y).1
  measurable_u : ∀ k, Measurable (fun x => (coordinates x).1.u k)
  measurable_v : ∀ k, Measurable (fun x => (coordinates x).1.v k)
  measurable_r : ∀ k, Measurable (fun x => (coordinates x).1.r k)
  measurable_z : ∀ k, Measurable (fun x => queueCount (coordinates x).1 k)
  size_continuous : Continuous (fun x => stateSize (coordinates x).1)

end BramsonQueueing.Fluid


