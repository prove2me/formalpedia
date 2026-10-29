-- Prove2me | Definitions.Def_BramsonQueueing_FIFOKelly_State
-- name    : BramsonQueueing_FIFOKelly_State
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:05:48.746992+00:00
-- url     : https://prove2.me/theorems/242e377d-f446-4814-adc2-5119cf971a54
-- title:
--   Ordered-job HL states and residual clocks
-- statement:
--   An HL state records a finite, unbounded-length list of class-labelled job ages, residual interarrival times, residual class-head services and class allocations. Ages descend, breaking interclass ties by class index. Only the first job of each class receives its class allocation; allocations sum to one at a nonempty station and vanish at empty classes. External clocks exist exactly where the external rate is positive. The size is
--   $$|x|=|z|+|u|+|v|.$$
--   The distance is exactly (4.2), using zero-padded job coordinates and their individual allocations. Between events, ages grow at unit speed, external clocks decrease at unit speed, and service clocks decrease at their allocated rates. The next event is the first exhausted active clock, or infinity when none exists. Job lists have no fixed capacity.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9, printed 81–83; PDF 89–91

import Definitions.Def_BramsonQueueing_FIFOKelly_Parameters

namespace BramsonQueueing.FIFOKelly

open scoped BigOperators

structure RawState (K : ℕ) where
  jobs : List (Fin K × ℝ)
  u : Fin K → ℝ
  v : Fin K → ℝ
  r : Fin K → ℝ

def queueCount {K : ℕ} (x : RawState K) (k : Fin K) : ℕ :=
  (x.jobs.filter fun q => q.1 = k).length

def ValidState {K J : ℕ} (p : Parameters K J) (x : RawState K) : Prop :=
  (∀ q ∈ x.jobs, 0 ≤ q.2) ∧
  x.jobs.Pairwise (fun a b => b.2 < a.2 ∨ (a.2 = b.2 ∧ a.1 ≤ b.1)) ∧
  (∀ k, if 0 < p.data.lam k then 0 < x.u k else x.u k = 0) ∧
  (∀ k, if queueCount x k = 0 then x.v k = 0 ∧ x.r k = 0
    else 0 < x.v k ∧ 0 ≤ x.r k ∧ x.r k ≤ 1) ∧
  (∀ j, (∑ k, if p.data.p k = j then x.r k else 0) =
    if ∃ q ∈ x.jobs, p.data.p q.1 = j then 1 else 0)

def NetworkState {K J : ℕ} (p : Parameters K J) := {x : RawState K // ValidState p x}

def stateSize {K : ℕ} (x : RawState K) : ℝ :=
  x.jobs.length + (∑ k, |x.u k|) + ∑ k, |x.v k|

/-- Service assigned to a job is zero unless it is the first of its class. -/
noncomputable def jobCoordinates {K : ℕ} (x : RawState K) (i : ℕ) : ℝ × ℝ × ℝ :=
  match x.jobs[i]? with
  | none => (0, 0, 0)
  | some q => ((q.1.val + 1 : ℕ), q.2,
      if ∃ q' ∈ x.jobs.take i, q'.1 = q.1 then 0 else x.r q.1)

/-- Metric (4.2), on zero-padded finite job lists. -/
noncomputable def stateDistance {K : ℕ} (x y : RawState K) : ℝ :=
  (∑ i ∈ Finset.range (max x.jobs.length y.jobs.length),
    min 1 (|((jobCoordinates x i).1 - (jobCoordinates y i).1)| +
      |((jobCoordinates x i).2.1 - (jobCoordinates y i).2.1)| +
      |((jobCoordinates x i).2.2 - (jobCoordinates y i).2.2)|)) +
  (∑ k, |x.u k - y.u k|) + ∑ k, |x.v k - y.v k|

/-- Between events, job ages grow, arrival clocks run at unit speed, and
the oldest job of class k receives service at the fixed class allocation. -/
noncomputable def advance {K J : ℕ} (p : Parameters K J) (x : RawState K) (dt : ℝ) : RawState K :=
  ⟨x.jobs.map (fun q => (q.1, q.2 + dt)),
    (fun k => if 0 < p.data.lam k then x.u k - dt else 0),
    (fun k => x.v k - x.r k * dt), x.r⟩

/-- A boundary is the first exhausted arrival or service clock. Infinity
is represented separately when the set of active clocks is empty. -/
def clockTimes {K J : ℕ} (p : Parameters K J) (x : RawState K) : Set ℝ :=
  {d | (∃ k, 0 < p.data.lam k ∧ d = x.u k) ∨
    (∃ k, 0 < x.r k ∧ d = x.v k / x.r k)}

noncomputable def nextEvent {K J : ℕ} (p : Parameters K J)
    (x : RawState K) : ENNReal :=
  ⨅ d ∈ clockTimes p x, ENNReal.ofReal d

end BramsonQueueing.FIFOKelly


