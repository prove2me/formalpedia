-- Prove2me | Definitions.Def_BramsonQueueing_FIFOKelly_Trace
-- name    : BramsonQueueing_FIFOKelly_Trace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:06:47.553017+00:00
-- url     : https://prove2.me/theorems/6887ca00-16c1-4406-b7f2-d37eeca2a962
-- title:
--   Primitive-driven HL event transitions
-- statement:
--   An event trace records times, post-event states and counters for external draws, new head services and class departures. At the first exhausted clock, completed head jobs leave their classes and follow their routing marks; external arrivals and routed arrivals are inserted at age zero. Surviving jobs age by the elapsed time. Newly exposed heads receive the next service draw, exhausted external clocks receive their next renewal draw, and the measurable discipline resets allocations. Simultaneous events are processed as a batch and the resulting jobs are ordered by the prescribed age/class convention. Traces start at the specified state and zero counters, have no finite accumulation of events, and agree with linear clock evolution between events. Infinity permits a final event when the empty network has no future arrivals. No recurrence, stationary distribution or fluid property is assumed.
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9, printed 81–84; PDF 89–92

import Definitions.Def_BramsonQueueing_FIFOKelly_State
import Definitions.Def_BramsonQueueing_FIFOKelly_Primitives

namespace BramsonQueueing.FIFOKelly

open scoped BigOperators ENNReal NNReal
open Set Filter

structure Counters (K : ℕ) where
  external : Fin K → ℕ
  service : Fin K → ℕ
  departed : Fin K → ℕ

noncomputable def completed {K : ℕ} (x : RawState K) (dt : ℝ) : Finset (Fin K) :=
  Finset.univ.filter (fun k => 0 < x.r k ∧ x.v k = x.r k * dt)

noncomputable def externalDue {K J : ℕ} (p : Parameters K J)
    (x : RawState K) (dt : ℝ) (k : Fin K) : ℕ :=
  if 0 < p.data.lam k ∧ x.u k = dt then 1 else 0

noncomputable def arrivalBatch {K J : ℕ} {Ω : Type} (p : Parameters K J)
    (U : Primitives K Ω) (ω : Ω) (x : RawState K) (c : Counters K)
    (dt : ℝ) (l : Fin K) : ℕ :=
  externalDue p x dt l + ∑ k ∈ completed x dt,
    if U.draw 2 k (c.departed k) ω = (l.val + 1 : ℕ) then 1 else 0

/-- Remove precisely the completed head job of each class, age survivors,
and insert the simultaneous arrival batch in the source's age/class order. -/
noncomputable def nextJobs {K J : ℕ} {Ω : Type} (p : Parameters K J)
    (U : Primitives K Ω) (ω : Ω) (x : RawState K) (c : Counters K)
    (dt : ℝ) : List (Fin K × ℝ) :=
  let survivors := (completed x dt).toList.foldl
    (fun qs k => qs.eraseP (fun q => q.1 = k)) x.jobs
  let arrivals := (Finset.univ : Finset (Fin K)).toList.flatMap
    (fun k => List.replicate (arrivalBatch p U ω x c dt k) (k, (0 : ℝ)))
  (survivors.map (fun q => (q.1, q.2 + dt)) ++ arrivals).mergeSort
    (fun a b => decide (b.2 < a.2 ∨ (a.2 = b.2 ∧ a.1 ≤ b.1)))

def StartsService {K : ℕ} (x : RawState K) (qs : List (Fin K × ℝ))
    (dt : ℝ) (k : Fin K) : Prop :=
  (∃ q ∈ qs, q.1 = k) ∧ (queueCount x k = 0 ∨ k ∈ completed x dt)

noncomputable def nextCounters {K J : ℕ} {Ω : Type} (p : Parameters K J)
    (U : Primitives K Ω) (ω : Ω) (x : RawState K) (c : Counters K)
    (dt : ℝ) : Counters K := by
  classical
  exact ⟨(fun k => c.external k + externalDue p x dt k),
    (fun k => c.service k + if StartsService x (nextJobs p U ω x c dt) dt k then 1 else 0),
    (fun k => c.departed k + if k ∈ completed x dt then 1 else 0)⟩

noncomputable def nextRaw {K J : ℕ} {Ω : Type} (p : Parameters K J)
    (U : Primitives K Ω) (ω : Ω) (f : RawState K → Fin K → ℝ)
    (x : RawState K) (c : Counters K) (dt : ℝ) : RawState K := by
  classical
  let qs := nextJobs p U ω x c dt
  let y : RawState K := ⟨qs,
    (fun k => if externalDue p x dt k = 1 then U.draw 0 k (c.external k) ω
      else if 0 < p.data.lam k then x.u k - dt else 0),
    (fun k => if ¬ ∃ q ∈ qs, q.1 = k then 0
      else if StartsService x qs dt k then U.draw 1 k (c.service k) ω
      else x.v k - x.r k * dt), (fun _ => 0)⟩
  exact { y with r := f y }

/-- An event sequence may end at infinity when no clocks are active.
Finite event times have no accumulation in finite time. -/
structure EventTrace (K : ℕ) where
  time : ℕ → ℝ≥0∞
  state : ℕ → RawState K
  counters : ℕ → Counters K

def RealizesTrace {K J : ℕ} {Ω : Type} (p : Parameters K J)
    (U : Primitives K Ω) (ω : Ω) (f : RawState K → Fin K → ℝ)
    (x : RawState K) (q : ℝ≥0 → RawState K) (e : EventTrace K) : Prop :=
  e.time 0 = 0 ∧ e.state 0 = x ∧
  e.counters 0 = ⟨(fun _ => 0), (fun _ => 0), (fun _ => 0)⟩ ∧
  Tendsto e.time atTop (nhds ⊤) ∧
  (∀ n, e.time (n+1) = e.time n + nextEvent p (e.state n)) ∧
  (∀ n, e.time n ≠ ⊤ → ValidState p (e.state n)) ∧
  (∀ n, e.time (n+1) ≠ ⊤ →
    e.state (n+1) = nextRaw p U ω f (e.state n) (e.counters n)
      (nextEvent p (e.state n)).toReal ∧
    e.counters (n+1) = nextCounters p U ω (e.state n) (e.counters n)
      (nextEvent p (e.state n)).toReal) ∧
  (∀ t : ℝ≥0, ∀ n, e.time n ≤ t → (t : ℝ≥0∞) < e.time (n+1) →
    q t = advance p (e.state n) ((t : ℝ) - (e.time n).toReal))

end BramsonQueueing.FIFOKelly


