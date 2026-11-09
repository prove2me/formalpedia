-- Prove2me | Definitions.Def_BatchMaxService_Metric_RequestInput
-- name    : BatchMaxService_Metric_RequestInput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:20:52.601092+00:00
-- url     : https://prove2.me/theorems/cc4145b7-1909-4bd2-91d7-6a7bee21b3e1
-- title:
--   Finite real-time inputs, elective schedules, costs and the unrestricted optimum
-- statement:
--   Let $X$ be a known finite metric, $s_0\in X$ its initial server position, and $Q$ a finite set of distinct request identities. Each $q\in Q$ has a real arrival time $a(q)\ge0$ and a location $x(q)\in X$. Equal location/time pairs do not identify requests.
--
--   A schedule is a finite time-ordered list of instantaneous finite walks with matching successive endpoints. Each event selects a possibly empty set of arrived, previously unserved identities at its listed vertices. An empty batch is pure repositioning; a nonempty batch incurs its own maximum waiting charge. Several separately charged events may occur at one timestamp. All requests are served exactly once. Write
--
--   $$\operatorname{Mov}(\sigma)=\sum_e\operatorname{len}(P_e),\qquad\operatorname{Delay}(\sigma)=\sum_{e:B_e\ne\varnothing}\max_{q\in B_e}(t_e-a(q)),\qquad\operatorname{OPT}(I)=\inf_{\sigma\text{ feasible}}(\operatorname{Mov}(\sigma)+\operatorname{Delay}(\sigma)).$$
--
--   The infimum ranges over all feasible elective schedules. Normalized schedules have batches containing complete consecutive arrival epochs and serve each at its last epoch time. A separate one-batch candidate waits until the final arrival and visits every requested location; it is not used to restrict OPT.
--
--   **Formalization Note** Sites are enumerated by `Fin n`; the initial site excludes an empty metric but permits one site. Labels are a finite subset of the naturals, including the empty set. Objective terms are real; OPT is in ENNReal. The maximum folded with zero agrees with the batch maximum because feasible ages are nonnegative.
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), Section 2 and Proposition 3.1, printed pp. 4–5 / PDF pp. 5–6

import Mathlib

namespace BatchMaxService.Metric

/-- Section 2, printed pp. 4–5. Identities are natural labels, not location/time pairs.
    `Fin n` is an enumeration of the known sites; `start` excludes only the empty metric. -/
structure RequestInput (n : ℕ) where
  start : Fin n
  ids : Finset ℕ
  arrival : ℕ → ℝ
  location : ℕ → Fin n
  arrival_nonneg : ∀ q ∈ ids, 0 ≤ arrival q

/-- A single instantaneous walk and its elective batch. Empty batches reposition. -/
structure ServiceEvent (n : ℕ) where
  time : ℝ
  walk : List (Fin n)
  batch : Finset ℕ

abbrev Schedule (n : ℕ) := List (ServiceEvent n)

variable {n : ℕ}

noncomputable def walkLength [MetricSpace (Fin n)] (w : List (Fin n)) : ℝ :=
  ((w.zip w.tail).map fun uv => dist uv.1 uv.2).sum

/-- Time order permits equality and each event retains its own delay bill. -/
def follows (s : Fin n) (t : ℝ) : Schedule n → Prop
  | [] => True
  | e :: rest => t ≤ e.time ∧ e.walk.head? = some s ∧
      follows (e.walk.getLast?.getD s) e.time rest

/-- Every selected request has arrived and is at a listed vertex of that walk.
    Pairwise batch disjointness and coverage express exactly-once service. -/
def Feasible (I : RequestInput n) (σ : Schedule n) : Prop :=
  follows I.start 0 σ ∧
  (∀ e ∈ σ, ∀ q ∈ e.batch, q ∈ I.ids ∧ I.arrival q ≤ e.time ∧
    I.location q ∈ e.walk) ∧
  σ.Pairwise (fun e f => Disjoint e.batch f.batch) ∧
  (σ.map ServiceEvent.batch).foldl (· ∪ ·) ∅ = I.ids

/-- Finite maximum, with zero for an empty batch. Feasibility makes every age nonnegative. -/
noncomputable def batchDelay (I : RequestInput n) (e : ServiceEvent n) : ℝ :=
  (e.batch.toList.map fun q => e.time - I.arrival q).foldl max 0

noncomputable def movement [MetricSpace (Fin n)] (σ : Schedule n) : ℝ :=
  (σ.map fun e => walkLength e.walk).sum

noncomputable def delay (I : RequestInput n) (σ : Schedule n) : ℝ :=
  (σ.map (batchDelay I)).sum

noncomputable def cost [MetricSpace (Fin n)] (I : RequestInput n) (σ : Schedule n) : ℝ :=
  movement σ + delay I σ

/-- Unrestricted elective infimum. An empty feasible index set would give +∞,
    never a spurious real zero. Finiteness is a conclusion of the goal. -/
noncomputable def OPT [MetricSpace (Fin n)] (I : RequestInput n) : ENNReal :=
  ⨅ σ : {σ : Schedule n // Feasible I σ}, ENNReal.ofReal (cost I σ.val)

/-- Complete consecutive epochs in every nonempty batch, served at its latest arrival.
    Feasibility supplies time order, disjointness and coverage of all epochs. -/
noncomputable def Normalized (I : RequestInput n) (σ : Schedule n) : Prop :=
  ∀ e ∈ σ, e.batch.Nonempty →
    (∃ q ∈ e.batch, e.time = I.arrival q) ∧
    (∀ q ∈ e.batch, I.arrival q ≤ e.time) ∧
    (∀ p ∈ e.batch, ∀ q ∈ I.ids,
      I.arrival p ≤ I.arrival q → I.arrival q ≤ e.time → q ∈ e.batch)

/-- A concrete finite offline candidate, independent of any online certificates:
    after the last arrival, walk through every requested location in one batch. -/
noncomputable def oneBatchSchedule (I : RequestInput n) : Schedule n := by
  classical
  exact if I.ids = ∅ then [] else
    [⟨(I.ids.toList.map I.arrival).foldl max 0,
      I.start :: (I.ids.sort (· ≤ ·)).map I.location, I.ids⟩]

end BatchMaxService.Metric


