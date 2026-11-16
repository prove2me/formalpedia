-- Prove2me | Definitions.Def_MLAMaxDelay_RandomizedTimer_Supplement_RootedLine
-- name    : MLAMaxDelay_RandomizedTimer_Supplement_RootedLine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:52:25.915204+00:00
-- url     : https://prove2.me/theorems/89f78b18-971e-4076-ab2d-cce9f3dd41b1
-- title:
--   The rooted half-line and the Max-Balance execution
-- statement:
--   On the continuous half-line rooted at $0$, a **rooted-line input** is a finite set of labelled request occurrences with arrival times $a(r)\ge0$ and locations $x(r)>0$. A service $(t,g)$ with $g\ge0$ clears the pending requests that have arrived by $t$ and lie in $[0,g]$, and costs $g$ plus the maximum delay $\max_{r\in B}(t-a(r))$ of its batch $B$. A schedule is feasible when it is chronological, uses nonnegative times and lengths, and clears every request; infeasible schedules cost $+\infty$, and $\mathrm{OPT}(I)$ is the infimum over all finite schedules.
--
--   **Max-Balance** uses the levels $g_i=2^i$, $i\in\mathbb Z$. With
--
--   $$M(t,g)=\max\{t-a(r): r \text{ pending at } t,\ x(r)\le g\}$$
--
--   (empty maximum $0$), level $g$ is **tight** at $t$ when $M(t,g)=g/4$. Whenever one or more levels are tight, Max-Balance serves the largest tight level; arrivals at a service time are processed first. A schedule is a Max-Balance execution when its services occur at strictly increasing times, each service at $t$ has the length of the largest level tight at $t$ (computed from the services strictly before $t$), and a service occurs at every time at which some level is tight.
--
--   **Formalization Note** Locations are strictly positive: a request at the root lies in every level and the thresholds $2^i/4$ tend to $0$, so Max-Balance has no first tight time after its arrival. Existence, uniqueness and feasibility of the execution are conclusions of Theorem B.2's item.
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Multi-Level Aggregation with Maximum Delay, STOC 2027 submission #217 (October 2026), pp. 21–22, Appendix B.1–B.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/217.pdf

import Mathlib

namespace MLAMaxDelay.RandomizedTimer.Supplement

open scoped ENNReal

/-! Appendix B, pp. 21–22: the continuous half-line rooted at `0`. A service of length `g ≥ 0`
activates `[0, g]` and costs `g` plus the maximum delay of the batch it clears. -/

/-- A rooted-line input: finitely many labelled request occurrences, each with an arrival time
`a(r) ≥ 0` and a location `x(r) > 0` (Max-Balance has no first tight time for a request at the
root `0`). Values outside `requests` are ignored. -/
structure LineInput where
  requests : Finset ℕ
  arrival : ℕ → ℝ
  location : ℕ → ℝ
  arrival_nonneg : ∀ r ∈ requests, 0 ≤ arrival r
  location_pos : ∀ r ∈ requests, 0 < location r

/-- A line service `(t, g)`: time `t`, length `g`. -/
abbrev LineService := ℝ × ℝ
abbrev LineSchedule := List LineService

/-- Pending requests that have arrived by `t` (arrivals at `t` first) and lie in `[0, g]`. -/
noncomputable def lineCleared (I : LineInput) (remaining : Finset ℕ) (s : LineService) :
    Finset ℕ := by
  classical
  exact remaining.filter (fun r => I.arrival r ≤ s.1 ∧ I.location r ≤ s.2)

noncomputable def lineFirstArrival (I : LineInput) (B : Finset ℕ) : ℝ :=
  if h : B.Nonempty then (B.image I.arrival).min' (h.image I.arrival) else 0

/-- `g` plus the maximum delay `t − min a` of the cleared batch (`0` for an empty batch). -/
noncomputable def lineCharge (I : LineInput) (B : Finset ℕ) (s : LineService) : ℝ :=
  s.2 + if B = ∅ then 0 else s.1 - lineFirstArrival I B

noncomputable def lineTraceFrom (I : LineInput) :
    Finset ℕ → LineSchedule → List (LineService × Finset ℕ × ℝ)
  | _, [] => []
  | remaining, s :: rest =>
    let B := lineCleared I remaining s
    (s, B, lineCharge I B s) :: lineTraceFrom I (remaining \ B) rest

noncomputable def lineRemainingAfter (I : LineInput) : Finset ℕ → LineSchedule → Finset ℕ
  | remaining, [] => remaining
  | remaining, s :: rest => lineRemainingAfter I (remaining \ lineCleared I remaining s) rest

def LineFeasible (I : LineInput) (S : LineSchedule) : Prop :=
  S.Pairwise (fun s u => s.1 ≤ u.1) ∧ (∀ s ∈ S, 0 ≤ s.1 ∧ 0 ≤ s.2) ∧
    lineRemainingAfter I I.requests S = ∅

noncomputable def lineRawCost (I : LineInput) (S : LineSchedule) : ℝ :=
  ((lineTraceFrom I I.requests S).map (fun e => e.2.2)).sum

/-- Infeasible schedules cost `⊤`. -/
noncomputable def lineCost (I : LineInput) (S : LineSchedule) : ℝ≥0∞ := by
  classical
  exact if LineFeasible I S then ENNReal.ofReal (lineRawCost I S) else ⊤

/-- `OPT(I)`: the infimum over all finite schedules. -/
noncomputable def lineOptimum (I : LineInput) : ℝ≥0∞ :=
  ⨅ S : LineSchedule, lineCost I S

/-! Max-Balance, Appendix B.2, p. 22. -/

/-- The requests pending at time `t` just before any service at `t`: arrived by `t` (arrivals
at `t` are processed first) and not cleared by a service of `S` strictly before `t`. -/
noncomputable def linePendingAt (I : LineInput) (S : LineSchedule) (t : ℝ) : Finset ℕ := by
  classical
  exact (lineRemainingAfter I I.requests (S.filter (fun s => s.1 < t))).filter
    (fun r => I.arrival r ≤ t)

/-- `M(t, g) = max {t − a(r) : r pending at t, x(r) ≤ g}`, the empty maximum being `0`. -/
noncomputable def maxAge (I : LineInput) (S : LineSchedule) (t g : ℝ) : ℝ := by
  classical
  exact
    let P := (linePendingAt I S t).filter (fun r => I.location r ≤ g)
    if h : P.Nonempty then (P.image (fun r => t - I.arrival r)).max' (h.image _) else 0

/-- Level `g_i = 2^i` (`i ∈ ℤ`) is tight at `t` when `M(t, g_i) = g_i / 4`. -/
def LevelTight (I : LineInput) (S : LineSchedule) (t : ℝ) (i : ℤ) : Prop :=
  maxAge I S t ((2 : ℝ) ^ i) = (2 : ℝ) ^ i / 4

/-- `S` is the execution of Max-Balance on `I`: services occur at strictly increasing times;
each service at `t` has length `2^i` for the largest level `i ∈ ℤ` tight at `t`; and at every
time at which some level is tight, a service occurs. -/
def IsMaxBalanceRun (I : LineInput) (S : LineSchedule) : Prop :=
  S.Pairwise (fun s u => s.1 < u.1) ∧
  (∀ s ∈ S, ∃ i : ℤ, s.2 = (2 : ℝ) ^ i ∧ LevelTight I S s.1 i ∧
    ∀ i' : ℤ, LevelTight I S s.1 i' → i' ≤ i) ∧
  (∀ t : ℝ, ∀ i : ℤ, LevelTight I S t i → ∃ s ∈ S, s.1 = t)

end MLAMaxDelay.RandomizedTimer.Supplement


