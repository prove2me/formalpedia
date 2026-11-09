-- Prove2me | Definitions.Def_MatchingDelays_Linear_Execution
-- name    : MatchingDelays_Linear_Execution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:29.632638+00:00
-- url     : https://prove2.me/theorems/cbd048ec-0030-4f2b-ab60-d42cbfddb3b5
-- title:
--   Continuous growth and ordered event microsteps
-- statement:
--   An execution starts from the empty state at time zero. At a tied time it processes all due arrivals first, then tight-edge merges, then eligible matches until none remain. Arrivals create zero-dual singletons. A merge replaces two active components by their union, preserving inactive duals and recording its edge. Matching leaves components and dual growth unchanged. Between events,
--   $$y_S(t+h)=y_S(t)+\alpha h\,\mathbf1_{\{S\text{ active and odd}\}}.$$
--   The next time is the minimum of future arrivals and internal events; arrivals preempt the policy's internal alarm. With no event left, the stream stutters. Neither stuttering nor execution validity assumes a perfect output. A run is an infinite sequence of these microstates, with continuous linear interpolation at arbitrary real times. A completed state follows all same-time microsteps. Termination, completed-state existence, and perfect output remain theorem conclusions.
--
--   A separate relation records that tie choices follow one observation policy. Equal revealed prefixes permit different final sizes and different ambient metric extensions, supplying the vocabulary for the goal's causal invariance assertion. Default values for unestablished completed/final states are total-function conventions, discharged by the structural theorem.
-- source:
--   Ahmadian, Chawla, Kumar, Purohit, and Zhang, STOC 2027 submission #482 (October 2026), §3, printed pp.6–7 / PDF pp.7–8, Time and event convention; Appendix A, printed pp.20–21 / PDF pp.21–22. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/482.pdf

import Mathlib
import Definitions.Def_MatchingDelays_Linear_Policy

set_option autoImplicit false
open scoped BigOperators
open Classical
noncomputable section

namespace MatchingDelays.Linear


variable {n : ℕ} {X : Type*} [MetricSpace X]

def observation (I : Instance n X) (s : State) : Observation :=
  ⟨s, (fun u => if u ∈ s.arrived then arrival I u else 0),
      (fun u v => if u ∈ s.arrived ∧ v ∈ s.arrived then requestDist I u v else 0)⟩

def dueArrivals (I : Instance n X) (s : State) : Finset ℕ :=
  ((Finset.range n).filter (fun u => arrival I u ≤ s.time)) \ s.arrived

def arriveBatch (I : Instance n X) (s : State) : State :=
  let B := dueArrivals I s
  let singletons := B.image (fun u => ({u} : Finset ℕ))
  { s with arrived := s.arrived ∪ B
           active := s.active ∪ singletons
           historical := s.historical ∪ singletons
           y := fun S => if S ∈ singletons then 0 else s.y S }

def component (s : State) (u : ℕ) : Finset ℕ :=
  if h : ∃ C ∈ s.active, u ∈ C then Classical.choose h else ∅

def mergeState (s : State) (e : Edge) : State :=
  let C := component s e.1
  let D := component s e.2
  { s with active := insert (C ∪ D) ((s.active.erase C).erase D)
           historical := insert (C ∪ D) s.historical
           y := fun S => if S = C ∪ D then 0 else s.y S
           forest := insert e s.forest }

def matchState (s : State) (e : Edge) : State :=
  { s with matched := insert e s.matched
           matchTime := fun f => if f = e then s.time else s.matchTime f }

def grow (s : State) (t : ℝ) : State :=
  { s with time := t
           y := fun S => s.y S + if S ∈ s.active ∧ Odd S.card
                                   then alpha * (t - s.time) else 0 }

def futureTimes (I : Instance n X) (s : State) : Finset ℝ :=
  internalTimes (observation I s) ∪
    (((Finset.range n) \ s.arrived).image (arrival I)).filter (fun t => s.time < t)

/-- One microstep, with arrivals before merges before matches, or exact continuous
advance to the next event. Quiescent stuttering does not assume matching completion. -/
def Step (I : Instance n X) (s s' : State) : Prop :=
  if (dueArrivals I s).Nonempty then s' = arriveBatch I s
  else if (readyMerges (observation I s)).Nonempty then
    ∃ e ∈ readyMerges (observation I s), s' = mergeState s e
  else if (readyMatches (observation I s)).Nonempty then
    ∃ e ∈ readyMatches (observation I s), s' = matchState s e
  else if h : (futureTimes I s).Nonempty then
    s' = grow s ((futureTimes I s).min' h)
  else s' = s

abbrev Run := ℕ → State

def IsExecution (I : Instance n X) (R : Run) : Prop :=
  R 0 = emptyState ∧ ∀ k, Step I (R k) (R (k+1))

/-- Tie choices come from one observation policy, not from the unrevealed input. -/
def Follows (I : Instance n X) (π : Policy) (R : Run) : Prop :=
  ∀ k, ¬ (dueArrivals I (R k)).Nonempty →
    if (readyMerges (observation I (R k))).Nonempty then
      ∃ e ∈ readyMerges (observation I (R k)),
        π (observation I (R k)) = .merge e ∧ R (k+1) = mergeState (R k) e
    else if (readyMatches (observation I (R k))).Nonempty then
      ∃ e ∈ readyMatches (observation I (R k)),
        π (observation I (R k)) = .matchPair e ∧ R (k+1) = matchState (R k) e
    else π (observation I (R k)) = .waitUntil (nextInternal (observation I (R k)))

/-- Completed event state, interpolated linearly in open event intervals. -/
def CompletedAt (R : Run) (t : ℝ) (s : State) : Prop :=
  ∃ k, (R k).time ≤ t ∧
    (t < (R (k+1)).time ∨ R (k+1) = R k) ∧ s = grow (R k) t

def stateAt (R : Run) (t : ℝ) : State :=
  if h : ∃ s, CompletedAt R t s then Classical.choose h else emptyState

def Terminated (R : Run) : Prop :=
  ∃ k, ∀ j, k ≤ j → R j = R k

def finalState (R : Run) : State :=
  if h : ∃ k, R (k+1) = R k then R (Nat.find h) else emptyState

def PerfectOutput (I : Instance n X) (R : Run) : Prop :=
  IsPairing n (finalState R).matched ∧
  FeasibleTimes I (finalState R).matched (finalState R).matchTime

/-- Equal revealed prefixes allow different total sizes and different ambient spaces. -/
def SameInputThrough {m : ℕ} {Y : Type*} [MetricSpace Y]
    (I : Instance n X) (J : Instance m Y) (t : ℝ) : Prop :=
  (∀ u, (u < n ∧ arrival I u ≤ t) ↔ (u < m ∧ arrival J u ≤ t)) ∧
  (∀ u, u < n → arrival I u ≤ t → arrival I u = arrival J u) ∧
  (∀ u v, u < n → v < n → arrival I u ≤ t → arrival I v ≤ t →
    spatial I u v = spatial J u v)

end MatchingDelays.Linear


