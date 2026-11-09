-- Prove2me | Definitions.Def_MatchingDelays_Linear_Policy
-- name    : MatchingDelays_Linear_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:31.855194+00:00
-- url     : https://prove2.me/theorems/d5fd6b68-99d8-4ae8-8b36-37ac42371bc4
-- title:
--   Revealed observations and the deterministic Algorithms 1–2 policy
-- statement:
--   The growth rate is fixed to $\alpha=1/32$. A raw state records current real time, revealed arrival ranks, active and historical components, their dual values, merge edges, and irrevocable matches with their times. Its fields contain no correctness or performance conditions. An observation supplies this past state, revealed arrival times, and distances between revealed requests; auxiliary functions vanish outside revealed labels.
--
--   A tight edge between distinct active components is ready to merge. A pair of unmatched requests in one active component is ready to match when
--   $$t\ge\min(a_u,a_v)+2d(u,v).$$
--   Future internal alarms are computed from current linear dual growth and maturation times of already revealed pairs. The policy selects the lexicographically first ready merge, then the first ready match, or waits for its next internal alarm. It has no field for the final request count, future arrivals, unrevealed distances, or an end-of-input signal.
--
--   The same observation-to-decision function serves every input and ambient metric space. Exact real comparisons express the mathematical online algorithm.
-- source:
--   Ahmadian, Chawla, Kumar, Purohit, and Zhang, STOC 2027 submission #482 (October 2026), §3, printed pp.6–7 / PDF pp.7–8, Algorithms 1–2 and Eq. (4). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/482.pdf

import Mathlib
import Definitions.Def_MatchingDelays_Linear_Instance

set_option autoImplicit false
open scoped BigOperators
open Classical
noncomputable section

namespace MatchingDelays.Linear


def alpha : ℝ := 1 / 32

/-- Raw operational state, independent of the final input length and metric carrier.
There are deliberately no invariants or cost bounds in this record. -/
structure State where
  time : ℝ
  arrived : Finset ℕ
  active : Finset (Finset ℕ)
  historical : Finset (Finset ℕ)
  y : Finset ℕ → ℝ
  forest : Finset Edge
  matched : Finset Edge
  matchTime : Edge → ℝ

def emptyState : State := ⟨0, ∅, ∅, ∅, fun _ => 0, ∅, ∅, fun _ => 0⟩

def unmatched (s : State) : Finset ℕ :=
  s.arrived \ s.matched.biUnion endpoints

def crosses (e : Edge) (S : Finset ℕ) : Prop := (e.1 ∈ S) ≠ (e.2 ∈ S)
def load (s : State) (e : Edge) : ℝ :=
  ∑ S ∈ s.historical, if crosses e S then s.y S else 0

def sameComponent (s : State) (e : Edge) : Prop :=
  ∃ C ∈ s.active, e.1 ∈ C ∧ e.2 ∈ C

def separateComponents (s : State) (e : Edge) : Prop :=
  ∃ C ∈ s.active, ∃ D ∈ s.active, C ≠ D ∧ e.1 ∈ C ∧ e.2 ∈ D

/-- Only revealed arrival ranks, arrival times, pairwise distances, and past state.
The functions are masked to zero outside the revealed ranks. There is no end signal. -/
structure Observation where
  state : State
  a : ℕ → ℝ
  d : ℕ → ℕ → ℝ

def readyMerges (O : Observation) : Finset Edge :=
  (allPairs O.state.arrived).filter (fun e =>
    separateComponents O.state e ∧ load O.state e = O.d e.1 e.2)

def readyMatches (O : Observation) : Finset Edge :=
  (allPairs (unmatched O.state)).filter (fun e => sameComponent O.state e ∧
    min (O.a e.1) (O.a e.2) + 2 * O.d e.1 e.2 ≤ O.state.time)

def growthRate (s : State) (e : Edge) : ℝ :=
  ∑ S ∈ s.active, if Odd S.card ∧ crosses e S then alpha else 0

/-- Internal wake-up times use only already arrived endpoints. -/
def internalTimes (O : Observation) : Finset ℝ :=
  (((allPairs O.state.arrived).filter (fun e => separateComponents O.state e ∧
      0 < growthRate O.state e)).image (fun e =>
      O.state.time + (O.d e.1 e.2 - load O.state e) / growthRate O.state e) ∪
    ((allPairs (unmatched O.state)).filter (sameComponent O.state)).image
      (fun e => min (O.a e.1) (O.a e.2) + 2 * O.d e.1 e.2)).filter
        (fun t => O.state.time < t)

def nextInternal (O : Observation) : Option ℝ :=
  if h : (internalTimes O).Nonempty then some ((internalTimes O).min' h) else none

inductive Decision where
  | merge : Edge → Decision
  | matchPair : Edge → Decision
  | waitUntil : Option ℝ → Decision

abbrev Policy := Observation → Decision

def chooseEdge (E : Finset Edge) (h : E.Nonempty) : Edge :=
  ofLex ((E.image (toLex : Edge → Lex Edge)).min' (h.image _))

/-- Deterministic lexicographic choices on revealed arrival ranks. -/
def algorithmPolicy : Policy := fun O =>
  if h : (readyMerges O).Nonempty then .merge (chooseEdge (readyMerges O) h)
  else if h : (readyMatches O).Nonempty then .matchPair (chooseEdge (readyMatches O) h)
  else .waitUntil (nextInternal O)

end MatchingDelays.Linear


