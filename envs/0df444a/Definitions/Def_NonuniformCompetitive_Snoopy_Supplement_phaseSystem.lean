-- Prove2me | Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_phaseSystem
-- name    : NonuniformCompetitive_Snoopy_Supplement_phaseSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:56:29.625792+00:00
-- url     : https://prove2.me/theorems/a842ba4b-141e-4f6b-a8d1-805f09d517fc
-- title:
--   Causal phase parsing, uninteresting requests and phase-based policies
-- statement:
--   A finite phase alphabet consists of actual request words with known starting and ending states. A causal parser retains the current phase word, deletes designated uninteresting requests and detects completion after retained requests. Every listed phase is reachable, has positive finite offline cost, and has the forcing witnesses required at its endpoints. Every nonempty final remainder extends a listed phase. Finiteness supplies the uniform length and offline-cost bounds.
--
--   A local phase policy is an actual randomized causal algorithm for each start state, initialized there and agreeing almost surely with the designated endpoint after each listed phase. Its actions depend only on the current phase requests. The LP-bound set is
--   $$\{\alpha\in\mathbb R:\text{some local phase policy has attained LP minimum }\alpha\}.$$
--   All such policies are included, with no threshold-family restriction. Values on inputs outside the phase-prefix domain are unused; the policy is not required to extend transparently through requests the input restriction deletes. This is the phase-policy domain on p.547 and in the warm-up argument on pp.548–549.
--
--   For the global upper bound, a separate actual algorithm must match its local policy's primitive-action laws on retained requests, and deleted requests must be free and state-preserving for that algorithm while preserving the offline work profile. These are action conditions, not assumed cost bounds or competitive reductions. Before-request actions use only the preceding request prefix, including for look-ahead-zero tasks. The relational greatest lower bound avoids a default-valued real infimum.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, §2, pp.546–549

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_Supplement_phaseLP

namespace NonuniformCompetitive.Snoopy.Supplement

open MeasureTheory
open scoped NNReal ENNReal

attribute [local instance] TaskRandomized.ms

/-- State of the causal preprocessor. Only the current phase word is retained
for decisions. The list of completed descriptors is an observation log. -/
structure PhaseCursor (S R : Type) where
  state : S
  pending : List R
  complete : List (TaskPhase S R)

/-- A finite phase alphabet with causal deletion and end detection. Deletion is
decided when the request arrives, using only the current phase prefix. It does
not provide the request to the algorithm when choosing a before-request move. -/
structure PhaseSystem {S R : Type} (T : TaskSystem S R) (s₀ : S) where
  alphabet : List (TaskPhase S R)
  ignore : S → List R → R → Bool
  finish : S → List R → Option S

def PhaseSystem.step {S R : Type} {T : TaskSystem S R} {s₀ : S}
    (F : PhaseSystem T s₀) (q : PhaseCursor S R) (r : R) : PhaseCursor S R :=
  if F.ignore q.state q.pending r then q else
    let w := q.pending ++ [r]
    match F.finish q.state w with
    | none => { q with pending := w }
    | some t =>
        { state := t
          pending := []
          complete := q.complete ++ [{start := q.state, finish := t, word := w}] }

def PhaseSystem.runFrom {S R : Type} {T : TaskSystem S R} {s₀ : S}
    (F : PhaseSystem T s₀) (s : S) (h : List R) : PhaseCursor S R :=
  h.foldl F.step {state := s, pending := [], complete := []}

def PhaseSystem.run {S R : Type} {T : TaskSystem S R} {s₀ : S}
    (F : PhaseSystem T s₀) (h : List R) : PhaseCursor S R := F.runFrom s₀ h

/-- The word actually delivered by the preprocessor, including its final
incomplete phase. A deleted request contributes no letter. -/
def PhaseSystem.filtered {S R : Type} {T : TaskSystem S R} {s₀ : S}
    (F : PhaseSystem T s₀) (h : List R) : List R :=
  ((F.run h).complete.map TaskPhase.word).flatten ++ (F.run h).pending

/-- The restriction justified by Theorem 1: synchronize at every canonical
known state. This is defined by states, not by assuming phase reduction or
competitiveness. For the global upper bound it also describes the candidate algorithm after
the source restriction. The local LP policy space below requires only phase
endpoint synchronization, as in the two defining clauses on p.547. -/
def TaskNormalized {S R : Type} [LinearOrder S] {T : TaskSystem S R}
    (s₀ : S) (A : TaskRandomized T) : Prop :=
  (∀ i, (A.alg i).after [] = s₀) ∧
  ∀ (h : List R) (t : S), h ≠ [] → TaskKnown T s₀ h t →
    ∀ᵐ i ∂A.μ, (A.alg i).after h = t

/-- Full charged cost of the primitive actions at one request. -/
noncomputable def taskActionCost {S R : Type} {T : TaskSystem S R}
    (A : TaskOnline T) (h : List R) (r : R) : ℝ≥0∞ :=
  (T.distance (A.after h) (A.before h) : ℝ≥0∞) +
    (T.distance (A.before h) (A.moment (h ++ [r])) : ℝ≥0∞) +
    T.task r (A.moment (h ++ [r])) +
    (T.distance (A.moment (h ++ [r])) (A.after (h ++ [r])) : ℝ≥0∞)

/-- Source phase property, expressed through the operational parser and the
actual work function. No global algorithmic cost inequality is postulated.
Every member is a possible phase (not an extra LP constraint on an unreachable
word); every nonempty unfinished phase extends a member. The known-state
criterion is imposed at each completed boundary, not on an unrelated partition.
Deleted requests preserve the entire work profile, as required of requests that
are free and state-preserving for opt. Their on-line transparency is below. -/
def PhaseSystem.Valid {S R : Type} [LinearOrder S] {T : TaskSystem S R} {s₀ : S}
    (F : PhaseSystem T s₀) : Prop :=
  (∀ q ∈ F.alphabet, HasForcingWord T q.start ∧ HasForcingWord T q.finish) ∧
  (∀ q ∈ F.alphabet, TaskPhase.Valid T q ∧
    (F.runFrom q.start q.word).complete = [q] ∧
    (F.runFrom q.start q.word).pending = [] ∧
    ∃ h : List R, (F.run h).state = q.start ∧ (F.run h).pending = []) ∧
  (∀ h : List R, ∀ q ∈ (F.run h).complete, q ∈ F.alphabet) ∧
  (∀ h : List R, (F.run h).pending ≠ [] →
    ∃ q ∈ F.alphabet, q.start = (F.run h).state ∧
      (F.run h).pending.IsPrefix q.word) ∧
  (∀ h : List R, (F.run h).pending = [] →
    TaskRawKnown T s₀ h (F.run h).state ∧
      (h ≠ [] → TaskKnown T s₀ h (F.run h).state)) ∧
  (∀ (h : List R) (r : R), F.ignore (F.run h).state (F.run h).pending r = true →
    ∀ t : S, taskWork T s₀ (h ++ [r]) t = taskWork T s₀ h t)

/-- Observable primitive actions for one request. Including the state before
any pre-move distinguishes look-ahead-zero requests from look-ahead-one. -/
def taskActions {S R : Type} {T : TaskSystem S R} (A : TaskOnline T)
    (h : List R) (r : R) : S × S × S × S :=
  (A.after h, A.before h, A.moment (h ++ [r]), A.after (h ++ [r]))

/-- Phase-based mixed algorithms are actual causal task algorithms. The local
policy at each start is also an actual causal mixed algorithm, initialized at
that state and synchronizing almost surely at endpoints. For kept requests,
primitive-action laws agree with those of the current local policy. For erased
requests, all actions are stationary and the task is free, almost surely.
These are action-level conditions, not assumed cost equalities or assumed
competitiveness. Correlations between phases are unrestricted. -/
def IsPhaseBased {S R : Type} [LinearOrder S] {T : TaskSystem S R} {s₀ : S}
    (F : PhaseSystem T s₀) (localPolicy : S → TaskRandomized T)
    (A : TaskRandomized T) : Prop :=
  (∀ i, (A.alg i).after [] = s₀) ∧
  (∀ (s : S) (i : (localPolicy s).ι), ((localPolicy s).alg i).after [] = s) ∧
  (∀ q ∈ F.alphabet,
    ∀ᵐ i ∂(localPolicy q.start).μ, ((localPolicy q.start).alg i).after q.word = q.finish) ∧
  (∀ (h : List R) (r : R),
    let q := F.run h
    if F.ignore q.state q.pending r = true then
      ∀ᵐ i ∂A.μ,
        taskActionCost (A.alg i) h r = 0 ∧
        (A.alg i).after (h ++ [r]) = (A.alg i).after h
    else
      ∀ v : S × S × S × S,
        MeasurableSet {i | taskActions (A.alg i) h r = v} ∧
        MeasurableSet {i | taskActions ((localPolicy q.state).alg i) q.pending r = v} ∧
        A.μ {i | taskActions (A.alg i) h r = v} =
          (localPolicy q.state).μ {i | taskActions ((localPolicy q.state).alg i) q.pending r = v})

/-- A policy on the retained phase inputs: an actual causal mixed algorithm
for each possible start state, initialized there and synchronized at each listed
phase endpoint. Values outside phase prefixes are unused. This is the local
meaning of the two clauses defining a phase-based algorithm on p.547. No
extension through erased requests, global competitiveness, or normal-form
reduction is assumed. Every causal policy on this input domain is included. -/
def IsPhasePolicy {S R : Type} {T : TaskSystem S R} {s₀ : S}
    (F : PhaseSystem T s₀) (policy : S → TaskRandomized T) : Prop :=
  (∀ (s : S) (i : (policy s).ι), ((policy s).alg i).after [] = s) ∧
  ∀ q ∈ F.alphabet,
    ∀ᵐ i ∂(policy q.start).μ, ((policy q.start).alg i).after q.word = q.finish

/-- All local phase policies, rather than only policies with a prescribed
full-input extension. The source LP is evaluated on retained phases; excluded
requests do not add constraints to this optimization. Theorem 2 separately
handles a global implementation and its deletion transparency. `IsGLB` in
Theorem 3 avoids real sInf defaults on empty or unbounded sets. -/
def phaseBounds {S R : Type} {T : TaskSystem S R} {s₀ : S}
    (F : PhaseSystem T s₀) : Set ℝ :=
  {α | ∃ policy : S → TaskRandomized T,
    IsPhasePolicy F policy ∧
      IsPhaseLPBound T (fun q : {q : TaskPhase S R // q ∈ F.alphabet} => q.val) policy α}

end NonuniformCompetitive.Snoopy.Supplement


