-- Prove2me | Definitions.Def_CoarseMatching_LowerBound_StreamingMachine
-- name    : CoarseMatching_LowerBound_StreamingMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:34:23.584058+00:00
-- url     : https://prove2.me/theorems/b5b67560-2caa-43b7-9731-20d189e53dfe
-- title:
--   Bounded-memory randomized numerical streaming machines
-- statement:
--   A numerical streaming machine has an update alphabet, public parameters, and $S$ stored bits. Its state space has exactly $2^S$ available states; smaller state spaces embed by leaving states unused. Initialization is an input-independent distribution depending only on public parameters. A transition sees only those parameters, the public pass index, the retained state, and the current update, and draws its new state from a probability law. The final state determines a probability measure on real-valued outputs.
--
--   $$q_{k,j+1}=q_{k,j}\mathbin{\mathrm{bind}}\bigl(x\mapsto T_k(x,u_j)\bigr).$$
--
--   A pass reads the same stream forward again, carrying state between passes. Fresh coins and unlimited computation are permitted; all retained input-dependent information and retained private random bits occupy the counted state. The public pass index is free and known in the communication simulation. No position counter, stream length, hidden core, future input or input-dependent advice is supplied.
--
--   This is a reusable operational numerical streaming model. Probability normalization is part of the types of initialization, transitions, and the real output law.
-- source:
--   Gillat Kol, Even Coarse Matching Estimates Require Nearly Linear Streaming Space, STOC 2027 submission #1135 (October 2026), §1.1 and §4.2, printed pp.1,13 (PDF pp.2,14). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1135.pdf

import Mathlib

open MeasureTheory

namespace CoarseMatching.LowerBound
noncomputable section

/-- Exactly the capacity of S stored bits, with arbitrary unused states allowed. -/
abbrev Memory (S : ℕ) := Fin (2 ^ S)

/-- Kol §1.1 and §4.2: input-local multipass numerical estimation. All retained
input-dependent information is in Memory S. Transitions use fresh randomness;
any retained random bits are in that same state. No computation-time bound.
The public pass index is allowed, and is known in the communication simulation.
The initial distribution depends only on the public partition. -/
structure StreamingMachine (Input Params : Type) (S : ℕ) where
  initial : Params → PMF (Memory S)
  step : Params → ℕ → Memory S → Input → PMF (Memory S)
  output : Params → Memory S → ProbabilityMeasure ℝ

/-- Re-read the identical fixed stream on each pass, retaining state. -/
def StreamingMachine.states {Input Params : Type} {S : ℕ} (A : StreamingMachine Input Params S) (p : ℕ)
    (color : Params) (s : List (Input)) : PMF (Memory S) :=
  (List.range p).foldl (fun q k =>
    s.foldl (fun q u => q.bind (fun st => A.step color k st u)) q) (A.initial color)

/-- A genuine probability measure on real-valued estimates, including randomized output. -/
def StreamingMachine.law {Input Params : Type} {S : ℕ} (A : StreamingMachine Input Params S) (p : ℕ)
    (color : Params) (s : List (Input)) : ProbabilityMeasure ℝ :=
  ⟨(A.states p color s).toMeasure.bind (fun st => (A.output color st : Measure ℝ)),
    isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
      (Filter.Eventually.of_forall (fun st => (A.output color st).prop))⟩

end
end CoarseMatching.LowerBound


