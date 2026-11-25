-- Prove2me | Definitions.Def_DetDLP_D4Transcript
-- name    : DetDLP_D4Transcript
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:31:22.015841+00:00
-- url     : https://prove2.me/theorems/c7d621fa-e15a-4847-9b4f-b287564f490c
-- title:
--   Word and resource invariant for guarded terminal controller transcripts
-- statement:
--   A finite interaction certificate carries the controller state, prior oracle answer, final word and a uniform bound on stored word lengths. At each transition the state either halts or issues a bounded call and continues from its result.

import Definitions.Def_DetDLP_Machine
set_option autoImplicit false
namespace DetDLP.D4Transcript
open OAI.Algorithms.SubexponentialSAT.Computation
abbrev W := List Bool
def pair (x y : W) : W := x.flatMap (fun b => [true,b]) ++ [false] ++ y
/-- Each successor is a local controller transition or a successful final readout.
The same word-length cap applies throughout; only oracle time may be exponential. -/
def run (step : W → W) (O : PrimitiveMachine) (o : Fin O.tapeCount) (τ σ : ℝ) : ℕ → W → W → W → ℕ → Prop :=
  Nat.rec (motive := fun _ => W → W → W → ℕ → Prop) (fun _ _ _ _ => False)
    (fun _ prev st ans out maxLen =>
      (step (pair st ans) = true :: out ∧ (pair st ans).length ≤ maxLen ∧ out.length ≤ maxLen) ∨
      ∃ st' q ans', step (pair st ans) = false :: pair st' q ∧ (pair st ans).length ≤ maxLen ∧
        (pair st' q).length ≤ maxLen ∧ ans'.length ≤ maxLen ∧ RunsWithin O o q ans' τ σ ∧
        prev st' ans' out maxLen)
end DetDLP.D4Transcript


