-- Prove2me | Definitions.Def_Freiman_backgroundWords
-- name    : Freiman_backgroundWords
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T10:44:00.824652+00:00
-- url     : https://prove2.me/theorems/7f4d2514-7afc-4874-9683-3a7bad3221c3
-- title:
--   Five-state forbidden-word automaton and the background reference tails
-- statement:
--   Concrete data for the proof of report Lemma 1.7: one-sided block avoidance, the five suffix states of 31313 and their transition table, the periodic reference words 13, 131312 and 131213, their six-step phase lists, and the two outward tails of a two-sided word. The Boolean false reference starts from the empty state and is T; true starts from state 3 and is U. All definitions are explicit and contain no proof assumptions.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.4, Lemma 1.7, printed pp. 11–12.

import Definitions.Def_Freiman_wordRealization
import Definitions.Def_Freiman_gapModel

namespace Freiman

def OneSidedMatchesBlock (b : ℕ → ℕ+) (w : List ℕ) (i : ℕ) : Prop :=
  ∀ k : ℕ, k < w.length → (b (i + k) : ℕ) = w.getD k 0

def OneSidedAvoidsBlock (b : ℕ → ℕ+) (w : List ℕ) : Prop :=
  ∀ i : ℕ, ¬ OneSidedMatchesBlock b w i

def backgroundPrepend (w : List ℕ+) (b : ℕ → ℕ+) : ℕ → ℕ+ :=
  fun n => if n < w.length then w.getD n 1 else b (n - w.length)

inductive BackgroundState
  | empty | three | threeOne | threeOneThree | threeOneThreeOne
  deriving DecidableEq, Inhabited

def backgroundStateWord : BackgroundState → List ℕ+
  | .empty => []
  | .three => [3]
  | .threeOne => [3,1]
  | .threeOneThree => [3,1,3]
  | .threeOneThreeOne => [3,1,3,1]

def backgroundStep : BackgroundState → ℕ+ → Option BackgroundState
  | .empty, d => if (d : ℕ) = 3 then some .three else some .empty
  | .three, d => if (d : ℕ) = 1 then some .threeOne
      else if (d : ℕ) = 3 then some .three else some .empty
  | .threeOne, d => if (d : ℕ) = 3 then some .threeOneThree else some .empty
  | .threeOneThree, d => if (d : ℕ) = 1 then some .threeOneThreeOne
      else if (d : ℕ) = 3 then some .three else some .empty
  | .threeOneThreeOne, d => if (d : ℕ) = 3 then none else some .empty

def backgroundRun (s : BackgroundState) (w : List ℕ+) : Option BackgroundState :=
  w.foldl (fun q d => q.bind (fun q' => backgroundStep q' d)) (some s)

def BackgroundAllowed (s : BackgroundState) (b : ℕ → ℕ+) : Prop :=
  ∀ n : ℕ, backgroundRun s ((List.range n).map b) ≠ none

def backgroundPeriod13 : ℕ → ℕ+ := gapEventuallyPeriodic [] [1,3]
def backgroundT : ℕ → ℕ+ := gapEventuallyPeriodic [] [1,3,1,3,1,2]
def backgroundU : ℕ → ℕ+ := gapEventuallyPeriodic [] [1,3,1,2,1,3]
def background12 : ℕ → ℕ+ := gapEventuallyPeriodic [1,2] [1,3,1,3,1,2]

def backgroundReference (r : Bool) : ℕ → ℕ+ := if r then backgroundU else backgroundT
def backgroundReferenceState (r : Bool) : BackgroundState := if r then .three else .empty

def backgroundPhaseState (r : Bool) (n : ℕ) : BackgroundState :=
  if r then
    ([.three, .threeOne, .threeOneThree, .threeOneThreeOne, .empty, .empty] :
      List BackgroundState).getD (n % 6) .empty
  else
    ([.empty, .empty, .three, .threeOne, .threeOneThree, .threeOneThreeOne] :
      List BackgroundState).getD (n % 6) .empty

def BackgroundCandidate (r : Bool) (n : ℕ) (d : ℕ+) : Prop :=
  (d : ℕ) ≤ 4 ∧ backgroundStep (backgroundPhaseState r n) d ≠ none ∧
    (¬ Even n → d ≠ 4)

def backgroundOutward (a : ℤ → ℕ+) (i : ℤ) (right : Bool) : ℕ → ℕ+ :=
  fun n => if right then a (i + (n : ℤ) + 1) else a (i - (n : ℤ) - 1)

end Freiman


