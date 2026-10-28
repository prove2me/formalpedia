-- Prove2me | Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
-- name    : CountingMatroid_Analysis_BoundedUniformAbortMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:08:13.858987+00:00
-- url     : https://prove2.me/theorems/71b7e743-a5c6-4fe2-bd13-2f46efa3c7e2
-- title:
--   Word scanning, rejection trials, and adaptive abort histories
-- statement:
--   Let $b:\mathbb N\to\{0,1\}$ be a Boolean tape. The word reader starts with a natural accumulator $v$ and cursor $c$, and repeats the update $(v,c)\mapsto(2v+b(c),c+1)$ exactly $k$ times. Its recursion and included bound are
--   $$R_0(v,c)=(v,c),\qquad R_{k+1}(v,c)=R_k(2v+b(c),c+1),\qquad
--   \bigl(R_k(v,c)\bigr)_1<(v+1)2^k.$$
--   For a natural sampling range $a$, put $w(a)=\lfloor\log_2(a-1)\rfloor+1$, using truncated natural subtraction and the library's natural logarithm convention. The trial loop maintains an optional accepted integer and a cursor. An already accepted value is preserved; otherwise it reads $w(a)$ bits from accumulator zero and accepts the word precisely when it is below $a$. It repeats at most the supplied number of trials.
--
--   For a fixed earlier tape prefix $p$, suffix budget $t$, and trial count $m$, a draw history consists of a finite prefix-free family $\mathcal H$ of Boolean lists and a denominator $a(h)>0$ for each $h\in\mathcal H$, satisfying
--   $$|h|\leq t,\qquad m\,w(a(h))\leq t-|h|.$$
--   For a Boolean list $u$, its abort event means that some $h\in\mathcal H$ is a prefix of $u$ and the actual bounded-uniform sampler, on the false-padded tape $p\,u$, fails with range $a(h)$, trial cap $m$, and starting cursor $|p|+|h|$. The event definition itself does not require $|u|=t$. These objects describe the operational stopping prefixes; no abort-probability estimate is asserted in this bundle.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedUniformAbortMass.lean#L18-L23

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhase
import Definitions.Def_CountingMatroid_Analysis_BoundedRunPhaseHistory
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Definitions.Def_CountingMatroid_Analysis_ScheduleConfidence
import Definitions.Def_CountingMatroid_Analysis_TransversalPartition
import Definitions.Def_CountingMatroid_Analysis_TransversalProjection
import Definitions.Def_CountingMatroid_Interface_Pseudocode
import Definitions.Def_CountingMatroid_Interface_Pseudocode_Extension1
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.InitialRestartLaw
end CountingMatroid.Analysis.InitialRestartLaw
namespace CountingMatroid.Interface
end CountingMatroid.Interface
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.TransversalRankBridge
end CountingMatroid.Analysis.TransversalRankBridge
namespace CountingMatroid.Analysis.GreedyRankCorrect
end CountingMatroid.Analysis.GreedyRankCorrect
section


set_option autoImplicit false

/-!
Finite-bit rejection-cap bounds for the actual charged integer sampler.
A rejected trial has a true leading bit: a false leading bit produces an
integer below the positive denominator. Distinct trials use disjoint words.
Coverage is an explicit premise here; obtaining it for adaptive calls in a
whole phase restart remains an obligation of the consuming analysis.
-/

namespace CountingMatroid.Analysis.BoundedUniformAbortMass

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: Value semantics of the sampler's inner fixed-width bit scan.
TEXLINE: main.tex:1392-1401 -/
def readWord (tape : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, value, cursor => (value, cursor)
  | k + 1, value, cursor =>
      readWord tape k (2 * value + if tape cursor then 1 else 0) (cursor + 1)



/-- INTERNAL: Appending k Boolean digits stays below the next binary boundary. -/
theorem readWord_lt (tape : ℕ → Bool) (k value cursor : ℕ) :
    (readWord tape k value cursor).1 < (value + 1) * 2 ^ k := by
  induction k generalizing value cursor with
  | zero => simp [readWord]
  | succ k ih =>
      simp only [readWord]
      have h := ih (2 * value + if tape cursor then 1 else 0) (cursor + 1)
      rw [pow_succ]
      have hb : (if tape cursor then 1 else 0 : ℕ) ≤ 1 := by split <;> omega
      nlinarith [(by positivity : 0 < 2 ^ k)]





/-- INTERNAL: Value semantics of the absorbing rejection-trial loop.
TEXLINE: main.tex:1392-1401 -/
def sampleWords (tape : ℕ → Bool) (v : ℕ) : ℕ → Option ℕ × ℕ → Option ℕ × ℕ
  | 0, acc => acc
  | k + 1, acc =>
      sampleWords tape v k (if acc.1.isSome then acc else
        let word := readWord tape ((v - 1).log2 + 1) 0 acc.2
        if word.1 < v then (some word.1, word.2) else (none, word.2))




  








/-- INTERNAL: A finite stopping-prefix description of one adaptive integer
call, including the positive denominator fixed at that prefix and the coverage
needed to read every permitted rejection trial. Relative prefixes are taken
after the fixed earlier tape `base`.
TEXLINE: main.tex:1415-1421 -/
structure DrawHistory (base : List Bool) (t trials : ℕ) where
  prefixes : Finset (List Bool)
  denominator : List Bool → ℕ
  positive : ∀ head ∈ prefixes, 0 < denominator head
  length_le : ∀ head ∈ prefixes, head.length ≤ t
  prefix_free : ∀ a ∈ prefixes, ∀ b ∈ prefixes, a <+: b → a = b
  coverage : ∀ head ∈ prefixes,
    trials * ((denominator head - 1).log2 + 1) ≤ t - head.length

/-- INTERNAL: Actual rejection-cap aborts at the stopping prefixes of an
adaptive integer call. No synthetic randomness replaces the original tape. -/
def DrawHistory.abortEvent {base : List Bool} {t trials : ℕ}
    (history : DrawHistory base t trials) (bits : List Bool) : Prop :=
  ∃ head ∈ history.prefixes, head <+: bits ∧
    (boundedUniform (fun i => ((base ++ bits)[i]?).getD false)
      trials (history.denominator head) (base.length + head.length)).val.1 = none



end CountingMatroid.Analysis.BoundedUniformAbortMass

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r26 · proved · identified the charged word and rejection loops, proved that every aborted trial has a true leading bit, counted the distinct forced coordinates, and transferred the resulting cap bound to covered prefix-free adaptive histories.
-/

end


