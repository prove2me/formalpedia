-- Prove2me | Definitions.Def_CountingMatroid_Analysis_FiniteSuffixDrawAbortMass
-- name    : CountingMatroid_Analysis_FiniteSuffixDrawAbortMass
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:09:11.051037+00:00
-- url     : https://prove2.me/theorems/abecfde2-cdb4-4762-8ca3-3ac857f5816f
-- title:
--   Covered prefix-free families of draw sites
-- statement:
--   For a trial cap $T\in\mathbb N$ and suffix length $t\in\mathbb N$, a draw-prefix cover consists of a finite family $\mathcal H$ of Boolean lists and a denominator assignment $v(h)\in\mathbb N$ to all Boolean lists. For each $h\in\mathcal H$, it requires
--   $$v(h)>0,\qquad |h|+T\bigl(\lfloor\log_2(v(h)-1)\rfloor+1\bigr)\le t.$$
--   The natural logarithm convention is $\log_2 0=0$, so the prescribed width is at least one. Prefix-freeness requires
--   $$h,h'\in\mathcal H,\quad h\text{ prefixes }h'\Longrightarrow h=h'.$$
--   The lists are relative to an external consumed prefix. The structure records positivity, coverage, and prefix-freeness only; it does not itself certify that these histories are reachable in a program or cover every possible draw.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FiniteSuffixDrawAbortMass.lean#L66-L76

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformAbortMass
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
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

namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
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
Finite fair-suffix rejection bounds for the actual charged integer sampler.
The single-call bound uses the proved forced-leading-bit count for covered
rejection trials. The prefix-cylinder transfer below separates this stochastic
bound from the program's reachability and finite-block coverage proof.
-/

namespace CountingMatroid.Analysis.FiniteSuffixDrawAbortMass

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteTapePrefixBound





/-- INTERNAL: A finite prefix-free family of reached draw histories, with
positive denominators and room for all capped trials in the remaining tape.
The histories are relative to a fixed external consumed prefix.
TEXLINE: main.tex:1392-1421 -/
structure DrawPrefixCover (trials t : ℕ) where
  prefixes : Finset (List Bool)
  denominator : List Bool → ℕ
  positive : ∀ head ∈ prefixes, 0 < denominator head
  covered : ∀ head ∈ prefixes,
    head.length + trials * ((denominator head - 1).log2 + 1) ≤ t
  prefix_free : ∀ a ∈ prefixes, ∀ b ∈ prefixes, a <+: b → a = b



end CountingMatroid.Analysis.FiniteSuffixDrawAbortMass

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r27 · proved · closed the covered single-call ENNReal abort bound using the existing rational rejection-cap theorem and finite-mass conversion; no new proof obligations.

* r26 · proved · prefix-cylinder summation transfers the single-call bound to adaptive positive denominators, retaining finite coverage explicitly.

* r26 · decomposed · separated covered rejection sampling from operational reachability; zero-trial and singleton-denominator cases proved, positive-trial counting and adaptive prefix transfer open.
-/

end


