-- Prove2me | Definitions.Def_CountingMatroid_Analysis_StoppedDrawHistory
-- name    : CountingMatroid_Analysis_StoppedDrawHistory
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:09:19.515995+00:00
-- url     : https://prove2.me/theorems/f6c40985-aab9-4412-a840-8c54444ce9d0
-- title:
--   A stopped draw descriptor with replay and coverage
-- statement:
--   For natural numbers $t$ and $d$, a stopped draw consists of a partial descriptor
--   $$
--   \operatorname{site}:\operatorname{List}(\{0,1\})
--   \longrightarrow\operatorname{Option}
--   \bigl(\operatorname{List}(\{0,1\})\times\mathbb N\bigr)
--   $$
--   with four obligations. Whenever a list $v$ has length $t$ and $\operatorname{site}(v)=\operatorname{some}(u,m)$, the list $u$ is a prefix of $v$, the denominator $m$ is positive, and
--   $$
--   d\bigl(\log_2(m-1)+1\bigr)\le t-|u|.
--   $$
--   Moreover, for every other length-$t$ list sharing prefix $u$, the descriptor is exactly the same pair $(u,m)$. Thus the selected denominator and consumed relative prefix are fixed before the subsequent trial bits. The logarithm and subtraction are natural-number operations. The structure constrains descriptors only on lists of length $t$; it does not itself provide a probability estimate.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/StoppedDrawHistory.lean#L11-L21

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
A deterministic stopping descriptor separates operational replay from the
finite prefix-free packaging required by the adaptive draw mass bound.
-/
namespace CountingMatroid.Analysis.StoppedDrawHistory

/-- INTERNAL: One partial pre-draw descriptor on fixed-length suffixes.
Replay fixes both the consumed relative prefix and the denominator before
reading any trial bits. TEXLINE: main.tex:1415-1421 -/
structure StoppedDraw (t trials : ℕ) where
  site : List Bool → Option (List Bool × ℕ)
  isPrefix : ∀ bits head v, bits.length = t → site bits = some (head, v) → head <+: bits
  stable : ∀ bits other head v, bits.length = t → other.length = t →
    site bits = some (head, v) → head <+: other → site other = some (head, v)
  positive : ∀ bits head v, bits.length = t → site bits = some (head, v) → 0 < v
  coverage : ∀ bits head v, bits.length = t → site bits = some (head, v) →
    trials * ((v - 1).log2 + 1) ≤ t - head.length



end CountingMatroid.Analysis.StoppedDrawHistory

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · finite stopping descriptors yield prefix-free covered histories; replay determines a unique denominator on each prefix.
-/

end


