-- Prove2me | Definitions.Def_CountingMatroid_Analysis_OmittedRankWeightPolynomial
-- name    : CountingMatroid_Analysis_OmittedRankWeightPolynomial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:10:06.803251+00:00
-- url     : https://prove2.me/theorems/71c25ae0-f5de-4a99-bc56-d7dda3fbccf2
-- title:
--   The operational omitted-label rank-weight polynomial
-- statement:
--   Let $E=[n]\times\{0,1\}$, let $r\in\mathbb N$ be a rank parameter, let $o_1,o_2$ be Boolean independence oracles, and let $q\in\mathbb Q$. For a paired state $S\subseteq E$, its omitted exponent is the squarefree vector
--   $$e_S(a)=\begin{cases}1&a\notin S,\\0&a\in S.\end{cases}$$
--   The omitted-label polynomial is
--   $$F_q(z)=\sum_{\substack{S\subseteq E\\|S|=n}}
--   q^{\,n-\operatorname{pairedRank}_{r,o_1,o_2}(S)}
--   \prod_{a\in E\setminus S}z_a.$$
--   The deficiency uses truncated natural subtraction and the returned value of the program's paired-rank routine. The polynomial includes all states of cardinality $n$, without restricting to accepted classifier states. Each monomial has degree $n$; the definition assumes neither positivity of $q$ nor an exact-oracle connection to a mathematical matroid rank.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/OmittedRankWeightPolynomial.lean#L21-L25

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
import Definitions.Def_CountingMatroid_Analysis_ConditionalDefectCoefficients
import Definitions.Def_CountingMatroid_Analysis_FirstPhaseFailure
import Definitions.Def_CountingMatroid_Analysis_InitialMultipliersGood
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
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

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
The omitted-element rank-weight polynomial, expressed using the operational
paired-rank scan. Its coefficients below are identified with the operational
conditional defect totals. These identities do not assert a Hessian signature
or identify this scan with the rank of a matroid.
-/

namespace CountingMatroid.Analysis.OmittedRankWeightPolynomial

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open scoped BigOperators
open Classical

/-- INTERNAL: Squarefree exponent vector of the labels omitted by a state.
TEXLINE: main.tex:571-625 -/
noncomputable def omittedExponent {n : ℕ} (state : PairedSet n) :
    PairedGround n →₀ ℕ :=
  Finsupp.indicator (Finset.univ \ state) (fun _ _ => 1)





/-- INTERNAL: Operational version of the homogeneous omitted-element
rank-weight polynomial, before the paired-rank/matroid-rank bridge.
TEXLINE: main.tex:571-625 -/
noncomputable def omittedRankPolynomial {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) : MvPolynomial (PairedGround n) ℚ := by
  classical
  exact ∑ state : PairedSet n, if state.card = n then
    MvPolynomial.monomial (omittedExponent state)
      (q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val))
    else 0















end CountingMatroid.Analysis.OmittedRankWeightPolynomial

end


