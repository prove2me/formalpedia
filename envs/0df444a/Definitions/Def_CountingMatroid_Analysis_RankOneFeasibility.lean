-- Prove2me | Definitions.Def_CountingMatroid_Analysis_RankOneFeasibility
-- name    : CountingMatroid_Analysis_RankOneFeasibility
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:05:45.379596+00:00
-- url     : https://prove2.me/theorems/fc1a3418-73cd-4f36-b625-832e1d772a00
-- title:
--   Charged scan for a commonly accepted singleton
-- statement:
--   Let $G=\{0,\ldots,n-1\}$ and let $o_1,o_2$ be arbitrary Boolean subset oracles. A singleton step takes a Boolean accumulator $f$ and a ground element $i$, constructs and encodes $\{i\}$, queries both oracles, and returns
--   $$
--   f'=f\lor\bigl(o_1(\{i\})\land o_2(\{i\})\bigr).
--   $$
--   The full singleton scan folds this step over the ordered list $0,\ldots,n-1$, starting with false:
--   $$
--   \operatorname{singletonScan}(o_1,o_2).\mathrm{val}
--   =\bigvee_{i\in G}\bigl(o_1(\{i\})\land o_2(\{i\})\bigr).
--   $$
--   Every listed singleton is tested, even after the accumulator becomes true. Set construction, query encoding, oracle calls, and Boolean operations carry abstract charges. The finite scan requires no matroid promise; interpreting oracle acceptance as independence requires additional assumptions.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RankOneFeasibility.lean#L18-L28

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Subroutines
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace Arlib
end Arlib
section


set_option autoImplicit false

/-!
The first augmentation from the empty common independent set can be found by
scanning singleton queries. This file implements that scan through the two
original charged oracles. It handles rank one, including infeasible inputs;
it does not implement subsequent augmentations for larger ranks.
-/

namespace CountingMatroid.Analysis.RankOneFeasibility

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open scoped Classical

/-- INTERNAL: Test one singleton through both original oracles and retain the
Boolean recording whether the scan has found a common independent singleton.
TEXLINE: main.tex:283-289 -/
def singletonStep {n : ℕ} (o₁ o₂ : IndependenceOracle n)
    (found : Bool) (i : Fin n) : Arlib.Computation.Charged Op Cell Bool := do
  let candidate ← insertElement ∅ i
  let query ← encodeQuery candidate
  let first ← oracleQuery false o₁ query
  let second ← oracleQuery true o₂ query
  let common ← Arlib.Computation.Charged.op (Op.word .band) (first && second)
  Arlib.Computation.Charged.op (Op.word .bor) (found || common)

/-- INTERNAL: Bounded scan for the first possible common-independent-set
augmentation. No matroid promise is needed for termination.
TEXLINE: main.tex:283-289 -/
def singletonScan {n : ℕ} (o₁ o₂ : IndependenceOracle n) :
    Arlib.Computation.Charged Op Cell Bool :=
  Arlib.Computation.Charged.foldl (singletonStep o₁ o₂) (List.finRange n) false







end CountingMatroid.Analysis.RankOneFeasibility

end


