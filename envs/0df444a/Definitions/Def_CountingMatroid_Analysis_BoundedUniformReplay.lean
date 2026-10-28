-- Prove2me | Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
-- name    : CountingMatroid_Analysis_BoundedUniformReplay
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:05:15.766799+00:00
-- url     : https://prove2.me/theorems/00ef8a55-f71b-40cd-bf83-92e7c292b529
-- title:
--   Interval replay for total tape-dependent outputs
-- statement:
--   Let $A$ be any type, let $f:(\mathbb N\to\{0,1\})\to A$, let $c:A\to\mathbb N$, and fix starting position $b\in\mathbb N$. Interval replay requires, for every tape $u$,
--   $$b\le c(f(u)),$$
--   and, for every other tape $v$,
--   $$u|_{[b,c(f(u)))}=v|_{[b,c(f(u)))}\Longrightarrow f(v)=f(u).$$
--   Unlike the successful-option predicate, this condition applies to every output of the supplied total function. It specifies cursor monotonicity and dependence on a half-open bit interval, not equality of operation charges or termination of an uncapped implementation.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/BoundedUniformReplay.lean#L14-L20

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
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section


set_option autoImplicit false

/-!
Deterministic locality of bounded rejection sampling. The cursor increases
monotonically, and agreement on the bits actually consumed determines the
whole value, including a rejected draw. No fair-bit law is assumed here.
-/

namespace CountingMatroid.Analysis.BoundedUniformReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: Cursor monotonicity and replay from the consumed half-open interval.
TEXLINE: main.tex:1392-1421 -/
def IntervalReplay {α : Type} (f : (ℕ → Bool) → α) (cursor : α → ℕ)
    (start : ℕ) : Prop :=
  ∀ tape, start ≤ cursor (f tape) ∧
    ∀ other, (∀ i, start ≤ i → i < cursor (f tape) → tape i = other i) →
      f other = f tape







end CountingMatroid.Analysis.BoundedUniformReplay

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r21 · proved · monotone interval replay for every bounded rejection outcome,
  by nested charged-fold induction, including exhausted rejection caps.
-/

end


