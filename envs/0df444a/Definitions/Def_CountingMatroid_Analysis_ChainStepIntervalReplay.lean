-- Prove2me | Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
-- name    : CountingMatroid_Analysis_ChainStepIntervalReplay
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:05:53.111818+00:00
-- url     : https://prove2.me/theorems/17cfaf84-7d47-4bfe-a465-b0a5c76b738d
-- title:
--   Successful interval replay
-- statement:
--   Let $A$ be a type, $f:(\mathbb N\to\{0,1\})\to\operatorname{Option}(A)$ a tape-dependent output, $c:A\to\mathbb N$ its cursor, and $b\in\mathbb N$ a starting position. Successful interval replay requires, for every tape $u$ and successful output $a$,
--   $$f(u)=\operatorname{some}(a)\Longrightarrow b\le c(a),$$
--   and for every other tape $v$,
--   $$u|_{[b,c(a))}=v|_{[b,c(a))}\Longrightarrow f(v)=\operatorname{some}(a).$$
--   The condition says nothing about replay of absent outputs, whose cursors have been discarded, or about equality of operation charges.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ChainStepIntervalReplay.lean#L15-L21

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
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
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
Success-path replay for the charged chain step. A successful transition has
a monotone cursor and depends only on its consumed bit interval. The generic
option-fold lemma also retains the program's absorbing abort state.
-/

namespace CountingMatroid.Analysis.ChainStepIntervalReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.BoundedUniformReplay

/-- INTERNAL: Success-path interval replay when aborted outcomes discard their
cursor. This does not assert replay of an aborted outcome. -/
def SuccessReplay {α : Type} (f : (ℕ → Bool) → Option α)
    (cursor : α → ℕ) (start : ℕ) : Prop :=
  ∀ tape out, f tape = some out → start ≤ cursor out ∧
    ∀ other, (∀ i, start ≤ i → i < cursor out → tape i = other i) →
      f other = some out







end CountingMatroid.Analysis.ChainStepIntervalReplay

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r21 · proved · success-path replay for chainStep, by composing the hold bit,
  two index draws and optional rational acceptance draw. Kept charged Boolean
  tests intact while splitting branches to preserve their decidable instances.
-/

end


