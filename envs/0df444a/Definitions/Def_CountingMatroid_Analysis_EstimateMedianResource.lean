-- Prove2me | Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
-- name    : CountingMatroid_Analysis_EstimateMedianResource
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T12:51:42.888588+00:00
-- url     : https://prove2.me/theorems/e997719c-d0d0-4db4-93d6-4f980dce3035
-- title:
--   Additivity of instruction tallies and nonoracle work
-- statement:
--   This bundle supplies two additive accounting lemmas. Let $\mathcal O$ be the type of named instructions in the supporting computation library, let $l$ be a finite list of such instructions, let $f,g:\mathcal O\to\mathbb N$ assign counts to instructions, and let $a,b\in\mathbb N$ be initial tallies. Write $T_l(f,a)$ for the result of starting at $a$ and, for each occurrence of an instruction $x$ in $l$, adding $f(x)$. Then
--
--   $$T_l(f+g,a+b)=T_l(f,a)+T_l(g,b),$$
--
--   where $(f+g)(x)=f(x)+g(x)$. The list may contain repeated instructions; every occurrence contributes to its tally.
--
--   For a charged computation $p$, write $V(p)$ for its returned value and $C_p(o)$ for the count of an operation label $o$. The counting algorithm's nonoracle charge is
--
--   $$W(p)=C_p(\mathrm{fairBit})+\sum_{x\in\mathcal O}C_p(\mathrm{word}(x)).$$
--
--   Here $\mathrm{fairBit}$ labels a tape-bit read, and $\mathrm{word}(x)$ labels the named instruction $x$. Calls to the two independence oracles have separate labels and do not contribute to $W$.
--
--   Let $A,B$ be arbitrary value types, let $p$ be a charged computation returning a value in $A$, and let $F$ assign to every $v\in A$ a charged computation returning a value in $B$, all using the counting algorithm's operation and storage types. If $p\mathbin{\gg=}F$ denotes sequencing $p$ with the continuation evaluated at its returned value, then
--
--   $$W(p\mathbin{\gg=}F)=W(p)+W(F(V(p))).$$
--
--   The first lemma follows by induction over the instruction list. The second applies that tally identity to the componentwise addition of cost vectors under sequencing and adds the fair-bit contribution. These are identities in the abstract charged-operation model; they do not assert a concrete bit-cost or physical-memory realization.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/EstimateMedianResource.lean#L18-L41

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
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

namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section


/-!
# Resource bounds for the charged rational median

The insertion scan preserves sorted values and has polynomial charged cost
when its input rational encodings have a common bound.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

/-- INTERNAL: The word-operation fold in `otherSteps` distributes over
two charged cost vectors. -/
theorem foldl_word_add (l : List Arlib.Computation.Op)
    (f g : Arlib.Computation.Op → ℕ) :
    ∀ a b, l.foldl (fun z x => z + (f x + g x)) (a + b) =
      l.foldl (fun z x => z + f x) a + l.foldl (fun z x => z + g x) b := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      intro a b
      simpa [List.foldl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (a + f x) (b + g x)

/-- INTERNAL: Nonoracle charges add when charged computations are sequenced. -/
theorem otherSteps_bind {α β : Type}
    (p : Arlib.Computation.Charged Op Cell α)
    (f : α → Arlib.Computation.Charged Op Cell β) :
    otherSteps (p >>= f) = otherSteps p + otherSteps (f p.val) := by
  simp only [otherSteps, Arlib.Computation.Charged.cost_bind, Pi.add_apply]
  have h := foldl_word_add Arlib.Computation.Op.all
    (fun x => p.cost (Op.word x)) (fun x => (f p.val).cost (Op.word x)) 0 0
  simp only [Nat.zero_add] at h
  rw [h]
  omega















end CountingMatroid.Analysis.ResourceBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · proved · extracted and closed the median length, sign, and charge invariants used by the estimator.
-/

end


