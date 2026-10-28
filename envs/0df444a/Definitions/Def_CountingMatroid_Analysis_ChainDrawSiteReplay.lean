-- Prove2me | Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
-- name    : CountingMatroid_Analysis_ChainDrawSiteReplay
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:06:20.269112+00:00
-- url     : https://prove2.me/theorems/9b732fb5-c0e9-4854-835d-bafd90f5f001
-- title:
--   Descriptors of the three draw sites in a chain attempt
-- statement:
--   Let $n,r\in\mathbb N$ and let $o_1,o_2$ be Boolean query functions on subsets of $[n]=\{0,\ldots,n-1\}$. Put $E=[n]\times\{0,1\}$, let paired states be subsets of $E$, and write $d(S)=n-\operatorname{pairedRank}(r,o_1,o_2,S)$ using truncated natural subtraction. A transversal has one label in each pair; a defect $(i,k)$ has empty pair $i$, full pair $k$, and one label elsewhere, with $i\ne k$. Fix a Boolean tape, schedule $s$, rational parameter $q$, rational defect weights, state $S$, starting cursor $c$, and site selector $a\in\{0,1,2\}$. The descriptor is an optional pair
--   $$(b,v)\in\mathbb N^2,$$
--   representing a draw's starting bit position and denominator. If the lazy bit at $c$ is true, no draw site is reported. Otherwise the cursor advances by one. Site zero reports $(c+1,n)$ before the first capped index draw. Site one runs that first draw and, if it succeeds, reports its final cursor with denominator $n$ before the second draw.
--   Site two runs both index draws, selects the occupied and unoccupied labels, forms the proposed exchange, and requires a valid candidate and successful old/new weight evaluations. For their ratio $\theta$, it reports
--   $$(b,\operatorname{den}(\theta))\quad\text{only when }\theta<1,$$
--   where $b$ is the cursor after the index draws. Otherwise it returns none. Earlier failed steps also produce none. The reported draw's own trial bits have not been inspected; the definition alone supplies neither positive denominators for all sites nor a probability bound.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/ChainDrawSiteReplay.lean#L13-L38

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
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
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
Pre-draw descriptors for a chain attempt. They record the next capped draw's
cursor and denominator without reading any bits of that draw.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid.Model CountingMatroid.Program

/-- INTERNAL: Stop before one of the three actual capped draws in a chain
attempt. No bits of the reported draw itself have been inspected.
TEXLINE: main.tex:746-751,1392-1421 -/
noncomputable def chainDrawSite {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (cursor : ℕ) (site : Fin 3) : Option (ℕ × ℕ) := do
  if tape cursor then none else
    let cursor := cursor + 1
    if site.val = 0 then some (cursor, n) else
      let selected := (boundedUniform tape s.drawTrials n cursor).val
      let aIndex ← selected.1
      if site.val = 1 then some (selected.2, n) else
        let selectedOut := (boundedUniform tape s.drawTrials n selected.2).val
        let bIndex ← selectedOut.1
        let a ← (selectPaired state true aIndex).val
        let b ← (selectPaired state false bIndex).val
        let candidate := (Model.Operations.insertPaired
          (Model.Operations.erasePaired state a).val b).val
        let newKind := (classifyState candidate).val
        if newKind = .invalid then none else
          let oldKind := (classifyState state).val
          let oldWeight ← (weightOfKind r o₁ o₂ q weights state oldKind).val
          let newWeight ← (weightOfKind r o₁ o₂ q weights candidate newKind).val
          let ratio := newWeight / oldWeight
          if ratio < 1 then some (selectedOut.2, ratio.den) else none





end CountingMatroid.Analysis.ObservationRoundDrawSites

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r28 · proved · all three stopped-draw replay branches, composing boundedUniform interval replay before each descriptor; no open proof remains in this file.
* r28 · open · retained the existing descriptor and positive-denominator
  proof under their original names; proved the hold-bit/site-0 locality
  branch. The remaining sites require composition of one or two
  boundedUniform_interval_replay results with deterministic option branches.
-/

end


