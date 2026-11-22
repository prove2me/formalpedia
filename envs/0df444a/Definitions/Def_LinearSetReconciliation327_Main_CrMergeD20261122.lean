-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CrMergeD20261122
-- name    : LinearSetReconciliation327_Main_CrMergeD20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T07:10:08.944309+00:00
-- url     : https://prove2.me/theorems/4e328c1e-0d47-4a91-a86b-a198f8ed0e5c
-- title:
--   The corrected merge entry predicate: the decoder window must miss the unpack's writes
-- statement:
--   The merge of Theorem 6.5's `cr` stage reads the decoded residual out of the decoder's output window $[b_b, b_b+b_l)$.  In the pipeline that window is produced *before* the unpack block runs, and the unpack writes the estimate's coordinate list into $[ab, ab + mW + 1)$ \u2014 the extra $+1$ because its store is branchless and one stale cell above the list is written on every clear bit.  If the two ranges meet, the unpack silently overwrites the residual list, so the merge's `outList` conjunct describes the wrong data.  This bundle states the corrected entry predicate `CrMergeInD` = `CrMergeIn` plus the disjunct $b_b+b_l \le ab \lor ab + (mW+1) \le b_b$, proves that it implies the published `CrMergeIn`, that the merge's `StageRun` still goes through from it, that it is inhabited both at the non-empty witness ($A=[5]$ at $[10,11)$, $B=[7]$ at $[20,21)$, $m=1$: the write range $[10,19)$ misses $[20,21)$) and at the degenerate $A=B=\varnothing$, and finally that the conjunct is *necessary*: one iteration of the scan really does replace the cell holding the residual element `7` by `0` when the destination base coincides with the window's start.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's `cr` stage; the predicate `CrMergeIn` is `Definitions.Def_LinearSetReconciliation327_Main_CrStage20261122`'s, and the unpack program whose write range it must miss is `Definitions.Def_LinearSetReconciliation327_Main_CrStageDec20261122`'s.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CrStage20261122
import Definitions.Def_LinearSetReconciliation327_Main_CrStageDec20261122
import Definitions.Def_LinearSetReconciliation327_Main_MergeStep20261121
import Definitions.Def_LinearSetReconciliation327_Main_CR23Dec

/-!
# The merge's entry predicate, corrected: the decoder window must miss the unpack's write range

`CRS.CrMergeIn` (`Def_…_CrStage20261122`) pins the residual list to the decoder's output window
`[bb, bb + bl)`: `outList t = mList t.mem bb bl`.  In the real pipeline that state is produced by the
*unpack* block of `Def_…_CrStageDec20261122`, which writes the estimate `x̂` as a coordinate list at
`[ab, ab + m·W + 1)`.  If the two ranges meet, the scan's own stores land on top of the residual list
and `CrMergeIn`'s `outList` conjunct silently describes the wrong data.

This file states the corrected predicate `CrMergeInD` = `CrMergeIn` + the missing side condition

```
bb + bl ≤ ab  ∨  ab + (m·W + 1) ≤ bb
```

proves it inhabited (both at the non-empty witness `A = [5]`, `B = [7]` and at the degenerate
`A = B = []`), shows the merge's `StageRun` still goes through, and records *why* the conjunct is
needed: without it one iteration of the scan really does overwrite `mem bb`.

Everything is new text; the published `CrMergeIn` is untouched.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace CRS

/-! ## 1. The corrected predicate -/

/-- **The corrected merge entry predicate.**  `CrMergeIn` plus the *disjointness* of the decoder's
output window `[bb, bb+bl)` and the unpack's write range `[ab, ab + m·W + 1)`.

The `+1` is not slack: the scan's store is unconditional and the counter only advances by the scanned
bit, so after the last clear bit one stale cell at `ab + (upkList …).length` is written as well. -/
def CrMergeInD (E : RAMEnv) (ab al bb bl ob m : ℕ) (Lx : List ℕ) (S : Finset ℕ)
    (t : RAMState) : Prop :=
  CrMergeIn E ab al bb bl ob Lx S t ∧
    (bb + bl ≤ ab ∨ ab + (m * E.W + 1) ≤ bb)

/-- The corrected predicate implies the published one. -/
theorem crMergeInD_toCrMergeIn {E : RAMEnv} {ab al bb bl ob m : ℕ} {Lx : List ℕ}
    {S : Finset ℕ} {t : RAMState} (h : CrMergeInD E ab al bb bl ob m Lx S t) :
    CrMergeIn E ab al bb bl ob Lx S t :=
  h.1

/-- The new conjunct, read on its own. -/
theorem crMergeInD_disj {E : RAMEnv} {ab al bb bl ob m : ℕ} {Lx : List ℕ} {S : Finset ℕ}
    {t : RAMState} (h : CrMergeInD E ab al bb bl ob m Lx S t) :
    bb + bl ≤ ab ∨ ab + (m * E.W + 1) ≤ bb :=
  h.2

/-- **The merge as a `StageRun` from the corrected entry predicate.**  The extra conjunct is not read
by the merge itself, so this is `stageRun_mergeAt` with the hypothesis weakened. -/
theorem stageRun_mergeAtD {G : Program} {E : RAMEnv} {base ab al bb bl ob m : ℕ}
    {Lx : List ℕ} {S xhat : Finset ℕ}
    (hAt : At G base (RMR.mrgStmtFull.compile base)) (hW : 1 < 2 ^ E.W)
    (hLx : Lx.toFinset = xhat) :
    StageRun G E base (base + RMR.mrgStmtFull.len) (RMR.mrgCost al bl)
      (CrMergeInD E ab al bb bl ob m Lx S)
      (fun s' => OutListIs s' (symmDiff xhat S)) := by
  intro t htpc htI
  exact stageRun_mergeAt (G := G) (E := E) (base := base) (ab := ab) (al := al) (bb := bb)
    (bl := bl) (ob := ob) (Lx := Lx) (S := S) (xhat := xhat) hAt hW hLx t htpc htI.1

/-! ## 2. Why the conjunct is not redundant -/

/-- `upkList` at `j = 0` is empty, so the first iteration writes cell `ab + 0 = ab`. -/
theorem upkMem_one_writes_start (W xbase : ℕ) (m0 : ℕ → ℕ) (ab : ℕ) :
    upkMem W xbase m0 ab 1 (ab + 0) = 0 := by
  show upkMem W xbase m0 ab (0 + 1) (ab + 0) = 0
  rw [upkMem_succ, upkMem_zero, upkList_zero, List.length_nil, Nat.add_zero, Function.update_self]

/-- **The scan really does destroy a residual list that starts inside its write range.**  With
`W = 8`, the destination base `ab = 20` and a memory whose cell `20` holds `7` — exactly the single
element of `B = [7]` at `[20, 21)` — one iteration replaces `mem 20` by `0`.  Hence the disjointness
conjunct of `CrMergeInD` is a genuine hypothesis, not a bookkeeping convenience. -/
theorem upkMem_corrupts_residual :
    ∃ m0 : ℕ → ℕ, upkMem 8 0 m0 20 1 20 ≠ m0 20 :=
  ⟨fun _ => 7, by rw [upkMem_one_writes_start]; norm_num⟩

/-- The same, stated as a hypothesis under which the published `CrMergeIn` is *not* preserved by the
unpack: a state whose `B` window is `[20, 21)` with `mem 20 = 7` has `mem 20 = 0` after one step. -/
theorem upkMem_corrupts_mem (m0 : ℕ → ℕ) (_h : m0 20 = 7) :
    upkMem 8 0 m0 20 1 20 = 0 := by
  rw [upkMem_one_writes_start]

/-! ## 3. Non-vacuity -/

/-- **`CrMergeInD` is inhabited at the non-empty witness.**  `A = [5]` at `[10, 11)`,
`B = [7]` at `[20, 21)`, output block at `40`, `W = 8`, `m = 1`: the write range is `[10, 19)` and the
residual window is `[20, 21)`, so they miss.  (This is `crMergeIn_witness` plus the new conjunct,
`10 + (1·8 + 1) = 19 ≤ 20`.) -/
theorem crMergeInD_witness : CrMergeInD RMR.mrgEnv8 10 1 20 1 40 1 [5] {7} crW1 :=
  ⟨crMergeIn_witness, by decide⟩

/-- **`CrMergeInD` is inhabited at the degenerate value.**  `A = B = []`: both blocks are empty, so
the ranges are disjoint by the left disjunct `0 + 0 ≤ 0`. -/
theorem crMergeInD_degenerate : CrMergeInD RMR.mrgEnv8 0 0 0 0 64 0 [] ∅ crW0 :=
  ⟨crMergeIn_degenerate, by decide⟩

/-- The merge half still runs from the corrected predicate at the witness, inside the composite CR
block: from `crW1` it reaches `86 = (ScrStage (.code [])).len` and outputs `{5} △ {7} = {5, 7}`. -/
theorem stageRun_mergeAtD_witness :
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ RMR.mrgCost 1 1 ∧
      (step RMR.mrgProg RMR.mrgEnv8)^[k] crW1 = s' ∧
      s'.pc = RMR.mrgStmtFull.len ∧
      OutListIs s' ({5, 7} : Finset ℕ) := by
  have h := stageRun_mergeAtD (G := RMR.mrgProg) (E := RMR.mrgEnv8) (base := 0)
    (ab := 10) (al := 1) (bb := 20) (bl := 1) (ob := 40) (m := 1)
    (Lx := [5]) (S := {7}) (xhat := {5}) RMR.mrgProg_at (by decide) (by decide)
    crW1 rfl crMergeInD_witness
  obtain ⟨k, s', hk, hstep, hpc, hpost⟩ := h
  refine ⟨k, s', hk, hstep, hpc, ?_⟩
  rwa [show symmDiff ({5} : Finset ℕ) {7} = {5, 7} from by decide] at hpost

end CRS
end LinearSetReconciliation327.Main


