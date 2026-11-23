-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CrSlot20261123
-- name    : LinearSetReconciliation327_Main_CrSlot20261123
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T12:12:54.796022+00:00
-- url     : https://prove2.me/theorems/b07329f0-b3f2-4f73-b79a-f321f46587c3
-- title:
--   The cr slot from a decoder exit: crMergeInD_of_upk applied
-- statement:
--   This bundle closes the interface half of Theorem 6.5's `cr` field. It packages the decoder's contract as `DecExitF` (the published exit facts `OutputsSupport` and `r0 = bb`, the output length and set, and the memory frame that keeps the estimate buffer alive) and names the frame lemma `DecMemFrame`: the decoder writes nothing at or above `B`. It then proves `crDecOut_of_exitF` (`DecExitF` plus the entry estimate frame gives `CrDecOut`), `hdecIn_of_exitF` (the only state-dependent hypothesis of the published `stageRun_crPipeline`), and `hdecIn_of_hdecW_frame` (the same from the **shape of the published `hdecW`** plus `DecMemFrame`), and finally `stageRun_crSlot`: the four-block `cr` stage `decStmt ; upkSetup ; upkStmt ; mrgStmtFull` runs from the corrected pre `CrStageInWzE` to `OutListIs s' (x hat triangle e hat)`. Its merge step is literally `crMergeInD_of_upk`, so the estimate buffer becomes the merge's A-side list.
-- source:
--   arXiv:2611.11409 (Linear Set Reconciliation with O(d) Additive Redundancy), Theorem 6.5 / Proposition 2.3

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CrStageInWzE20261123

/-!
# The `cr` slot from a decoder exit — `crMergeInD_of_upk` applied

This bundle closes the *interface* half of Theorem 6.5's item 1: with the corrected pre
`CRS.CrStageInWzE` (finite-zero pin **plus** the estimate-payload frame), the published composition
`CRS.stageRun_crPipeline` — decoder · `upkSetup` · the 31-instruction unpack · the merge — applies,
and its merge step is literally `CRS.crMergeInD_of_upk`: the unpack's repacked estimate becomes the
merge's `A`-side list.

The decoder's contract is packaged as one predicate, `DecExitF`: the decoder's published exit facts
(`OutputsSupport`, `r0 = bb`) **together with the memory frame** that keeps the estimate buffer
alive.  `DecMemFrame` names the frame lemma itself: *the decoder writes nothing at or above `B`*.

Everything here is stated with the output base `bb` and the frame bound `B` as parameters, so that
the file imports only `CrStageInWzE` (hence `CrField`) and stays importable next to the `z`-address
bundles; the `bb = decOutBase N t`, `B = decOutBase N t + N` instantiation is in
`Def_…_DecOutBase20261123`.

Contents:

* `DecExitF`, `DecMemFrame`;
* `outList_toFinset_eq`, `decExitF_of_outputs`, `regs_one_eq_card`;
* `crDecOut_of_exitF` — `DecExitF` plus the entry frame gives `CrDecOut`;
* `hdecIn_of_exitF` — the `hdec` slot of `stageRun_crPipeline`, from `DecExitF`;
* `hdecIn_of_hdecW_frame` — the same from the **shape of the published `CRS.hdecW`** plus
  `DecMemFrame`;
* `stageRun_crSlot` — **the `cr` field**: the four-block stage from `CrStageInWzE` to
  `OutListIs s' (symmDiff xhat S)`, i.e. `crMergeInD_of_upk` applied.

Axiom-clean: only `Mathlib` and published `Definitions.Def_*` bundles are imported.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 40000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace CRS

/-! ## 1. The decoder's exit contract and the frame lemma it needs -/

/-- **What the `cr` block reads off the decoder's exit.**  The published Proposition 2.3 exit facts
(`OutputsSupport`, `r0 = bb`), the output length and set that `CrMergeInD` needs, and — the one new
ingredient — **the memory frame**: every address `≥ B` is untouched. -/
def DecExitF (E : RAMEnv) {N : ℕ} (x : Fin N → ZMod 2) (bb bl : ℕ) (S : Finset ℕ) (B : ℕ)
    (s s' : RAMState) : Prop :=
  OutputsSupport s' x ∧ s'.regs 0 = bb ∧ s'.regs 1 = bl ∧
    (outList s').toFinset = S ∧ ∀ a : ℕ, B ≤ a → s'.mem a = s.mem a

/-- **The decoder memory-frame lemma** — *the decoder writes nothing at or above `B`*.  This is the
one statement no published bundle has; at 2.3's decoder the sharp choice is
`B = decOutBase N t + N` (the output window is `[decOutBase, decOutBase + |S|)` with `|S| ≤ N`). -/
def DecMemFrame (E : RAMEnv) (B : ℕ) (S : Stmt) (T : ℝ) : Prop :=
  ∀ s s' : RAMState, HaltsWithin (programOfStatement S) E T s s' → ∀ a : ℕ, B ≤ a → s'.mem a = s.mem a

/-- The frame is monotone in the bound. -/
theorem decMemFrame_mono {E : RAMEnv} {B B' : ℕ} {S : Stmt} {T : ℝ}
    (h : DecMemFrame E B S T) (hle : B ≤ B') : DecMemFrame E B' S T :=
  fun s s' hrun a ha => h s s' hrun a (le_trans hle ha)

/-! ## 2. From the published exit facts to `DecExitF` -/

/-- The output list of a state whose `OutputsSupport` is `x` has toFinset equal to the support image. -/
theorem outList_toFinset_eq {N : ℕ} {x : Fin N → ZMod 2} {S : Finset ℕ} {s' : RAMState}
    (hout : OutputsSupport s' x)
    (hS : S = (univ.filter fun i : Fin N => x i = 1).image Fin.val) :
    (outList s').toFinset = S := by
  rw [hS]
  ext v
  rw [List.mem_toFinset, hout.2 v]
  constructor
  · rintro ⟨i, rfl, hi⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨i, rfl, (Finset.mem_filter.mp hi).2⟩

/-- The card form of the exit length: `r1 = S.card`. -/
theorem regs_one_eq_card {N : ℕ} {x : Fin N → ZMod 2} {S : Finset ℕ} {s' : RAMState}
    (hout : OutputsSupport s' x) (hset : (outList s').toFinset = S) :
    s'.regs 1 = S.card := by
  have hlen : (outList s').length = s'.regs 1 := by simp [outList]
  have hcard : (outList s').toFinset.card = (outList s').length :=
    List.toFinset_card_of_nodup hout.1
  rw [hset] at hcard
  omega

/-- **`OutputsSupport` plus the frame is `DecExitF`.** -/
theorem decExitF_of_outputs {E : RAMEnv} {N : ℕ} {x : Fin N → ZMod 2} {bb bl : ℕ}
    {S : Finset ℕ} {B : ℕ} {s s' : RAMState}
    (hout : OutputsSupport s' x)
    (hS : S = (univ.filter fun i : Fin N => x i = 1).image Fin.val)
    (h0 : s'.regs 0 = bb)
    (hframe : ∀ a : ℕ, B ≤ a → s'.mem a = s.mem a)
    (hbl : s'.regs 1 = bl) :
    DecExitF E x bb bl S B s s' :=
  ⟨hout, h0, hbl, outList_toFinset_eq hout hS, hframe⟩

/-! ## 3. `DecExitF` plus the entry frame is `CrDecOut` -/

/-- **`CrDecOut` from `DecExitF`.** -/
theorem crDecOut_of_exitF {E : RAMEnv} {N : ℕ} {x : Fin N → ZMod 2} {xbase m bb bl B : ℕ}
    {y : Fin (E.W * m) → ZMod 2} {S : Finset ℕ} {s s' : RAMState}
    (hexit : DecExitF E x bb bl S B s s')
    (hS : S = (univ.filter fun i : Fin N => x i = 1).image Fin.val)
    (hpad : C8R.HoldsVecPad E.W m xbase s y) (hxb : B ≤ xbase)
    (hWN : N ≤ 2 ^ E.W) (hbl : bl < 2 ^ E.W) (hbbbl : bb + bl ≤ 2 ^ E.W) :
    CrDecOut E xbase m bb bl y S s' := by
  obtain ⟨hout, h0, h1, hset, hframe⟩ := hexit
  have hval : ∀ p, p < bl → s'.mem (bb + p) < 2 ^ E.W := by
    intro p hp
    have h := outList_lt_of_outputsSupport hout hWN p (by rw [h1]; exact hp)
    rwa [h0] at h
  rw [hS]
  exact crDecOut_of_exit hout h0 h1 hframe hpad hxb hval hbl hbbbl

/-! ## 4. The `hdec` slot of `stageRun_crPipeline` -/

/-- **The `hdec` slot from `DecExitF`.**  `stageRun_crPipeline`'s only state-dependent hypothesis is
`hdec`; this is it, produced from the decoder's exit contract. -/
theorem hdecIn_of_exitF {Sinit Srow Sdec Sassem Sres : Stmt} {E : RAMEnv} {N : ℕ}
    {x : Fin N → ZMod 2} {xbase m bb bl B : ℕ} {y : Fin (E.W * m) → ZMod 2} {S : Finset ℕ}
    {Tdec : ℝ} {Pre : RAMState → Prop}
    (hexit : ∀ s : RAMState, s.pc = 0 → Pre (withPc (dCrBase Sinit Srow Sdec Sassem Sres) s) →
      ∃ s', HaltsWithin (programOfStatement decStmt) E Tdec s s' ∧ DecExitF E x bb bl S B s s')
    (hpre : ∀ s : RAMState, Pre s → C8R.HoldsVecPad E.W m xbase s y)
    (hS : S = (univ.filter fun i : Fin N => x i = 1).image Fin.val)
    (hxb : B ≤ xbase)
    (hWN : N ≤ 2 ^ E.W) (hbl : bl < 2 ^ E.W) (hbbbl : bb + bl ≤ 2 ^ E.W) :
    ∀ s : RAMState, s.pc = 0 → Pre (withPc (dCrBase Sinit Srow Sdec Sassem Sres) s) →
      ∃ s', HaltsWithin (programOfStatement decStmt) E Tdec s s' ∧
        CrDecOut E xbase m bb bl y S
          (withPc (dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len) s') := by
  intro s hpc hPre
  obtain ⟨s', hrun, hexit'⟩ := hexit s hpc hPre
  refine ⟨s', hrun, ?_⟩
  have hpad : C8R.HoldsVecPad E.W m xbase s y :=
    hpre (withPc (dCrBase Sinit Srow Sdec Sassem Sres) s) hPre
  exact crDecOut_of_exitF hexit' hS hpad hxb hWN hbl hbbbl

/-! ## 5. The same from the shape of the published `hdecW` plus `DecMemFrame` -/

/-- **The `hdec` slot from `hdecW`'s shape plus the frame lemma.**  `CRS.hdecW` (published, `Proved`)
concludes `HaltsWithin ∧ OutputsSupport ∧ r0 = decOutBase`; adding `DecMemFrame` is exactly
`DecExitF`, so the slot closes. -/
theorem hdecIn_of_hdecW_frame {Sinit Srow Sdec Sassem Sres : Stmt} {E : RAMEnv} {N : ℕ}
    {x : Fin N → ZMod 2} {xbase m bb bl B : ℕ} {y : Fin (E.W * m) → ZMod 2} {S : Finset ℕ}
    {Tdec : ℝ} {Pre : RAMState → Prop}
    (hdecW : ∀ s : RAMState, s.pc = 0 → Pre (withPc (dCrBase Sinit Srow Sdec Sassem Sres) s) →
      ∃ s', HaltsWithin (programOfStatement decStmt) E Tdec s s' ∧
        OutputsSupport s' x ∧ s'.regs 0 = bb)
    (hframe : DecMemFrame E B decStmt Tdec)
    (hpre : ∀ s : RAMState, Pre s → C8R.HoldsVecPad E.W m xbase s y)
    (hS : S = (univ.filter fun i : Fin N => x i = 1).image Fin.val)
    (hblcard : bl = S.card)
    (hxb : B ≤ xbase)
    (hWN : N ≤ 2 ^ E.W) (hbl : bl < 2 ^ E.W) (hbbbl : bb + bl ≤ 2 ^ E.W) :
    ∀ s : RAMState, s.pc = 0 → Pre (withPc (dCrBase Sinit Srow Sdec Sassem Sres) s) →
      ∃ s', HaltsWithin (programOfStatement decStmt) E Tdec s s' ∧
        CrDecOut E xbase m bb bl y S
          (withPc (dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len) s') := by
  refine hdecIn_of_exitF (Pre := Pre) ?_ hpre hS hxb hWN hbl hbbbl
  intro s hpc hPre
  obtain ⟨s', hrun, hout, h0⟩ := hdecW s hpc hPre
  have hset : (outList s').toFinset = S := outList_toFinset_eq hout hS
  have hlen : s'.regs 1 = bl := by
    rw [regs_one_eq_card hout hset, ← hblcard]
  exact ⟨s', hrun, decExitF_of_outputs hout hS h0 (hframe s s' hrun) hlen⟩

/-! ## 6. The `cr` field -/

/-- **The `cr` field of Theorem 6.5, with the estimate-payload frame in its pre.**

`CRS.stageRun_crPipeline` composed with the decoder exit contract: from `CrStageInWzE` (the decoder's
finite-zero pin, the merge's block data, and the estimate buffer at `xbase`) the four-block
`cr` stage — `decStmt · upkSetup · upkStmt · mrgStmtFull` — runs to the merge's output
`OutListIs s' (x̂ △ ê)`.  Its merge step is `crMergeInD_of_upk`, so the estimate buffer *is* the
merge's `A`-side list. -/
theorem stageRun_crSlot {Sinit Srow Sdec Sassem Sres : Stmt} {E : RAMEnv}
    {M Z xbase m ab bb bl ob al : ℕ} {y : Fin M → ZMod 2} {yest : Fin (E.W * m) → ZMod 2}
    {Lx : List ℕ} {S xhat : Finset ℕ} {Tdec : ℝ} {N : ℕ} {x : Fin N → ZMod 2} {B : ℕ}
    (hexit : ∀ s : RAMState, s.pc = 0 →
      CrStageInWzE E M Z y xbase m yest ab al bb bl ob Lx
        (withPc (dCrBase Sinit Srow Sdec Sassem Sres) s) →
      ∃ s', HaltsWithin (programOfStatement decStmt) E Tdec s s' ∧ DecExitF E x bb bl S B s s')
    (hS : S = (univ.filter fun i : Fin N => x i = 1).image Fin.val)
    (hxhat : (packedSupp E.W m yest).toFinset = xhat)
    (hxdisj : xbase + m ≤ ab) (hEhab : ab + E.W * m + 1 < 2 ^ E.W)
    (hob : ob < 2 ^ E.W)
    (hdisj : bb + bl ≤ ab ∨ ab + (m * E.W + 1) ≤ bb)
    (hobig : ob + ((packedSupp E.W m yest).length + bl) + 1 < 2 ^ E.W)
    (hAob : ab + (packedSupp E.W m yest).length ≤ ob) (hBob : bb + bl ≤ ob)
    (hW : 1 < 2 ^ E.W) (hWm : E.W * m < 2 ^ E.W)
    (hxb : B ≤ xbase)
    (hWN : N ≤ 2 ^ E.W) (hbl : bl < 2 ^ E.W) (hbbbl : bb + bl ≤ 2 ^ E.W) :
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres (CrStage4 decStmt E.W xbase m ab ob)) E
      (dCrBase Sinit Srow Sdec Sassem Sres)
      (dEnd Sinit Srow Sdec Sassem Sres (CrStage4 decStmt E.W xbase m ab ob))
      (Tdec + 5 + ((16 * (E.W * m) + 17 : ℕ) : ℝ) +
        RMR.mrgCost (packedSupp E.W m yest).length bl)
      (CrStageInWzE E M Z y xbase m yest ab al bb bl ob Lx)
      (fun s' => OutListIs s' (symmDiff xhat S)) :=
  stageRun_crPipeline (Sinit := Sinit) (Srow := Srow) (Sdec := Sdec) (Sassem := Sassem)
    (Sres := Sres) (E := E) (xbase := xbase) (m := m) (ab := ab) (bb := bb)
    (bl := bl) (ob := ob) (y := yest) (S := S) (xhat := xhat) (Tdec := Tdec)
    (Pre := CrStageInWzE E M Z y xbase m yest ab al bb bl ob Lx)
    (hdecIn_of_exitF (Pre := CrStageInWzE E M Z y xbase m yest ab al bb bl ob Lx)
      hexit (fun s h => crStageInWzE_pad h) hS hxb hWN hbl hbbbl)
    hxhat hW hWm hxdisj hEhab (by omega) hbl hob hdisj hobig hAob hBob

end CRS
end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.CRS.decMemFrame_mono
#print axioms LinearSetReconciliation327.Main.CRS.outList_toFinset_eq
#print axioms LinearSetReconciliation327.Main.CRS.regs_one_eq_card
#print axioms LinearSetReconciliation327.Main.CRS.decExitF_of_outputs
#print axioms LinearSetReconciliation327.Main.CRS.crDecOut_of_exitF
#print axioms LinearSetReconciliation327.Main.CRS.hdecIn_of_exitF
#print axioms LinearSetReconciliation327.Main.CRS.hdecIn_of_hdecW_frame
#print axioms LinearSetReconciliation327.Main.CRS.stageRun_crSlot


