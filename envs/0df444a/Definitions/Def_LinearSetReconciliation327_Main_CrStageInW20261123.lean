-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CrStageInW20261123
-- name    : LinearSetReconciliation327_Main_CrStageInW20261123
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T10:52:20.493146+00:00
-- url     : https://prove2.me/theorems/0a23ccdd-c805-4a8b-839d-42978b9413e9
-- title:
--   Theorem 6.5: CrStageIn with a window pin instead of a whole-memory pin
-- statement:
--   The `cr` stage's entry predicate of Theorem 6.5, weakened from the whole-memory pin `t.mem = decoderStart.mem` to a finite window pin: the state presents the decoder's payload on `[0, wordsOf E.W M)` (`DecInputOn E.W M 0 y []`, the published positional repair), its registers are the decoder's start registers, and the merge's state-free block data `CrMergeData` holds.  Proved: the old predicate implies the new one; the new one is strictly weaker (`y` and memory past the window are free); it has a frame property (agree on the window and the pin survives), which the old infinite pin lacks; it is non-degenerately inhabited for every `k` by a state whose word `wordsOf E.W M + k` is `1`; the old predicate forces the whole zero tail and is a subsingleton per program counter; `CrMergeIn` depends only on the registers and on `[ab, ab+al) union [bb, bb+bl)`; and the published `stageRun_crMerge_top` consumes the weakened precondition syntactically unchanged.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5 / Proposition 2.3; the project's published `CrField20261122`, `CrPipeline20261122`, `CrStage20261122` and `DecodeClose20261121` bundles.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CrField20261122

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 40000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace CRS

/-! # The weakened `CrStageIn`: a window pin instead of a whole-memory pin

The published `CRS.CrStageIn` conjoins `t.mem = (decoderStart E.W y []).mem`, i.e. it pins the
**whole infinite memory** (the packed sketch on `[0, wordsOf E.W M)` and zeros at every address
`≥ wordsOf E.W M`).  The consequence, established in the previous round, is that any `StageRun`
whose post is `CrStageIn` forces the same infinite pin in its pre — no finite program can restore
infinitely many zeros after a write — which is why the corrected `res` pre pushed a memory frame
`MemInv : (ℕ → ℕ) → Prop` through `init → row → col → as`.

This bundle replaces that conjunct by the **window pin** `C8R.DecInputOn E.W M 0 y []`, which is
exactly the published, proved predicate for "the state presents the decoder's payload on the finite
window `[0, wordsOf E.W M)`" (and `r0 = 0`, `r1 = wordsOf E.W M`, `r2 = 0`).  The merge's
state-free block data `CrMergeData` is kept verbatim.

What is proved here:

* the whole API of the weakened predicate, including the **frame property** the whole-memory pin
  does not have (`crStageInW_of_agree`: agree on the window, keep the pin);
* that the old predicate **implies** the weakened one (`crStageInW_of_crStageIn`), so the change is
  a genuine weakening;
* that it is **non-degenerately inhabited**: for every `k`, a state satisfying it whose word
  `wordsOf E.W M + k` is `1` (`crStageInW_inhabited_nondegen`), plus a concrete `y ≠ 0` witness;
* that it is **strictly** weaker: such a state never satisfies the old `CrStageIn`
  (`crStageInW_not_of_garbage`), whereas the old predicate is a **subsingleton per pc**
  (`crStageIn_subsingleton`) — the precise sense in which it pinned the whole memory;
* the **`cr` composition lemma**: the published `stageRun_crMerge_top` consumes the weakened pre
  syntactically unchanged (`stageRun_crMerge_top_window`), and `CrMergeIn` reads memory only on
  `[ab, ab+al) ∪ [bb, bb+bl)` (`crMergeIn_frame`), the two windows the block itself produces.
-/

/-! ## 1. The weakened predicate -/

/-- **The `cr` block's entry predicate with a window pin instead of a whole-memory pin.**

`t.regs = decoderStart`'s registers is finite and unchanged.  The memory conjunct is
`C8R.DecInputOn E.W M 0 y [] t`, i.e. `t.mem j = packMem E.W y j` for every
`j < wordsOf E.W M` — the exact finite window Proposition 2.3's decoder reads its payload from.
Memory at `≥ wordsOf E.W M` is **not** constrained.  The merge's state-free block data
`CrMergeData` is unchanged. -/
def CrStageInW (E : RAMEnv) (M : ℕ) (y : Fin M → ZMod 2)
    (ab al bb bl ob : ℕ) (Lx : List ℕ) (t : RAMState) : Prop :=
  t.regs = (decoderStart E.W y []).regs ∧
    C8R.DecInputOn E.W M 0 y [] t ∧ CrMergeData E ab al bb bl ob Lx

/-! ## 2. The API -/

/-- The register conjunct, verbatim. -/
theorem crStageInW_regs {E : RAMEnv} {M : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {t : RAMState} (h : CrStageInW E M y ab al bb bl ob Lx t) :
    t.regs = (decoderStart E.W y []).regs := h.1

/-- The **window pin**: the state presents the decoder's payload on `[0, wordsOf E.W M)`. -/
theorem crStageInW_win {E : RAMEnv} {M : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {t : RAMState} (h : CrStageInW E M y ab al bb bl ob Lx t) :
    C8R.DecInputOn E.W M 0 y [] t := h.2.1

/-- The state-free merge data, verbatim. -/
theorem crStageInW_data {E : RAMEnv} {M : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {t : RAMState} (h : CrStageInW E M y ab al bb bl ob Lx t) :
    CrMergeData E ab al bb bl ob Lx := h.2.2

/-- The window, written without `DecInputOn`'s bookkeeping: the packed sketch on
`[0, wordsOf E.W M)`. -/
theorem crStageInW_holdsVec {E : RAMEnv} {M : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {t : RAMState} (h : CrStageInW E M y ab al bb bl ob Lx t) :
    C8R.HoldsVec E.W M 0 t y :=
  C8R.decInputOn_holdsVec h.2.1

/-- **The weakened predicate, characterised**: registers as the decoder's start state, the packed
sketch on the finite window `[0, wordsOf E.W M)`, and the merge's block data.  No statement about
memory at `≥ wordsOf E.W M` appears. -/
theorem crStageInW_iff {E : RAMEnv} {M : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {t : RAMState} :
    CrStageInW E M y ab al bb bl ob Lx t ↔
      t.regs = (decoderStart E.W y []).regs ∧ C8R.HoldsVec E.W M 0 t y ∧
        CrMergeData E ab al bb bl ob Lx := by
  constructor
  · rintro ⟨hr, hw, hd⟩
    exact ⟨hr, C8R.decInputOn_holdsVec hw, hd⟩
  · rintro ⟨hr, hv, hd⟩
    refine ⟨hr, ⟨?_, ?_, ?_, ?_⟩, hd⟩
    · intro j hj
      rw [List.length_nil, Nat.add_zero] at hj
      rw [show hintMem E.W y [] j = packMem E.W y j from by
        unfold hintMem
        rw [if_pos hj]]
      simpa using hv j hj
    · rw [hr]; simp [decoderStart, initState]
    · rw [hr]; simp [decoderStart, initState]
    · rw [hr]; simp [decoderStart, initState]

/-- Constructor from the three pieces. -/
theorem crStageInW_of_eq {E : RAMEnv} {M : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {t : RAMState}
    (hregs : t.regs = (decoderStart E.W y []).regs)
    (hwin : C8R.DecInputOn E.W M 0 y [] t)
    (hdata : CrMergeData E ab al bb bl ob Lx) : CrStageInW E M y ab al bb bl ob Lx t :=
  ⟨hregs, hwin, hdata⟩

/-! ## 3. Inhabitants -/

/-- **Inhabitant at `decoderStart`.**  The decoder's own start state satisfies the weakened
predicate, exactly as it satisfied the old one. -/
theorem crStageInW_decoderStart (E : RAMEnv) (M : ℕ) (y : Fin M → ZMod 2)
    (ab al bb bl ob : ℕ) (Lx : List ℕ) (hdata : CrMergeData E ab al bb bl ob Lx) :
    CrStageInW E M y ab al bb bl ob Lx (decoderStart E.W y []) :=
  ⟨rfl, C8R.decInputOn_decoderStart E.W M y [], hdata⟩

/-- **The window pin is not a whole-memory pin.**  For every `k`, some state satisfies the weakened
predicate and has `1` at the word `wordsOf E.W M + k`, which is `0` in `decoderStart`'s memory.
The old predicate forbids this by construction. -/
theorem crStageInW_inhabited_nondegen {E : RAMEnv} {M : ℕ} {y : Fin M → ZMod 2}
    {ab al bb bl ob : ℕ} {Lx : List ℕ} (hdata : CrMergeData E ab al bb bl ob Lx) (k : ℕ) :
    ∃ t : RAMState, CrStageInW E M y ab al bb bl ob Lx t ∧
      t.mem (wordsOf E.W M + k) = 1 := by
  classical
  refine ⟨⟨0, (decoderStart E.W y []).regs,
      fun a => if a < wordsOf E.W M then packMem E.W y a else 1⟩, ?_, ?_⟩
  · refine ⟨rfl, ⟨fun j hj => ?_, ?_, ?_, ?_⟩, hdata⟩
    · rw [List.length_nil, Nat.add_zero] at hj
      rw [Nat.zero_add]
      rw [show hintMem E.W y [] j = packMem E.W y j from by
        unfold hintMem
        rw [if_pos hj]]
      change (if j < wordsOf E.W M then packMem E.W y j else 1) = packMem E.W y j
      rw [if_pos hj]
    · simp [decoderStart, initState]
    · simp [decoderStart, initState]
    · simp [decoderStart, initState]
  · change (if wordsOf E.W M + k < wordsOf E.W M then
      packMem E.W y (wordsOf E.W M + k) else 1) = 1
    rw [if_neg (by omega)]

/-! ## 4. The old pin implies the new one, and the new one is strictly weaker -/

/-- **The change is a weakening: the old whole-memory pin implies the window pin.** -/
theorem crStageInW_of_crStageIn {E : RAMEnv} {M : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {t : RAMState} (h : CrStageIn E M y ab al bb bl ob Lx t) :
    CrStageInW E M y ab al bb bl ob Lx t := by
  obtain ⟨hr, hm, hd⟩ := h
  have hAt : C8R.DecInputAt E.W M y [] t := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j
      rw [hm]
      rfl
    · rw [hr]; simp [decoderStart, initState]
    · rw [hr]; simp [decoderStart, initState]
    · rw [hr]; simp [decoderStart, initState]
  exact ⟨hr, C8R.decInputOn_of_decInputAt hAt, hd⟩

/-- **The frame property the whole-memory pin does not have.**  Two states agreeing on the window
(and on the registers) both satisfy the weakened predicate.  This is what lets a finite program —
and in particular the residual stage — re-establish the pin. -/
theorem crStageInW_of_agree {E : RAMEnv} {M : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {s s' : RAMState} (h : CrStageInW E M y ab al bb bl ob Lx s)
    (hmem : ∀ j, j < wordsOf E.W M → s'.mem j = s.mem j)
    (hregs : s'.regs = s.regs) : CrStageInW E M y ab al bb bl ob Lx s' := by
  obtain ⟨hr, hw, hd⟩ := h
  refine ⟨by rw [hregs, hr], ?_, hd⟩
  refine C8R.decInputOn_of_agree hw ?_ ?_ ?_ ?_
  · intro j hj
    simpa using hmem j (by simpa using hj)
  · rw [hregs]
  · rw [hregs]
  · rw [hregs]

/-- **The old predicate pins the whole zero tail**: every word at `≥ wordsOf E.W M` is `0`. -/
theorem crStageIn_forces_zero {E : RAMEnv} {M : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {t : RAMState} (h : CrStageIn E M y ab al bb bl ob Lx t) :
    ∀ a, wordsOf E.W M ≤ a → t.mem a = 0 := by
  obtain ⟨-, hm, -⟩ := h
  intro a ha
  rw [hm]
  show hintMem E.W y [] a = 0
  unfold hintMem
  rw [if_neg (by omega)]
  rfl

/-- **The weakened predicate is strictly weaker.**  A state with `1` at `wordsOf E.W M + k` satisfies
it and never satisfies the old whole-memory `CrStageIn`. -/
theorem crStageInW_not_of_garbage {E : RAMEnv} {M : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {t : RAMState} (h : CrStageInW E M y ab al bb bl ob Lx t)
    (hg : t.mem (wordsOf E.W M + 1) = 1) : ¬ CrStageIn E M y ab al bb bl ob Lx t := by
  intro hold
  have h0 : t.mem (wordsOf E.W M + 1) = 0 :=
    crStageIn_forces_zero hold _ (by omega)
  rw [hg] at h0
  exact absurd h0 (by norm_num)

/-- The old whole-memory predicate is a **subsingleton per program counter**: two states satisfying
it at the same `pc` are equal.  (The window predicate is not: see
`crStageInW_inhabited_nondegen`.) -/
theorem crStageIn_subsingleton {E : RAMEnv} {M : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ}
    {Lx : List ℕ} {s t : RAMState} (hpc : s.pc = t.pc)
    (hs : CrStageIn E M y ab al bb bl ob Lx s) (ht : CrStageIn E M y ab al bb bl ob Lx t) :
    s = t := by
  obtain ⟨hrs, hms, -⟩ := hs
  obtain ⟨hrt, hmt, -⟩ := ht
  exact state_eq_of hpc (by rw [hrs, hrt]) (by rw [hms, hmt])

/-! ## 5. A concrete non-degenerate witness (`y ≠ 0`) -/

/-- The model environment: `W = 8`, no randomness. -/
abbrev E8 : RAMEnv := detEnv 8 (fun _ => 0)

/-- The all-ones `8`-bit payload: `y ≠ 0`. -/
def y8 : Fin 8 → ZMod 2 := fun _ => 1

theorem y8_ne_zero : y8 ≠ 0 := by
  intro h
  have := congrFun h ⟨0, by norm_num⟩
  simp [y8] at this

/-- The merge's block data at `(ab,al,bb,bl,ob) = (10,1,20,1,40)`, `Lx = [5]`. -/
theorem data8 : CrMergeData E8 10 1 20 1 40 [5] := by
  unfold CrMergeData
  decide

/-- **The concrete non-degenerate inhabitant.**  `y8 ≠ 0`, the merge data holds, the window pin is
satisfied, and memory at word `wordsOf 8 8 + 1 = 2` is `1` (it is `0` in `decoderStart`'s memory). -/
theorem crStageInW_nondegen_concrete :
    ∃ t : RAMState, CrStageInW E8 8 y8 10 1 20 1 40 [5] t ∧ t.mem (wordsOf 8 8 + 1) = 1 :=
  crStageInW_inhabited_nondegen data8 1

/-- The concrete state of `crStageInW_nondegen_concrete` does **not** satisfy the old predicate. -/
theorem crStageInW_concrete_not_old :
    ∃ t : RAMState, CrStageInW E8 8 y8 10 1 20 1 40 [5] t ∧
      ¬ CrStageIn E8 8 y8 10 1 20 1 40 [5] t := by
  obtain ⟨t, ht, hg⟩ := crStageInW_nondegen_concrete
  exact ⟨t, ht, crStageInW_not_of_garbage ht hg⟩

/-! ## 6. `CrMergeIn` reads only the merge's two windows -/

/-- `mList` only depends on the words `[b, b+len)`. -/
theorem mList_congr {m0 m1 : ℕ → ℕ} {b len : ℕ}
    (h : ∀ p, p < len → m1 (b + p) = m0 (b + p)) :
    RMR.mList m1 b len = RMR.mList m0 b len := by
  unfold RMR.mList
  exact List.map_congr_left (fun i hi => h i (List.mem_range.mp hi))

/-- `outList` only depends on the two output registers and the words `[regs 0, regs 0 + regs 1)`. -/
theorem outList_congr {s t : RAMState} (h0 : t.regs 0 = s.regs 0) (h1 : t.regs 1 = s.regs 1)
    (h : ∀ p, p < s.regs 1 → t.mem (s.regs 0 + p) = s.mem (s.regs 0 + p)) :
    outList t = outList s := by
  unfold outList
  rw [h1]
  exact List.map_congr_left (fun i hi => by
    rw [h0]
    exact h i (List.mem_range.mp hi))

/-- **`CrMergeIn` is a window predicate.**  It is determined by the registers and by memory on
`[ab, ab+al) ∪ [bb, bb+bl)` only; every other word is irrelevant.  So the residual and `CR` stages
never need an entry pin beyond those windows, which the block itself writes. -/
theorem crMergeIn_frame {E : RAMEnv} {ab al bb bl ob : ℕ} {Lx : List ℕ} {S : Finset ℕ}
    {s t : RAMState} (h : CrMergeIn E ab al bb bl ob Lx S s)
    (hregs : ∀ d, t.regs d = s.regs d)
    (hA : ∀ p, p < al → t.mem (ab + p) = s.mem (ab + p))
    (hB : ∀ p, p < bl → t.mem (bb + p) = s.mem (bb + p)) :
    CrMergeIn E ab al bb bl ob Lx S t := by
  obtain ⟨h10, h11, h12, h13, h14, h0, h1, hL, hnd, hset, hndL, hvA, hvB, hal, hbl, hab, hbb,
    hob, hdA, hdB⟩ := h
  have houts : outList s = RMR.mList s.mem bb bl := by
    simp only [outList, RMR.mList, h0, h1]
  have ht0 : t.regs 0 = bb := (hregs 0).trans h0
  have ht1 : t.regs 1 = bl := (hregs 1).trans h1
  have houtt : outList t = RMR.mList t.mem bb bl := by
    simp only [outList, RMR.mList, ht0, ht1]
  have hmL : RMR.mList t.mem ab al = RMR.mList s.mem ab al := mList_congr hA
  have hmB : RMR.mList t.mem bb bl = RMR.mList s.mem bb bl := mList_congr hB
  refine ⟨(hregs r10).trans h10, (hregs r11).trans h11, (hregs r12).trans h12,
    (hregs r13).trans h13, (hregs r14).trans h14, (hregs 0).trans h0, (hregs 1).trans h1,
    ?_, ?_, ?_, hndL, ?_, ?_, hal, hbl, hab, hbb, hob, hdA, hdB⟩
  · rw [hmL, hL]
  · rw [houtt, hmB, ← houts]; exact hnd
  · rw [houtt, hmB, ← houts]; exact hset
  · intro p hp
    rw [hA p hp]; exact hvA p hp
  · intro p hp
    rw [hB p hp]; exact hvB p hp

/-! ## 7. The `cr` field composes from the weakened pin -/

/-- **The `cr` field composes from the window pin.**  The published `stageRun_crMerge_top` is
syntactically unchanged: its `Pre` is the only slot the repair touches, and the weakened predicate
plugs in verbatim.  The one remaining obligation is the decoder half `hdec`, now required from the
window pin rather than from the exact `decoderStart`; it is named in the report as the fifth
hypothesis (Proposition 2.3 is published only from `decoderStart`'s whole memory). -/
theorem stageRun_crMerge_top_window {Sinit Srow Sdec Sassem Sres Sdec23 : Stmt} {E : RAMEnv}
    {Tdec : ℝ} {M : ℕ} {y : Fin M → ZMod 2} {ab al bb bl ob : ℕ} {Lx : List ℕ} {S xhat : Finset ℕ}
    (hno : sNoJumpB Sdec23 = true) (hhf : sHaltFreeB Sdec23 = true)
    (hdec : ∀ s : RAMState, s.pc = 0 →
      CrStageInW E M y ab al bb bl ob Lx (withPc (dCrBase Sinit Srow Sdec Sassem Sres) s) →
      ∃ s', HaltsWithin (programOfStatement Sdec23) E Tdec s s' ∧
        CrMergeIn E ab al bb bl ob Lx S
          (withPc (dCrBase Sinit Srow Sdec Sassem Sres + Sdec23.len) s'))
    (hLx : Lx.toFinset = xhat) (hW : 1 < 2 ^ E.W) :
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres (ScrStage Sdec23)) E
      (dCrBase Sinit Srow Sdec Sassem Sres)
      (dEnd Sinit Srow Sdec Sassem Sres (ScrStage Sdec23))
      (Tdec + RMR.mrgCost al bl) (CrStageInW E M y ab al bb bl ob Lx)
      (fun s' => OutListIs s' (symmDiff xhat S)) :=
  stageRun_crMerge_top hno hhf hdec hLx hW

end CRS
end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.CRS.crStageInW_iff
#print axioms LinearSetReconciliation327.Main.CRS.crStageInW_of_crStageIn
#print axioms LinearSetReconciliation327.Main.CRS.crStageInW_of_agree
#print axioms LinearSetReconciliation327.Main.CRS.crStageIn_forces_zero
#print axioms LinearSetReconciliation327.Main.CRS.crStageInW_not_of_garbage
#print axioms LinearSetReconciliation327.Main.CRS.crStageIn_subsingleton
#print axioms LinearSetReconciliation327.Main.CRS.crStageInW_inhabited_nondegen
#print axioms LinearSetReconciliation327.Main.CRS.crStageInW_nondegen_concrete
#print axioms LinearSetReconciliation327.Main.CRS.crStageInW_concrete_not_old
#print axioms LinearSetReconciliation327.Main.CRS.crMergeIn_frame
#print axioms LinearSetReconciliation327.Main.CRS.stageRun_crMerge_top_window


