-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_RowStage6_20261122
-- name    : LinearSetReconciliation327_Main_RowStage6_20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T15:36:52.401819+00:00
-- url     : https://prove2.me/theorems/03b8bec5-7a43-4040-a87f-dec929135300
-- title:
--   Theorem 6.5's row stage: the real nine-stage row body, closed without `hbody` or `At`
-- statement:
--   The row stage of Theorem 6.5's top-level decoder, at the *real* nine-stage body `save | clear | reload | stage | 2.1 decoder | setup | repack | restore | d65Inc | jmp`, with the per-row payload table as the arithmetic progression `payTabAddr + j * stageLen` (so there is no `d <= 51` cap) and at the composite header of the published `P21DetBndComp` decoder contract.  Proved here: `zBody_at` splits the compiled body into its eight `At` blocks at the exact numeral addresses; `zRowStage_closed` gives the `StageRun` with **no** `hbody` and no `At` hypothesis, cost `d * (K + 2) + 5` with `K = 64 t^2 + 352 t + 36 L + PDB + 20 t + 1308` and `L = stageLen`, `PDB = positiveDecoderBudget`; `zLayout_zPayDT` proves the layout for arbitrary `d` from one linear memory-size inequality and `zFlatLayout` is a concrete `d = 60` instance (refuting the old cap); `zWrun` is a genuine run of the real program at `d = 2` ending with both row bitmaps written and `ColIn 3`.  The only instance hypothesis is `hclose` (each stored row syndrome is within distance `t` of a codeword).  Axiom-clean: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`; local `cpl` 13 s.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5 / Theorem 1.1 (the top-level decoder) and Proposition 2.1 (the base-relative decoder); the project's verified row-stage development.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_RowStage4Pay20261122
import Definitions.Def_LinearSetReconciliation327_Main_CrStageDet20261122
import Definitions.Def_LinearSetReconciliation327_Main_DecodeLoopsPay20261122
import Definitions.Def_LinearSetReconciliation327_Main_P21DetBndComp20261122

/-!
# `RowStage5` — the row body with the *real* decoder at the composite header

`rowstage4` left one obstruction: the only proved decoder contract demanded
`E.det = detStd t N b iota`, and under that table the staging base `stageBase = det 16` is `0`, so
the decoder's own hypothesis `wordsOf (8w) (tw) <= beta` forced `t = 0`.  That obstruction is now
discharged by the published `P21DetBndComp`:

* `pinsketch_decoding_at_bounded_det` — the decoder at `detEnv (8*w) dt` for **any** `dt` that agrees
  with `detStd t N b iota` on the ten header slots `{0,1,2,4,5,6,8,9,10,12}` and on the multiplier
  table `[detMulBase w, inf)`, with the bounded zero hypothesis;
* `pinsketch_decoding_at_bounded_det_loc` — the same **plus** the output-location bound
  `s'.regs r0 + s'.regs r1 <= decoderAllocEnd t` (residual B).

Slots `3` (`rowBase`), `15` (`payTab`) and `16` (`stageBase`) are *not* constrained, so the row body
can carry its own layout in the same environment.  This bundle therefore

* **§1** re-points `zDecodeStage_sem` to `pinsketch_decoding_at_bounded_det_loc`;
* **§2** proves the two auxiliary facts the body consumes (`packMem` word bound = residual C, the
  output-length bound `r1 <= t`);
* **§3** proves the repack step **with its frame**, which the published `StageRun` forgets;
* **§4** states the layout arithmetic (residual F) as one small structure `ZRowLayout` and assembles
  the nine stages — save, clear/reload/stage, decode, setup, repack, restore, `d65Inc`, `jmp` — into
  one run from `zLoopHeads j` to `zLoopHeads (j+1)` (`zBody_hbody`);
* **§5** `zRowStage_real` fires **without** the `hbody` hypothesis;
* **§6** a concrete, non-degenerate instantiation.

No published file is modified.  The `*Det20261122` mirrors are copies of the published row-stage
bundles with the `DecoderLemmas` import replaced by `P21DetBndComp` (no other change, except the
deletions recorded in the report), because Lean cannot load `P21DetFront`/`P21DetBack` into an
environment that already contains `DecoderLemmas` (duplicate `axpyBody_spec` and 168 more names).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace RSD6

open R66 RDec RMR RSD RDL RSD3 RSD4 CRS

/-- The composite environment: 2.1's decoder environment at width `8w`, with the *composite* table
`dt`.  `dt` is free on slots `3`, `7`, `11`, `13`–`63` (so `rowBase`, `payTab`, `stageBase` and the
per-row payload bases all live there) and must equal `detStd t N b iota` on the slots the decoder
reads. -/
abbrev zDE (w : ℕ) (dt : ℕ → ℕ) : RAMEnv := detEnv (8 * w) dt

/-! ## 1. The decoder, re-pointed to the composite header -/

theorem zPinsketch_noJump (t w β : ℕ) : sNoJumpB (pinsketchRunStmt t w β) = true := rfl

theorem zPinsketch_haltFree (t w β : ℕ) : sHaltFreeB (pinsketchRunStmt t w β) = true := rfl

/-- **The real Proposition 2.1 decoder inside the row body.**  `zDecodeStage_sem` with its environment
weakened from `detEnv (8*w) (detStd t N b iota)` to `detEnv (8*w) dt` for any `dt` agreeing with
`detStd` on the slots the decoder reads, and with the output-location bound (residual B) added.

This is the change that makes the row body possible at all: under `detStd`, `det 16 = 0`, so
`stageBase = 0` and the decoder's hypothesis `wordsOf (8w) (tw) <= beta` is unsatisfiable at `t >= 1`
(`RSD4.zDetStd_no_rowBody`).  With `dt` free on slot `16` the staging base can be `wordsOf (8w) (tw)`,
while slots `3`, `15` carry the row base and the payload table — all in the *same* environment `E`. -/
theorem zDecodeStage_sem_loc {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F]
    {N t w : ℕ} (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (y : Fin (t * w) → ZMod 2) (β : ℕ) (dt : ℕ → ℕ) {G : Program} {base : ℕ} {s : RAMState}
    (hAt : At G base ((pinsketchRunStmt t w β).compile base))
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N) (h0 : ∀ i < N, ι i ≠ 0)
    (hinj : Set.InjOn ι (Set.Iio N)) (hpc : s.pc = base)
    (hpayload : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) = packMem (8 * w) y j)
    (hpayloadWord : ∀ j < wordsOf (8 * w) (t * w), s.mem (β + j) < 2 ^ (8 * w))
    (hzeroB : (∀ a, wordsOf (8 * w) (t * w) ≤ a → a < β → s.mem a = 0) ∧
      (∀ a, β + wordsOf (8 * w) (t * w) ≤ a → a < decoderAllocEnd t → s.mem a = 0))
    (hβL : wordsOf (8 * w) (t * w) ≤ β)
    (hβ2 : β + 2 * wordsOf (8 * w) (t * w) ≤ decoderAllocEnd t)
    (hβfit : β + 2 * wordsOf (8 * w) (t * w) < 2 ^ (8 * w))
    (hdt : (∀ a, (a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨
        a = 12) → dt a = detStd t N b ι a) ∧
      (∀ a, detMulBase w ≤ a → dt a = detStd t N b ι a)) :
    ∃ (k : ℕ) (s' : RAMState),
      (k : ℝ) ≤ ((positiveDecoderBudget t w + (24 * wordsOf (8 * w) (t * w) + 40) : ℕ) : ℝ) ∧
      (step G (detEnv (8 * w) dt))^[k] s = s' ∧
      s'.pc = base + (pinsketchRunStmt t w β).len ∧
      decoderPost (N := N) b ι y s' ∧
      (∀ a, decoderAllocEnd t ≤ a → s'.mem a = s.mem a) ∧
      s'.regs r0 + s'.regs r1 ≤ decoderAllocEnd t := by
  obtain ⟨s1, hHalts, hPost, hFrame, hLoc⟩ :=
    P21DetBndComp.pinsketch_decoding_at_bounded_det_loc (F := F) b ι y β (withPc 0 s) dt
      hN ht htN h0 hinj rfl
      (by simpa [withPc] using hpayload)
      (by simpa [withPc] using hpayloadWord)
      (by simpa [withPc] using hzeroB)
      hβL hβ2 hβfit hdt
  have hhalted : Halted (programOfStatement (pinsketchRunStmt t w β)) s1 := hHalts.choose_spec.2.2
  have hhalt : s1.pc = (pinsketchRunStmt t w β).len :=
    haltPc_of_haltFree (zPinsketch_haltFree t w β) hhalted
  obtain ⟨k, hk, hrun⟩ :=
    run_transport (G := G) (S := pinsketchRunStmt t w β) (base := base)
      (E := detEnv (8 * w) dt) (T := _) hAt
      (zPinsketch_noJump t w β) hHalts rfl hhalt
  refine ⟨k, withPc (base + (pinsketchRunStmt t w β).len) s1, hk, ?_, by simp, ?_, ?_, ?_⟩
  · rw [← hrun, withPc_withPc_of hpc]
  · simpa [decoderPost, OutputsSupport, outList, withPc] using hPost
  · intro a ha
    simpa [withPc] using hFrame a ha
  · simpa [withPc] using hLoc

/-! ## 2. Residual C and the output-length bound -/

/-- **The decoded length is at most `t`.**  `OutputsSupport` makes the output list a duplicate-free
enumeration of the support of `x`, so its length is at most `(binSupp x).card`. -/
theorem zOutList_len_le {n t : ℕ} {s : RAMState} {x : Fin n → ZMod 2}
    (h : OutputsSupport s x) (hc : (binSupp x).card ≤ t) : s.regs r1 ≤ t := by
  have hlen : (outList s).length = s.regs r1 := by simp [outList]
  rw [← hlen, ← List.toFinset_card_of_nodup h.1, RDec.toFinset_outList h]
  exact le_trans Finset.card_image_le hc

/-- **Residual C, discharged.**  The payload word bound the decoder asks for is the published
`packMem_lt_eight_mul`. -/
theorem zRowPayWord_lt {W M : ℕ} (hW : 1 ≤ W) (y : Fin M → ZMod 2) (addr : ℕ) :
    packMem (8 * W) y addr < 2 ^ (8 * W) :=
  P21DetBndComp.packMem_lt_eight_mul hW y addr

/-! ## 3. The repack step with its frame -/

/-- `ListSupports` identifies the list's `toFinset` with the support of `x`. -/
theorem zListSupports_toFinset {R : ℕ} {l : List ℕ} {x : Fin R → ZMod 2}
    (hx : ListSupports l x) :
    l.toFinset = (univ.filter (fun p : Fin R => x p = 1)).image (fun p => p.val) := by
  ext v
  rw [List.mem_toFinset, hx.2 v, Finset.mem_image]
  constructor
  · rintro ⟨i, hxi, hv⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hv⟩, hxi⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨i, hv, (Finset.mem_filter.mp hi).2⟩

/-- **The repack pass realises `RowOut`.**  `packMem` is itself the sum over the support, so the
accumulated bit sums are its words. -/
theorem zRowOut_repackMem {E : RAMEnv} {R j : ℕ} {m : ℕ → ℕ} {l : List ℕ} {x : Fin R → ZMod 2}
    (hx : ListSupports l x) : RowOut E R j x (RDec.repackMem E R j l m) := by
  intro i hi
  rw [RDec.repackMem_slot E R j l m i hi, zListSupports_toFinset hx]
  refine Eq.trans ?_ (RDec.packMem_eq_sum E.W R x i).symm
  exact Finset.sum_image
    (s := univ.filter (fun p : Fin R => x p = 1))
    (f := fun v : ℕ => if v / E.W = i then 2 ^ (v % E.W) else 0)
    (g := fun p : Fin R => p.val) (fun a _ c _ hac => Fin.ext hac)

/-- **The repack step, with the exact exit memory and its frame.**  `RDL.repackStageRun` forgets the
state; the row invariant needs it, because the invariant steps from `j` to `j+1` only if the repack
writes nothing outside `[rowSlot j, rowSlot j + wordsOf)`. -/
theorem zRepack_stage {P : Program} {E : RAMEnv} {R j len listBase base : ℕ} {m : ℕ → ℕ}
    {l : List ℕ} {x : Fin R → ZMod 2}
    (hAt : At P base (Stmt.compile repackStmt base)) (hW : 1 < 2 ^ E.W)
    (hlen : len < 2 ^ E.W) (hadr : listBase + len ≤ 2 ^ E.W)
    (hadr2 : rowSlot E R j + wordsOf E.W R ≤ 2 ^ E.W)
    (hdisj : listBase + len ≤ rowSlot E R j ∨ rowSlot E R j + wordsOf E.W R ≤ listBase)
    (hval : ∀ p, p < len → l.getD p 0 < 2 ^ E.W)
    (hR : ∀ p, p < len → l.getD p 0 < R)
    (hget : ∀ p, p < len → m (listBase + p) = l.getD p 0)
    (hl : l.Nodup) (hlen' : len = l.length)
    (s : RAMState) (hspc : s.pc = base) (hs0 : s.regs r0 = 0) (hs7 : s.regs r7 = listBase)
    (hs8 : s.regs r8 = len) (hs11 : s.regs r11 = E.W) (hs6 : s.regs r6 = wordsOf E.W R)
    (hs5 : s.regs r5 = rowSlot E R j) (hsm : s.mem = m)
    (hz : ∀ i, i < wordsOf E.W R → m (rowSlot E R j + i) = 0)
    (hx : ListSupports l x) :
    ∃ c : ℕ, c ≤ 20 * len + 2 ∧
      (step P E)^[c] s
        = { runBlock (Cond.lt r15 r0 r8).code E
              (repackFam E R j len listBase m s l base len) with pc := base + 20 } ∧
      RowOut E R j x (repackFam E R j len listBase m s l base len).mem ∧
      (∀ a, a < rowSlot E R j ∨ rowSlot E R j + wordsOf E.W R ≤ a →
        (repackFam E R j len listBase m s l base len).mem a = m a) := by
  have hWpos : 0 < E.W := by
    rcases Nat.eq_zero_or_pos E.W with h | h
    · rw [h] at hW; simp at hW
    · exact h
  obtain ⟨c, hc, hstep⟩ :=
    RDL.repackLoop_sem (P := P) (E := E) (R := R) (j := j) (len := len) (listBase := listBase)
      (base := base) (m := m) (l := l) hAt hW hlen hadr hadr2 hdisj hval hR hget hl hlen'
      s hspc hs0 hs7 hs8 hs11 hs6 hs5 hsm hz
  have hmem : (repackFam E R j len listBase m s l base len).mem = RDec.repackMem E R j l m := by
    rw [repackFam_mem E R j len listBase m s l base hsm hz len, hlen',
      RDL.repackLoopMem_end E R j m l hl hWpos]
  refine ⟨c, hc, hstep, ?_, ?_⟩
  · rw [hmem]
    exact zRowOut_repackMem hx
  · intro a ha
    rw [hmem]
    exact RDec.repackMem_frame E R j l m a (by
      rcases ha with h | h
      · exact Or.inl h
      · exact Or.inr h)

/-- **Residual F, with the payload table in memory as one base word plus the stride.**

`det 15` is the single `det` word holding the base `payTabAddr E` of the payload region; row `j`'s
payload base is `rowPayBase E j = (payTabAddr E + j * stageLen E) % 2^E.W`, so the per-row bases are
the arithmetic progression `base, base + L, base + 2L, ...` and no `d`-entry `det` table is needed.
The payload region is pinned by the three explicit conjuncts `hbaseK` (above 2.1's scratch, so the
clearing pass cannot erase it), `hpayTop` (below the row-output bitmaps) and `hpayWord` (a word). -/
structure ZRowLayout (E : RAMEnv) (R d t w cell : ℕ) : Prop where
  hW1      : 1 < 2 ^ E.W
  hW16     : 16 < 2 ^ E.W
  hlen     : stageLen E = wordsOf (8 * w) (t * w)
  hstage   : stageBase E = stageLen E
  hK       : decoderAllocEnd t < 2 ^ E.W
  hβ2      : stageBase E + 2 * stageLen E ≤ decoderAllocEnd t
  hβfit    : stageBase E + 2 * stageLen E < 2 ^ E.W
  hbaseW   : payTabAddr E < 2 ^ E.W
  hbaseK   : decoderAllocEnd t ≤ payTabAddr E
  hpayTop  : payTabAddr E + d * stageLen E ≤ rowBase E
  hpayWord : payTabAddr E + d * stageLen E < 2 ^ E.W
  hdeRow   : decoderAllocEnd t ≤ rowBase E
  hslotW   : ∀ r, r < d → rowSlot E R r + wordsOf E.W R ≤ 2 ^ E.W
  hslW     : ∀ r, r < d → rowSlot E R r < 2 ^ E.W
  hRW      : R + E.W < 2 ^ E.W
  hdet2    : E.det 2 % 2 ^ E.W = R
  hdet12   : E.det 12 % 2 ^ E.W = E.W
  hcell    : cell + 2 ≤ 2 ^ E.W
  hcellge  : decoderAllocEnd t ≤ cell
  hpayCell : payTabAddr E + d * stageLen E ≤ cell
  hrowCell : ∀ r, r < d → rowSlot E R r + wordsOf E.W R ≤ cell
  hdW      : d < 2 ^ E.W

theorem zWordsOf_le {W M : ℕ} (hW : 1 ≤ W) (hM : 1 ≤ M) : wordsOf W M ≤ M := by
  rw [wordsOf, Nat.div_le_iff_le_mul (by omega)]
  have h : M ≤ M * W := by
    calc M = M * 1 := (Nat.mul_one M).symm
      _ ≤ M * W := Nat.mul_le_mul_left _ hW
  omega

/-- `g + r * L < M` for `r < d`, from `g < M` and `g + d * L ≤ M`. -/
theorem zAddLt {g L r d M : ℕ} (hg : g < M) (h : g + d * L ≤ M) (hr : r < d) :
    g + r * L < M := by
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    simp only [Nat.mul_zero, Nat.add_zero]
    exact hg
  · have h1 : r + 1 ≤ d := by omega
    have h2 : (r + 1) * L ≤ d * L := Nat.mul_le_mul_right _ h1
    have h3 : r * L + L = (r + 1) * L := by ring
    omega

namespace ZRowLayout

variable {E : RAMEnv} {R d t w cell : ℕ}

theorem hcell1 (L : ZRowLayout E R d t w cell) : cell + 1 < 2 ^ E.W := by
  have := L.hcell; omega

theorem hcellW (L : ZRowLayout E R d t w cell) : cell < 2 ^ E.W := by
  have := L.hcell; omega

theorem hstageW (L : ZRowLayout E R d t w cell) : stageBase E + stageLen E ≤ 2 ^ E.W := by
  have h1 := L.hβ2
  have h2 := L.hK
  have h3 : stageBase E + stageLen E ≤ stageBase E + 2 * stageLen E := by omega
  omega

theorem h2L (L : ZRowLayout E R d t w cell) : 2 * stageLen E ≤ decoderAllocEnd t := by
  have h1 : stageLen E ≤ stageBase E + 2 * stageLen E := by
    have h2 := L.hstage; omega
  have h2 := L.hβ2
  omega

theorem hLle (L : ZRowLayout E R d t w cell) : stageLen E ≤ decoderAllocEnd t := by
  have := L.h2L; omega

/-- Every row's payload base is the `r`-th term of the progression. -/
theorem hpayMod (L : ZRowLayout E R d t w cell) {r : ℕ} (hr : r < d) :
    rowPayBase E r = payTabAddr E + r * stageLen E := by
  have h := zAddLt L.hbaseW (le_of_lt L.hpayWord) hr
  rw [rowPayBase, Nat.mod_eq_of_lt h]

/-- The payload region sits above 2.1's scratch, row by row. -/
theorem hdePay (L : ZRowLayout E R d t w cell) :
    ∀ r, r < d → decoderAllocEnd t ≤ rowPayBase E r := by
  intro r hr
  rw [L.hpayMod hr]
  have := L.hbaseK
  omega

/-- The payload region sits below the row-output bitmaps, row by row. -/
theorem hpayRow (L : ZRowLayout E R d t w cell) :
    ∀ r, r < d → rowPayBase E r + stageLen E ≤ rowBase E := by
  intro r hr
  rw [L.hpayMod hr]
  have h1 : (r + 1) * stageLen E ≤ d * stageLen E := Nat.mul_le_mul_right _ (by omega)
  have h2 := L.hpayTop
  have h3 : r * stageLen E + stageLen E = (r + 1) * stageLen E := by ring
  omega

theorem hpayCell' (L : ZRowLayout E R d t w cell) :
    ∀ r, r < d → rowPayBase E r + stageLen E ≤ cell := by
  intro r hr
  rw [L.hpayMod hr]
  have h1 : (r + 1) * stageLen E ≤ d * stageLen E := Nat.mul_le_mul_right _ (by omega)
  have h2 := L.hpayCell
  have h3 : r * stageLen E + stageLen E = (r + 1) * stageLen E := by ring
  omega

end ZRowLayout

/-! ## Satisfiability of the layout, for every `d` -/

/-- The payload-region base. -/
def zPayBase (t : ℕ) : ℕ := decoderAllocEnd t

/-- The row-output base: above the whole payload region. -/
def zRowBaseOf (t w d : ℕ) : ℕ := zPayBase t + d * wordsOf (8 * w) (t * w)

/-- The two save cells: above the whole row-output region. -/
def zCellOf (t w N d : ℕ) : ℕ := zRowBaseOf t w d + d * wordsOf (8 * w) N + 2

/-- **The composite table of the layout**: `det 3` is the row-output base, `det 15` the
payload-region base, `det 16` the staging base (= the payload length); every other slot is
`detStd`'s. -/
def zPayDT (t N w : ℕ) {F : Type} [Field F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (d : ℕ) : ℕ → ℕ :=
  fun p =>
    if p = 3 then zRowBaseOf t w d
    else if p = 15 then zPayBase t
    else if p = 16 then wordsOf (8 * w) (t * w)
    else detStd t N b ι p

theorem zPayDT_three {t N w : ℕ} {F : Type} [Field F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (d : ℕ) :
    zPayDT t N w b ι d 3 = zRowBaseOf t w d := by
  simp [zPayDT]

theorem zPayDT_pay {t N w : ℕ} {F : Type} [Field F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (d : ℕ) :
    zPayDT t N w b ι d 15 = zPayBase t := by
  simp [zPayDT]

theorem zPayDT_stage {t N w : ℕ} {F : Type} [Field F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (d : ℕ) :
    zPayDT t N w b ι d 16 = wordsOf (8 * w) (t * w) := by
  simp [zPayDT]

theorem zPayDT_four {t N w : ℕ} {F : Type} [Field F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (d : ℕ) :
    zPayDT t N w b ι d 4 = wordsOf (8 * w) (t * w) := by
  have h3 : (4 : ℕ) ≠ 3 := by omega
  have h15 : (4 : ℕ) ≠ 15 := by omega
  have h16 : (4 : ℕ) ≠ 16 := by omega
  simp [zPayDT, h3, h15, h16, detStd, hdrTab]

theorem zPayDT_two {t N w : ℕ} {F : Type} [Field F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (d : ℕ) :
    zPayDT t N w b ι d 2 = N := by
  have h3 : (2 : ℕ) ≠ 3 := by omega
  have h15 : (2 : ℕ) ≠ 15 := by omega
  have h16 : (2 : ℕ) ≠ 16 := by omega
  simp [zPayDT, h3, h15, h16, detStd, hdrTab]

theorem zPayDT_twelve {t N w : ℕ} {F : Type} [Field F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (d : ℕ) :
    zPayDT t N w b ι d 12 = 8 * w := by
  have h3 : (12 : ℕ) ≠ 3 := by omega
  have h15 : (12 : ℕ) ≠ 15 := by omega
  have h16 : (12 : ℕ) ≠ 16 := by omega
  simp [zPayDT, h3, h15, h16, detStd, hdrTab]

theorem zPayDT_agree_read {t N w : ℕ} {F : Type} [Field F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (d : ℕ) :
    ∀ p, (p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨ p = 12) →
      zPayDT t N w b ι d p = detStd t N b ι p := by
  intro p hp
  have h3 : p ≠ 3 := by omega
  have h15 : p ≠ 15 := by omega
  have h16 : p ≠ 16 := by omega
  simp [zPayDT, h3, h15, h16]

theorem zPayDT_agree_mul {t N w : ℕ} {F : Type} [Field F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (d : ℕ) :
    ∀ p, detMulBase w ≤ p → zPayDT t N w b ι d p = detStd t N b ι p := by
  intro p hp
  have h3 : p ≠ 3 := by rw [detMulBase_eq] at hp; omega
  have h15 : p ≠ 15 := by rw [detMulBase_eq] at hp; omega
  have h16 : p ≠ 16 := by rw [detMulBase_eq] at hp; omega
  simp [zPayDT, h3, h15, h16]

theorem zLayout_zPayDT {F : Type} [Field F] [Algebra (ZMod 2) F]
    {w t N d : ℕ} (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (ht : 1 ≤ t) (hw : 1 ≤ w) (hN : 1 ≤ N) (hNW : N + 8 * w < 2 ^ (8 * w))
    (h3t : 3 * (t + 8) < 2 ^ (8 * w))
    (hK : decoderAllocEnd t < 2 ^ (8 * w))
    (hroom : decoderAllocEnd t + d * wordsOf (8 * w) (t * w) + d * wordsOf (8 * w) N + 4
      ≤ 2 ^ (8 * w)) :
    ZRowLayout (zDE w (zPayDT t N w b ι d)) N d t w (zCellOf t w N d) := by
  have hpos : 0 < 2 ^ (8 * w) := Nat.two_pow_pos _
  have htw : 1 ≤ t * w := Nat.mul_pos (by omega) (by omega)
  -- the payload length is at most `t + 8`
  have hLle : wordsOf (8 * w) (t * w) ≤ t + 8 := by
    rw [wordsOf, Nat.div_le_iff_le_mul (show 0 < 8 * w by omega)]
    have h2 : t * w ≤ (t + 8) * (8 * w) := by nlinarith
    omega
  have hLpos : 1 ≤ wordsOf (8 * w) (t * w) := by
    rw [wordsOf, Nat.one_le_div_iff (show 0 < 8 * w by omega)]
    omega
  have hwopos : 1 ≤ wordsOf (8 * w) N := by
    rw [wordsOf, Nat.one_le_div_iff (show 0 < 8 * w by omega)]
    omega
  have hwole : wordsOf (8 * w) N ≤ N := zWordsOf_le (by omega) hN
  have hRBlt : zRowBaseOf t w d < 2 ^ (8 * w) := by
    have h1 : zRowBaseOf t w d ≤ decoderAllocEnd t + d * wordsOf (8 * w) (t * w) := by
      unfold zRowBaseOf zPayBase; omega
    omega
  have ht8 : t + 8 < 2 ^ (8 * w) := by omega
  have hLlt : wordsOf (8 * w) (t * w) < 2 ^ (8 * w) := by omega
  have hwolt : wordsOf (8 * w) N < 2 ^ (8 * w) := by omega
  have hcellLt : zCellOf t w N d + 2 ≤ 2 ^ (8 * w) := by
    unfold zCellOf zRowBaseOf zPayBase; omega
  -- the % 2^W reductions, stated in the definally-unfolded form
  have hmodPB : zPayBase t % 2 ^ (8 * w) = zPayBase t := by
    unfold zPayBase; exact Nat.mod_eq_of_lt hK
  have hmodL : wordsOf (8 * w) (t * w) % 2 ^ (8 * w) = wordsOf (8 * w) (t * w) :=
    Nat.mod_eq_of_lt hLlt
  have hmodRB : zRowBaseOf t w d % 2 ^ (8 * w) = zRowBaseOf t w d := by
    unfold zRowBaseOf zPayBase; exact Nat.mod_eq_of_lt hRBlt
  -- the four `det` reads of the layout
  have hSB : stageBase (zDE w (zPayDT t N w b ι d)) = wordsOf (8 * w) (t * w) := by
    show zPayDT t N w b ι d 16 % 2 ^ (8 * w) = wordsOf (8 * w) (t * w)
    rw [zPayDT_stage b ι d, Nat.mod_eq_of_lt hLlt]
  have hSL : stageLen (zDE w (zPayDT t N w b ι d)) = wordsOf (8 * w) (t * w) := by
    show zPayDT t N w b ι d 4 % 2 ^ (8 * w) = wordsOf (8 * w) (t * w)
    rw [zPayDT_four b ι d, Nat.mod_eq_of_lt hLlt]
  have hRB : rowBase (zDE w (zPayDT t N w b ι d)) = zRowBaseOf t w d := by
    show zPayDT t N w b ι d 3 % 2 ^ (8 * w) = zRowBaseOf t w d
    rw [zPayDT_three b ι d, Nat.mod_eq_of_lt hRBlt]
  have hPB : payTabAddr (zDE w (zPayDT t N w b ι d)) = zPayBase t := by
    show zPayDT t N w b ι d 15 % 2 ^ (8 * w) = zPayBase t
    rw [zPayDT_pay b ι d]
    unfold zPayBase
    exact Nat.mod_eq_of_lt hK
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (1 : ℕ) < 2 ^ (8 * w)
    exact Nat.one_lt_two_pow (by omega)
  · show (16 : ℕ) < 2 ^ (8 * w)
    have h2 : (2 : ℕ) ^ 5 ≤ 2 ^ (8 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rw [hSL]
  · rw [hSB, hSL]
  · exact hK
  · rw [hSB, hSL, decoderAllocEnd_eq]
    nlinarith
  · rw [hSB, hSL]
    show wordsOf (8 * w) (t * w) + 2 * wordsOf (8 * w) (t * w) < 2 ^ (8 * w)
    omega
  · show zPayDT t N w b ι d 15 % 2 ^ (8 * w) < 2 ^ (8 * w)
    exact Nat.mod_lt _ hpos
  · show decoderAllocEnd t ≤ zPayDT t N w b ι d 15 % 2 ^ (8 * w)
    rw [zPayDT_pay b ι d]
    unfold zPayBase
    exact Nat.le_of_eq (Nat.mod_eq_of_lt hK).symm
  · show zPayDT t N w b ι d 15 % 2 ^ (8 * w) + d * (zPayDT t N w b ι d 4 % 2 ^ (8 * w))
      ≤ zPayDT t N w b ι d 3 % 2 ^ (8 * w)
    rw [zPayDT_pay b ι d, zPayDT_four b ι d, zPayDT_three b ι d, hmodPB, hmodL, hmodRB]
    unfold zRowBaseOf zPayBase
    omega
  · show zPayDT t N w b ι d 15 % 2 ^ (8 * w) + d * (zPayDT t N w b ι d 4 % 2 ^ (8 * w))
      < 2 ^ (8 * w)
    rw [zPayDT_pay b ι d, zPayDT_four b ι d, hmodPB, hmodL]
    unfold zPayBase
    omega
  · show decoderAllocEnd t ≤ zPayDT t N w b ι d 3 % 2 ^ (8 * w)
    rw [zPayDT_three b ι d, hmodRB]
    unfold zRowBaseOf zPayBase
    omega
  · intro r hr
    show zPayDT t N w b ι d 3 % 2 ^ (8 * w) + r * wordsOf (8 * w) N + wordsOf (8 * w) N
      ≤ 2 ^ (8 * w)
    rw [zPayDT_three b ι d, hmodRB]
    unfold zRowBaseOf zPayBase
    have h1 : (r + 1) * wordsOf (8 * w) N ≤ d * wordsOf (8 * w) N :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : r * wordsOf (8 * w) N + wordsOf (8 * w) N = (r + 1) * wordsOf (8 * w) N := by ring
    omega
  · intro r hr
    show zPayDT t N w b ι d 3 % 2 ^ (8 * w) + r * wordsOf (8 * w) N < 2 ^ (8 * w)
    rw [zPayDT_three b ι d, hmodRB]
    have h := zAddLt (g := zRowBaseOf t w d) (L := wordsOf (8 * w) N) (r := r) (d := d)
      (M := 2 ^ (8 * w)) hRBlt (by unfold zRowBaseOf zPayBase; omega) hr
    exact h
  · show N + 8 * w < 2 ^ (8 * w)
    exact hNW
  · show zPayDT t N w b ι d 2 % 2 ^ (8 * w) = N
    rw [zPayDT_two b ι d, Nat.mod_eq_of_lt (by omega)]
  · show zPayDT t N w b ι d 12 % 2 ^ (8 * w) = 8 * w
    rw [zPayDT_twelve b ι d, Nat.mod_eq_of_lt (by omega)]
  · exact hcellLt
  · show decoderAllocEnd t ≤ zCellOf t w N d
    unfold zCellOf zRowBaseOf zPayBase
    omega
  · show zPayDT t N w b ι d 15 % 2 ^ (8 * w) + d * (zPayDT t N w b ι d 4 % 2 ^ (8 * w))
      ≤ zCellOf t w N d
    rw [zPayDT_pay b ι d, zPayDT_four b ι d, hmodPB, hmodL]
    unfold zCellOf zRowBaseOf zPayBase
    omega
  · intro r hr
    show zPayDT t N w b ι d 3 % 2 ^ (8 * w) + r * wordsOf (8 * w) N + wordsOf (8 * w) N
      ≤ zCellOf t w N d
    rw [zPayDT_three b ι d, hmodRB]
    unfold zCellOf zRowBaseOf zPayBase
    have h1 : (r + 1) * wordsOf (8 * w) N ≤ d * wordsOf (8 * w) N :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : r * wordsOf (8 * w) N + wordsOf (8 * w) N = (r + 1) * wordsOf (8 * w) N := by ring
    omega
  · show d < 2 ^ (8 * w)
    unfold zCellOf zRowBaseOf zPayBase at hcellLt
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h]; exact hpos
    · have h2 : d ≤ d * wordsOf (8 * w) N := by
        calc d = d * 1 := (Nat.mul_one d).symm
          _ ≤ d * wordsOf (8 * w) N := Nat.mul_le_mul_left _ hwopos
      omega

/-- **The repack step, adapted to the layout's restricted payload ordering.**  `RSD4`'s
`zRowInv_succ_repack` asks for `rowPayBase r + stageLen <= rowBase` at *every* `r`; the row body only
knows it for `r < d`, which is all the proof uses. -/
theorem zRowPayBelow_slot' {E : RAMEnv} {R d j : ℕ}
    (hpayRow : ∀ r, r < d → rowPayBase E r + stageLen E ≤ rowBase E) {r : ℕ} (hr : r < d) {i : ℕ}
    (hi : i < stageLen E) : rowPayBase E r + i < rowSlot E R j := by
  have h1 : rowPayBase E r + i < rowPayBase E r + stageLen E := by omega
  have h2 := hpayRow r hr
  have h3 : rowBase E ≤ rowSlot E R j := by rw [rowSlot]; exact Nat.le_add_right _ _
  omega

theorem zRowInv_succ_repack' {E : RAMEnv} {R d t w j : ℕ} {y : Fin d → Fin (t * w) → ZMod 2}
    {m m' : ℕ → ℕ} {x : Fin R → ZMod 2}
    (hj : j < d)
    (hupd : ∀ a, a < rowSlot E R j ∨ rowSlot E R j + wordsOf E.W R ≤ a → m' a = m a)
    (hpayRow : ∀ r, r < d → rowPayBase E r + stageLen E ≤ rowBase E)
    (hnew : RowOut E R j x m')
    (h : zRowInv E R d t w y j m) : zRowInv E R d t w y (j + 1) m' := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr i hi
    rw [hupd _ (Or.inl (zRowPayBelow_slot' hpayRow hr hi))]
    exact h.1 r hr i hi
  · intro r hr
    by_cases hrj : r = j
    · subst hrj
      exact ⟨x, hnew⟩
    · obtain ⟨x', hx'⟩ := h.2.1 r (by omega)
      refine ⟨x', fun i hi => ?_⟩
      rw [hupd _ (zRowSlot_disj_lin hrj hi)]
      exact hx' i hi
  · intro r hrj hrd i hi
    have hrj' : r ≠ j := by omega
    rw [hupd _ (zRowSlot_disj_lin hrj' hi)]
    exact h.2.2 r (by omega) hrd i hi

/-! ## 5. The nine-stage body -/

/-- **The nine stages, composed.**  From a state at the row-loop head `a` with the registers of
iteration `j` and the invariant at `j`, the body

`save -> clear/reload/stage -> decode -> setup -> repack -> restore -> d65Inc -> jmp`

returns to `a` in at most `64t^2 + 352t + 36L + PDB + 20t + 1308` steps, with the registers of
iteration `j+1` and the invariant at `j+1`.

`hclose` is the instance hypothesis of Theorem 6.5 ("row `j` lies within distance `t` of a
codeword"): it is what makes the decoder's *success* branch fire, so that `decoderPost` yields an
actual support `x` for `RowOut`, and it is also what bounds the decoded length by `t`. -/
theorem zBody_hbody
    {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F]
    {N t w : ℕ} (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (dt : ℕ → ℕ)
    {d : ℕ} {y : Fin d → Fin (t * w) → ZMod 2}
    {G : Program} {a cell : ℕ} {Sdec : Stmt}
    (LAY : ZRowLayout (zDE w dt) N d t w cell)
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N) (h0 : ∀ i < N, ι i ≠ 0)
    (hinj : Set.InjOn ι (Set.Iio N)) (hw : 1 ≤ w)
    (hdt : (∀ p, (p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨
        p = 12) → dt p = detStd t N b ι p) ∧
      (∀ p, detMulBase w ≤ p → dt p = detStd t N b ι p))
    (hclose : ∀ (j : ℕ) (hj : j < d), ∃ x : Fin N → ZMod 2,
        (binSupp x).card ≤ t ∧ pinBits b (pin ι t x) = y ⟨j, hj⟩)
    (hSdec : Sdec = pinsketchRunStmt t w (stageBase (zDE w dt)))
    (hAtSave : At G (a + 2) (zSaveCode cell))
    (hAtClear : At G (a + 6) (Stmt.compile (clearFull 0 (decoderAllocEnd t)) (a + 6)))
    (hAtReload : At G (a + 21) (zReloadCode cell))
    (hAtStage : At G (a + 23) (Stmt.compile stageStmt (a + 23)))
    (hAtDec : At G (a + 67) (Stmt.compile Sdec (a + 67)))
    (hAtSetup : At G (a + 67 + Sdec.len) (zSetupCode cell))
    (hAtRepack : At G (a + 84 + Sdec.len) (Stmt.compile repackStmt (a + 84 + Sdec.len)))
    (hAtRestore : At G (a + 104 + Sdec.len) (zRestoreCode cell))
    (hAtInc : At G (a + 125 + Sdec.len) d65Inc)
    (hAtJmp : G[a + 127 + Sdec.len]? = some (iJmp a)) :
    ∀ j < d, ∀ s : RAMState, s.pc = a → s.regs = zHeadsRegs j d →
      zRowInv (zDE w dt) N d t w y j s.mem →
      ∃ (s' : RAMState) (k : ℕ),
        k ≤ 64 * t * t + 352 * t + 36 * stageLen (zDE w dt) + positiveDecoderBudget t w
              + 20 * t + 1308 ∧
        (step G (zDE w dt))^[k]
          { runBlock d65Cond.code (zDE w dt) s with pc := a + d65Cond.code.length + 1 } = s' ∧
        s'.pc = a ∧ s'.regs = zHeadsRegs (j + 1) d ∧
        zRowInv (zDE w dt) N d t w y (j + 1) s'.mem := by
  subst hSdec
  intro j hj s hspc hregs hinv
  have hW1 : 1 < 2 ^ (zDE w dt).W := LAY.hW1
  have hW16 : 16 < 2 ^ (zDE w dt).W := LAY.hW16
  -- the loop test, then the body entry at `a + 2`
  let rg0 : Fin 16 → ℕ := (runBlock d65Cond.code (zDE w dt) s).regs
  have hrg0_1 : rg0 r1 = j := by
    show (runBlock d65Cond.code (zDE w dt) s).regs r1 = j
    rw [(zCond_regs_pres (zDE w dt) s).1, hregs, zHeadsRegs_r1]
  have hrg0_2 : rg0 r2 = d := by
    show (runBlock d65Cond.code (zDE w dt) s).regs r2 = d
    rw [(zCond_regs_pres (zDE w dt) s).2, hregs, zHeadsRegs_r2]
  -- 1. save `j`, `d`
  let M1 : ℕ → ℕ := Function.update (Function.update s.mem cell j) (cell + 1) d
  let rg1 : Fin 16 → ℕ := Function.update rg0 r15 (cell + 1)
  let st1 : RAMState := ⟨a + 6, rg1, M1⟩
  have hsave : (step G (zDE w dt))^[(zSaveCode cell).length] ⟨a + 2, rg0, s.mem⟩ = st1 := by
    rw [iterate_runBlock_of_at G (zDE w dt) (zSaveCode cell) ⟨a + 2, rg0, s.mem⟩ hAtSave
      (by simp [zSaveCode, NoBranch, Instr.NoBranchI])]
    rw [zSave_run (zDE w dt) (a + 2) cell rg0 s.mem hW1 LAY.hcellW LAY.hcell1, hrg0_1, hrg0_2]
  -- 2. clear / reload `r1 := j` / stage
  have hcellj1 : st1.mem cell = j := by
    show M1 cell = j
    rw [show M1 = Function.update (Function.update s.mem cell j) (cell + 1) d from rfl,
      Function.update_of_ne (by omega : cell ≠ cell + 1), Function.update_self]
  have hword1 : ∀ i, i < stageLen (zDE w dt) →
      st1.mem (rowPayBase (zDE w dt) j + i) < 2 ^ (zDE w dt).W := by
    intro i hi
    show M1 (rowPayBase (zDE w dt) j + i) < 2 ^ (zDE w dt).W
    have hlt : rowPayBase (zDE w dt) j + i < cell :=
      lt_of_lt_of_le (Nat.add_lt_add_left hi _) (LAY.hpayCell' j hj)
    rw [show M1 = Function.update (Function.update s.mem cell j) (cell + 1) d from rfl,
      Function.update_of_ne (by omega : rowPayBase (zDE w dt) j + i ≠ cell + 1),
      Function.update_of_ne (by omega : rowPayBase (zDE w dt) j + i ≠ cell),
      hinv.1 j hj i hi]
    exact zRowPayWord_lt hw (y ⟨j, hj⟩) i
  obtain ⟨kc, s2, hkc, hstep2, hpc2, hregs2, hz2a, hz2b, hfr2, hmem2⟩ :=
    zClearReloadStage_sem (P := G) (E := zDE w dt) (pc := a + 6) (t := t) (j := j)
      (K := decoderAllocEnd t) (cell := cell) (s := st1)
      hAtClear hAtReload hAtStage hW1 hW16 LAY.hK LAY.hcellW LAY.hcellge hcellj1
      (lt_trans hj LAY.hdW) rfl LAY.hstageW
      (by
        have h1 := LAY.hpayRow j hj
        have h2 : rowBase (zDE w dt) < 2 ^ (zDE w dt).W := rowBase_lt (zDE w dt)
        omega)
      hword1
      (by
        have h2 : 2 * stageLen (zDE w dt) ≤ rowPayBase (zDE w dt) j := by
          have h3 := LAY.h2L
          have h4 := LAY.hdePay j hj
          have h5 := LAY.hstage
          omega
        have h6 := LAY.hstage
        omega)
      (by
        have h1 := LAY.hβ2
        have h2 := LAY.hstage
        omega)
      (le_refl _)
      (LAY.hdePay j hj)
  -- 3. the real decoder
  have hpay2 : ∀ i < wordsOf (8 * w) (t * w),
      s2.mem (stageBase (zDE w dt) + i) = packMem (8 * w) (y ⟨j, hj⟩) i := by
    intro i hi
    have hiL : i < stageLen (zDE w dt) := by rw [LAY.hlen]; exact hi
    rw [hmem2]
    show writeArray (stageBase (zDE w dt)) (clearMem 0 M1 (decoderAllocEnd t))
      (fun i => clearMem 0 M1 (decoderAllocEnd t) (rowPayBase (zDE w dt) j + i))
      (stageLen (zDE w dt)) (stageBase (zDE w dt) + i) = packMem (8 * w) (y ⟨j, hj⟩) i
    rw [writeArray_get _ _ _ _ _ hiL]
    have hde : (0 : ℕ) + decoderAllocEnd t ≤ rowPayBase (zDE w dt) j + i := by
      rw [Nat.zero_add]
      exact le_trans (LAY.hdePay j hj) (Nat.le_add_right _ _)
    rw [clearMem_frame 0 M1 (decoderAllocEnd t) (rowPayBase (zDE w dt) j + i) (Or.inr hde)]
    have hlt : rowPayBase (zDE w dt) j + i < cell :=
      lt_of_lt_of_le (Nat.add_lt_add_left hiL _) (LAY.hpayCell' j hj)
    rw [show M1 = Function.update (Function.update s.mem cell j) (cell + 1) d from rfl,
      Function.update_of_ne (by omega : rowPayBase (zDE w dt) j + i ≠ cell + 1),
      Function.update_of_ne (by omega : rowPayBase (zDE w dt) j + i ≠ cell)]
    exact hinv.1 j hj i hiL
  have hpayW2 : ∀ i < wordsOf (8 * w) (t * w),
      s2.mem (stageBase (zDE w dt) + i) < 2 ^ (8 * w) := by
    intro i hi
    rw [hpay2 i hi]
    exact zRowPayWord_lt hw (y ⟨j, hj⟩) i
  have hzero2 : (∀ a', wordsOf (8 * w) (t * w) ≤ a' → a' < stageBase (zDE w dt) →
        s2.mem a' = 0) ∧
      (∀ a', stageBase (zDE w dt) + wordsOf (8 * w) (t * w) ≤ a' → a' < decoderAllocEnd t →
        s2.mem a' = 0) := by
    constructor
    · intro a' ha' hb'
      exact hz2a a' (by rw [LAY.hlen]; exact ha') hb'
    · intro a' ha' hb'
      exact hz2b a' (by rw [LAY.hlen]; exact ha') hb'
  obtain ⟨kd, s3, hkd, hstep3, hpc3, hpost3, hfr3, hloc3⟩ :=
    zDecodeStage_sem_loc (F := F) (N := N) (t := t) (w := w) b ι (y ⟨j, hj⟩)
      (stageBase (zDE w dt)) dt hAtDec hN ht htN h0 hinj hpc2
      hpay2 hpayW2 hzero2
      (by rw [← LAY.hlen, ← LAY.hstage])
      (by rw [← LAY.hlen]; exact LAY.hβ2)
      (by rw [← LAY.hlen]; exact LAY.hβfit)
      hdt
  -- the success branch
  have hr2ne : s3.regs r2 ≠ 0 := by
    intro hz
    obtain ⟨x, hx1, hx2⟩ := hclose j hj
    exact (hpost3.2 hz) ⟨x, hx1, hx2⟩
  obtain ⟨x, hxcard, hxpin, hxsupp⟩ := hpost3.1 hr2ne
  have hlenT : s3.regs r1 ≤ t := zOutList_len_le hxsupp hxcard
  -- 4. setup
  have hcell3 : s3.mem cell = j := by
    rw [hfr3 cell LAY.hcellge, hfr2 cell LAY.hcellge]
    exact hcellj1
  let st4 : RAMState :=
    ⟨a + 84 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len,
      zSetupRegs (zDE w dt) N j s3.regs, s3.mem⟩
  have hpc3' : s3.pc = a + 67 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len := hpc3
  have hs3 : s3 = ⟨a + 67 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len,
      s3.regs, s3.mem⟩ := by
    have h1 : s3 = (⟨s3.pc, s3.regs, s3.mem⟩ : RAMState) := rfl
    rw [h1, hpc3']
  have hsetupAt : (step G (zDE w dt))^[(zSetupCode cell).length] s3 = st4 := by
    rw [show s3 = (⟨a + 67 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len,
        s3.regs, s3.mem⟩ : RAMState) from hs3]
    rw [iterate_runBlock_of_at G (zDE w dt) (zSetupCode cell) _
      (hpc3'.symm ▸ hAtSetup)
      (by simp [zSetupCode, NoBranch, Instr.NoBranchI])]
    rw [zSetup_run (zDE w dt) (a + 67 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len)
      cell N j s3.regs s3.mem hW1 hW16 LAY.hcellW hcell3 (lt_trans hj LAY.hdW)
      LAY.hdet2 LAY.hdet12 LAY.hRW (LAY.hslW j hj)]
    refine zRamState_eq_of ?_ (fun i => rfl) rfl
    show (a + 67 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len) + 17
      = a + 84 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len
    omega
  -- 5. repack
  have hlistW : s3.regs r0 < 2 ^ (zDE w dt).W :=
    lt_of_le_of_lt (le_trans (Nat.le_add_right _ _) hloc3) LAY.hK
  have hlenW : s3.regs r1 < 2 ^ (zDE w dt).W :=
    lt_of_le_of_lt (le_trans (Nat.le_add_left _ _) hloc3) LAY.hK
  have hadrW : s3.regs r0 + s3.regs r1 ≤ 2 ^ (zDE w dt).W := le_trans hloc3 (le_of_lt LAY.hK)
  have hnodup : (listAt s3 (s3.regs r0) (s3.regs r1)).Nodup := hxsupp.1
  have hlenEq : s3.regs r1 = (listAt s3 (s3.regs r0) (s3.regs r1)).length := by
    simp [listAt]
  have hsuppL : ListSupports (listAt s3 (s3.regs r0) (s3.regs r1)) x := ⟨hxsupp.1, hxsupp.2⟩
  have hgetE := fun (p : ℕ) (hp : p < s3.regs r1) =>
    (RDL.getD_listAt s3 (s3.regs r0) (s3.regs r1) p hp).symm
  have hgetO : ∀ p, p < s3.regs r1 →
      s3.mem (s3.regs r0 + p) = (listAt s3 (s3.regs r0) (s3.regs r1)).getD p 0 := hgetE
  have hmemE := fun (p : ℕ) (hp : p < s3.regs r1) =>
    (mem_listAt s3 (s3.regs r0) (s3.regs r1) p hp : s3.mem (s3.regs r0 + p) ∈ outList s3)
  have hvall : ∀ p, p < s3.regs r1 → s3.mem (s3.regs r0 + p) < 2 ^ (zDE w dt).W := by
    intro p hp
    obtain ⟨i, hi, -⟩ := (hxsupp.2 (s3.mem (s3.regs r0 + p))).mp (hmemE p hp)
    have := LAY.hRW
    omega
  have hRll : ∀ p, p < s3.regs r1 → s3.mem (s3.regs r0 + p) < N := by
    intro p hp
    obtain ⟨i, hi, -⟩ := (hxsupp.2 (s3.mem (s3.regs r0 + p))).mp (hmemE p hp)
    omega
  have hvalO : ∀ p, p < s3.regs r1 →
      (listAt s3 (s3.regs r0) (s3.regs r1)).getD p 0 < 2 ^ (zDE w dt).W := by
    intro p hp
    rw [← hgetO p hp]; exact hvall p hp
  have hRO : ∀ p, p < s3.regs r1 → (listAt s3 (s3.regs r0) (s3.regs r1)).getD p 0 < N := by
    intro p hp
    rw [← hgetO p hp]; exact hRll p hp
  have hpay_le_slot : rowPayBase (zDE w dt) j ≤ rowSlot (zDE w dt) N j := by
    have h1 := LAY.hpayRow j hj
    have h2 : rowBase (zDE w dt) ≤ rowSlot (zDE w dt) N j := by
      rw [rowSlot]; exact Nat.le_add_right _ _
    omega
  have hzO : ∀ i, i < wordsOf (zDE w dt).W N →
      s3.mem (rowSlot (zDE w dt) N j + i) = 0 := by
    intro i hi
    have hde : decoderAllocEnd t ≤ rowSlot (zDE w dt) N j + i :=
      le_trans (LAY.hdePay j hj) (le_trans hpay_le_slot (Nat.le_add_right _ _))
    have hlt : rowSlot (zDE w dt) N j + i < cell :=
      lt_of_lt_of_le (Nat.add_lt_add_left hi _) (LAY.hrowCell j hj)
    rw [hfr3 _ hde, hfr2 _ hde]
    show M1 (rowSlot (zDE w dt) N j + i) = 0
    rw [show M1 = Function.update (Function.update s.mem cell j) (cell + 1) d from rfl,
      Function.update_of_ne (by omega : rowSlot (zDE w dt) N j + i ≠ cell + 1),
      Function.update_of_ne (by omega : rowSlot (zDE w dt) N j + i ≠ cell)]
    exact hinv.2.2 j le_rfl hj i hi
  obtain ⟨kr, hkr, hstep5, hrow5, hupd5⟩ :=
    zRepack_stage (P := G) (E := zDE w dt) (R := N) (j := j) (len := s3.regs r1)
      (listBase := s3.regs r0)
      (base := a + 84 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len)
      (m := s3.mem) (l := listAt s3 (s3.regs r0) (s3.regs r1)) (x := x)
      hAtRepack hW1 hlenW hadrW (LAY.hslotW j hj)
      (Or.inl (le_trans (le_trans hloc3 LAY.hdeRow) (by
        rw [rowSlot]; exact Nat.le_add_right _ _)))
      hvalO hRO hgetO hnodup hlenEq st4 rfl
      (zSetupRegs_r0 (zDE w dt) N j s3.regs)
      (by
        show zSetupRegs (zDE w dt) N j s3.regs r7 = s3.regs r0
        rw [zSetupRegs_r7, Nat.mod_eq_of_lt hlistW])
      (by
        show zSetupRegs (zDE w dt) N j s3.regs r8 = s3.regs r1
        rw [zSetupRegs_r8, Nat.mod_eq_of_lt hlenW])
      (zSetupRegs_r11 (zDE w dt) N j s3.regs)
      (zSetupRegs_r6 (zDE w dt) N j s3.regs)
      (zSetupRegs_r5 (zDE w dt) N j s3.regs)
      rfl hzO hsuppL
  let st5 : RAMState :=
    { runBlock (Cond.lt r15 r0 r8).code (zDE w dt)
        (repackFam (zDE w dt) N j (s3.regs r1) (s3.regs r0) s3.mem st4
          (listAt s3 (s3.regs r0) (s3.regs r1))
          (a + 84 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len) (s3.regs r1)) with
      pc := (a + 84 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len) + 20 }
  have hstep5' : (step G (zDE w dt))^[kr] st4 = st5 := hstep5
  have hrow5' : RowOut (zDE w dt) N j x st5.mem := hrow5
  have hupd5' : ∀ a', a' < rowSlot (zDE w dt) N j
      ∨ rowSlot (zDE w dt) N j + wordsOf (zDE w dt).W N ≤ a' → st5.mem a' = s3.mem a' := hupd5
  -- 6. restore, 7. d65Inc, 8. jmp
  have hls : rowSlot (zDE w dt) N j + wordsOf (zDE w dt).W N ≤ cell := LAY.hrowCell j hj
  have hcell5 : st5.mem cell = j := by
    rw [hupd5' cell (Or.inr hls)]
    exact hcell3
  have hcell5' : st5.mem (cell + 1) = d := by
    rw [hupd5' (cell + 1) (Or.inr (le_trans hls (Nat.le_succ cell)))]
    rw [hfr3 (cell + 1) (le_trans LAY.hcellge (Nat.le_succ cell)),
      hfr2 (cell + 1) (le_trans LAY.hcellge (Nat.le_succ cell))]
    show M1 (cell + 1) = d
    rw [show M1 = Function.update (Function.update s.mem cell j) (cell + 1) d from rfl,
      Function.update_self]
  have hpc5 : st5.pc = a + 104 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len := by
    show (a + 84 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len) + 20
      = a + 104 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len
    omega
  have hs5 : st5 = ⟨a + 104 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len,
      st5.regs, st5.mem⟩ := by
    have h1 : st5 = (⟨st5.pc, st5.regs, st5.mem⟩ : RAMState) := rfl
    rw [h1, hpc5]
  let st6 : RAMState :=
    ⟨a + 125 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len, zPreIncRegs j d, st5.mem⟩
  have hrestoreAt : (step G (zDE w dt))^[(zRestoreCode cell).length] st5 = st6 := by
    rw [hs5]
    rw [iterate_runBlock_of_at G (zDE w dt) (zRestoreCode cell) _ hAtRestore
      (by simp [zRestoreCode, zeroRegsCode, NoBranch, Instr.NoBranchI])]
    rw [zRestore_run (zDE w dt)
      (a + 104 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len) cell j d st5.regs st5.mem
      hW1 LAY.hcellW LAY.hcell1 hcell5 hcell5'
      (lt_trans hj LAY.hdW) LAY.hdW]
    refine zRamState_eq_of ?_ (fun i => rfl) rfl
    show (a + 104 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len) + 21
      = a + 125 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len
    omega
  have hpc6 : st6.pc = a + 125 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len := rfl
  let st7 : RAMState :=
    ⟨a + 127 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len,
      (zLoopHeads a d (fun _ => st5.mem) (j + 1)).regs, st5.mem⟩
  have hincAt : (step G (zDE w dt))^[d65Inc.length] st6 = st7 := by
    rw [show st6 = (⟨a + 125 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len,
        zPreIncRegs j d, st5.mem⟩ : RAMState) from rfl]
    rw [iterate_runBlock_of_at G (zDE w dt) d65Inc _ hAtInc
      (by simp [d65Inc, NoBranch, Instr.NoBranchI])]
    rw [zD65Inc_pre (zDE w dt)
      (a + 125 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len) a d j st5.mem hW1
      (lt_of_le_of_lt (Nat.succ_le_of_lt hj) LAY.hdW)]
    refine zRamState_eq_of ?_ (fun i => rfl) rfl
    show (a + 125 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len) + 2
      = a + 127 + (pinsketchRunStmt t w (stageBase (zDE w dt))).len
    omega
  have hjmpAt : (step G (zDE w dt))^[1] st7 = ⟨a, st7.regs, st7.mem⟩ := by
    rw [Function.iterate_one, step_eq_execInstr G (zDE w dt) st7 (iJmp a) hAtJmp, execInstr_jmp]
  -- the invariant, stage by stage
  have hinv1 : zRowInv (zDE w dt) N d t w y j M1 :=
    zRowInv_frame_cell (E := zDE w dt) (R := N) (j := j) (cell := cell) (by omega)
      (by
        intro a' h1 h2
        show M1 a' = s.mem a'
        rw [show M1 = Function.update (Function.update s.mem cell j) (cell + 1) d from rfl,
          Function.update_of_ne h2, Function.update_of_ne h1])
      (fun r hr => LAY.hpayCell' r hr) (fun r hr => LAY.hrowCell r hr) hinv
  have hinv2 : zRowInv (zDE w dt) N d t w y j s2.mem :=
    zRowInv_frame_ge (E := zDE w dt) (R := N) (j := j) (by omega) hfr2
      (fun r hr => LAY.hdePay r hr) LAY.hdeRow hinv1
  have hinv3 : zRowInv (zDE w dt) N d t w y j s3.mem :=
    zRowInv_frame_ge (E := zDE w dt) (R := N) (j := j) (by omega) hfr3
      (fun r hr => LAY.hdePay r hr) LAY.hdeRow hinv2
  have hinv4 : zRowInv (zDE w dt) N d t w y j st4.mem := hinv3
  have hinv5 : zRowInv (zDE w dt) N d t w y (j + 1) st5.mem :=
    zRowInv_succ_repack' hj hupd5' (fun r hr => LAY.hpayRow r hr) hrow5' hinv4
  -- the cost
  have h1 : kc ≤ 17 + 8 * decoderAllocEnd t + (12 * stageLen (zDE w dt) + 34) := by
    have hsc : stageCost (zDE w dt) ≤ 12 * stageLen (zDE w dt) + 34 := by
      simp only [stageCost]; omega
    omega
  have h2 : kd ≤ positiveDecoderBudget t w + (24 * stageLen (zDE w dt) + 40) := by
    have h := hkd
    rw [show wordsOf (8 * w) (t * w) = stageLen (zDE w dt) from LAY.hlen.symm] at h
    exact_mod_cast h
  have h3 : kr ≤ 20 * t + 2 := by omega
  have hK : decoderAllocEnd t = 8 * (t * t) + 44 * t + 144 := by
    rw [decoderAllocEnd_eq]; ring
  have hkey : 8 * decoderAllocEnd t = 64 * (t * t) + 352 * t + 1152 := by rw [hK]; ring
  have hfin : 4 + kc + kd + 17 + kr + 21 + 2 + 1
      ≤ 64 * (t * t) + 352 * t + 36 * stageLen (zDE w dt) + positiveDecoderBudget t w
        + 20 * t + 1308 := by omega
  have hfin' : 4 + kc + kd + 17 + kr + 21 + 2 + 1
      ≤ 64 * t * t + 352 * t + 36 * stageLen (zDE w dt) + positiveDecoderBudget t w
        + 20 * t + 1308 := by
    refine le_trans hfin (le_of_eq ?_)
    ring
  refine ⟨⟨a, st7.regs, st7.mem⟩,
    (zSaveCode cell).length + kc + kd + (zSetupCode cell).length + kr
      + (zRestoreCode cell).length + d65Inc.length + 1, ?_, ?_, rfl, ?_, ?_⟩
  · have hy : ((zSaveCode cell).length + kc + kd + (zSetupCode cell).length + kr
        + (zRestoreCode cell).length + d65Inc.length + 1 : ℕ)
        = (4 + kc + kd + 17 + kr + 21 + 2 + 1 : ℕ) := rfl
    rw [hy]
    exact_mod_cast hfin'
  · have hA : (step G (zDE w dt))^[(zSaveCode cell).length] ⟨a + 2, rg0, s.mem⟩ = st1 := hsave
    have hB : (step G (zDE w dt))^[kc] st1 = s2 := hstep2
    have hC : (step G (zDE w dt))^[kd] s2 = s3 := hstep3
    have hD : (step G (zDE w dt))^[(zSetupCode cell).length] s3 = st4 := hsetupAt
    have hE : (step G (zDE w dt))^[kr] st4 = st5 := hstep5'
    have hF : (step G (zDE w dt))^[(zRestoreCode cell).length] st5 = st6 := hrestoreAt
    have hG : (step G (zDE w dt))^[d65Inc.length] st6 = st7 := hincAt
    have i1 : (step G (zDE w dt))^[(zSaveCode cell).length + kc]
        ⟨a + 2, rg0, s.mem⟩ = s2 := zIter _ hA hB
    have i2 : (step G (zDE w dt))^[((zSaveCode cell).length + kc) + kd]
        ⟨a + 2, rg0, s.mem⟩ = s3 := zIter _ i1 hC
    have i3 : (step G (zDE w dt))^[(((zSaveCode cell).length + kc) + kd)
          + (zSetupCode cell).length] ⟨a + 2, rg0, s.mem⟩ = st4 := zIter _ i2 hD
    have i4 : (step G (zDE w dt))^[((((zSaveCode cell).length + kc) + kd)
          + (zSetupCode cell).length) + kr] ⟨a + 2, rg0, s.mem⟩ = st5 := zIter _ i3 hE
    have i5 : (step G (zDE w dt))^[(((((zSaveCode cell).length + kc) + kd)
          + (zSetupCode cell).length) + kr) + (zRestoreCode cell).length]
        ⟨a + 2, rg0, s.mem⟩ = st6 := zIter _ i4 hF
    have i6 : (step G (zDE w dt))^[((((((zSaveCode cell).length + kc) + kd)
          + (zSetupCode cell).length) + kr) + (zRestoreCode cell).length) + d65Inc.length]
        ⟨a + 2, rg0, s.mem⟩ = st7 := zIter _ i5 hG
    have hentry : ({ runBlock d65Cond.code (zDE w dt) s with
        pc := a + d65Cond.code.length + 1 } : RAMState) = ⟨a + 2, rg0, s.mem⟩ := by
      refine zRamState_eq_of ?_ (fun i => rfl) ?_
      · show a + d65Cond.code.length + 1 = a + 2
        rw [zD65Cond_code_length]
      · exact zCond_mem (zDE w dt) s
    rw [hentry]
    exact zIter _ i6 hjmpAt
  · show (zLoopHeads a d (fun _ => st5.mem) (j + 1)).regs = zHeadsRegs (j + 1) d
    exact zLoopHeads_regs_heads a d (fun _ => st5.mem) (j + 1)
  · show zRowInv (zDE w dt) N d t w y (j + 1) st5.mem
    exact hinv5

/-! ## 6. Residual H: the `At` plumbing from the loop head to the nine stages -/

/-- One stage of a `.seq`, split at its own length.  The second half's address is `base + d`. -/
theorem zAt_stage {P : Program} {base : ℕ} {S T : Stmt} {d : ℕ}
    (h : At P base (Stmt.compile (.seq S T) base)) (hd : S.len = d) :
    At P base (Stmt.compile S base) ∧ At P (base + d) (Stmt.compile T (base + d)) := by
  constructor
  · exact at_seq_left h
  · have h2 := at_seq_right h
    rwa [show base + S.len = base + d from by rw [hd]] at h2

theorem zCodeLen_save (cell : ℕ) : (Stmt.code (zSaveCode cell)).len = 4 := rfl
theorem zCodeLen_clear (t : ℕ) : (clearFull 0 (decoderAllocEnd t)).len = 15 := clearFull_len _ _
theorem zCodeLen_reload (cell : ℕ) : (Stmt.code (zReloadCode cell)).len = 2 := rfl
theorem zCodeLen_stage : stageStmt.len = 44 := stageStmt_len
theorem zCodeLen_setup (cell : ℕ) : (Stmt.code (zSetupCode cell)).len = 17 := rfl
theorem zCodeLen_repack : repackStmt.len = 20 := by
  simp [repackStmt, Stmt.len, repackBody, Cond.code]
theorem zCodeLen_restore (cell : ℕ) : (Stmt.code (zRestoreCode cell)).len = 21 := by
  rw [show (Stmt.code (zRestoreCode cell)).len = (zRestoreCode cell).length from rfl,
    zRestoreCode_length]

/-- **Residual H, closed.**  The compiled nine-stage body occupies the eight consecutive blocks
`save (4) | clear (15) | reload (2) | stage (44) | decode | setup (17) | repack (20) | restore (21)`,
each `At` fact stated at the numeral address `zBody_hbody` consumes.  `hSrow` is the definition of the
body (`Srow = zBody cell t Sdec`), kept as a parameter so that the large term is not unfolded here. -/
theorem zBody_at {G : Program} {a cell t : ℕ} {Sdec Srow : Stmt}
    (hSrow : Srow = zBody cell t Sdec)
    (hAt : At G (a + 2) (Stmt.compile Srow (a + 2))) :
    At G (a + 2) (zSaveCode cell) ∧
    At G (a + 6) (Stmt.compile (clearFull 0 (decoderAllocEnd t)) (a + 6)) ∧
    At G (a + 21) (zReloadCode cell) ∧
    At G (a + 23) (Stmt.compile stageStmt (a + 23)) ∧
    At G (a + 67) (Stmt.compile Sdec (a + 67)) ∧
    At G (a + 67 + Sdec.len) (zSetupCode cell) ∧
    At G (a + 84 + Sdec.len) (Stmt.compile repackStmt (a + 84 + Sdec.len)) ∧
    At G (a + 104 + Sdec.len) (zRestoreCode cell) := by
  subst hSrow
  obtain ⟨h1, q1⟩ := zAt_stage (S := Stmt.code (zSaveCode cell)) hAt (zCodeLen_save cell)
  obtain ⟨h2, q2⟩ := zAt_stage (S := clearFull 0 (decoderAllocEnd t)) q1 (zCodeLen_clear t)
  obtain ⟨h3, q3⟩ := zAt_stage (S := Stmt.code (zReloadCode cell)) q2 (zCodeLen_reload cell)
  obtain ⟨h4, q4⟩ := zAt_stage (S := stageStmt) q3 zCodeLen_stage
  obtain ⟨h5, q5⟩ := zAt_stage (S := Sdec) q4 rfl
  obtain ⟨h6, q6⟩ := zAt_stage (S := Stmt.code (zSetupCode cell)) q5 (zCodeLen_setup cell)
  obtain ⟨h7, h8⟩ := zAt_stage (S := repackStmt) q6 zCodeLen_repack
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h1
  · have h := h2
    rw [show a + 2 + 4 = a + 6 from by omega] at h
    exact h
  · have h := h3
    rw [show a + 2 + 4 + 15 = a + 21 from by omega] at h
    exact h
  · have h := h4
    rw [show a + 2 + 4 + 15 + 2 = a + 23 from by omega] at h
    exact h
  · have h := h5
    rw [show a + 2 + 4 + 15 + 2 + 44 = a + 67 from by omega] at h
    exact h
  · have h := h6
    rw [show a + 2 + 4 + 15 + 2 + 44 + Sdec.len = a + 67 + Sdec.len from by omega] at h
    exact h
  · have h := h7
    rw [show a + 2 + 4 + 15 + 2 + 44 + Sdec.len + 17 = a + 84 + Sdec.len from by omega] at h
    exact h
  · have h := h8
    rw [show a + 2 + 4 + 15 + 2 + 44 + Sdec.len + 17 + 20 = a + 104 + Sdec.len from by omega] at h
    exact h

/-! ## 7. `zRowStage_real` without the `hbody` hypothesis -/

/-- **The row stage, closed.**  No `hbody` (and no `At`) hypothesis: the body is `Srow`, its eight
`At` facts come from the program itself (`zAt_row_loopD` + `at_loop` + `zBody_at`), and the per-row
step is `zBody_hbody`.  `hSrow`, `hSdec` are the two *definitions* of the body and the decoder. -/
theorem zRowStage_closed {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F]
    {N t w : ℕ} (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (dt : ℕ → ℕ)
    {d : ℕ} {y : Fin d → Fin (t * w) → ZMod 2}
    {Sinit Srow Sdec Sassem Sres Scr : Stmt} {cell ell : ℕ}
    (LAY : ZRowLayout (zDE w dt) N d t w cell)
    (hN : 1 ≤ N) (ht : 1 ≤ t) (htN : t ≤ N) (h0 : ∀ i < N, ι i ≠ 0)
    (hinj : Set.InjOn ι (Set.Iio N)) (hw : 1 ≤ w)
    (hdt : (∀ p, (p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 8 ∨ p = 9 ∨ p = 10 ∨
        p = 12) → dt p = detStd t N b ι p) ∧
      (∀ p, detMulBase w ≤ p → dt p = detStd t N b ι p))
    (hclose : ∀ (j : ℕ) (hj : j < d), ∃ x : Fin N → ZMod 2,
        (binSupp x).card ≤ t ∧ pinBits b (pin ι t x) = y ⟨j, hj⟩)
    (hell : ell < 2 ^ (zDE w dt).W)
    (hSrow : Srow = zBody cell t Sdec)
    (hSdec : Sdec = pinsketchRunStmt t w (stageBase (zDE w dt))) :
    StageRun (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) (zDE w dt)
      (zDRowBase Sinit) (zDColHead Sinit Srow ell)
      ((d : ℝ) * (((64 * t * t + 352 * t + 36 * stageLen (zDE w dt) + positiveDecoderBudget t w
        + 20 * t + 1308 : ℕ) : ℝ) + 2) + 5)
      (fun s => s.regs = zHeadsRegs 0 d ∧ zRowInv (zDE w dt) N d t w y 0 s.mem)
      (fun s => zRowsOut (zDE w dt) N d s.mem ∧ ColIn ell s) := by
  refine RSD3.zRowStage_real (Srow := Srow) (Sdec := Sdec)
    (E := zDE w dt) (R := N) (K := 64 * t * t + 352 * t + 36 * stageLen (zDE w dt)
      + positiveDecoderBudget t w + 20 * t + 1308)
    (y := y) (ell := ell) LAY.hW1 hell ?_
  intro j hj s hpc hregs hinv
  have hSrowLen : Srow.len = 123 + Sdec.len := by rw [hSrow, zBody_len]
  have hloop := zAt_row_loopD Sinit Srow Sdec Sassem Sres Scr ell
  obtain ⟨-, -, hbodyAt, hjmp⟩ := at_loop hloop
  have hbodyAt2 : At (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell) (zDRowBase Sinit + 2)
      (Stmt.compile (.seq Srow (.code d65Inc)) (zDRowBase Sinit + 2)) := by
    have h := hbodyAt
    rw [show zDRowBase Sinit + d65Cond.code.length + 1 = zDRowBase Sinit + 2 from by
      rw [zD65Cond_code_length]] at h
    exact h
  obtain ⟨hbodyAt', hinc⟩ := zAt_stage (S := Srow) (T := Stmt.code d65Inc) (d := Srow.len) hbodyAt2 rfl
  have hinc' : At (zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell)
      (zDRowBase Sinit + 125 + Sdec.len) d65Inc := by
    have h := hinc
    rw [hSrowLen] at h
    rw [show zDRowBase Sinit + 2 + (123 + Sdec.len) = zDRowBase Sinit + 125 + Sdec.len from by
      omega] at h
    exact h
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ :=
    zBody_at (G := zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell)
      (a := zDRowBase Sinit) (cell := cell) (t := t) (Sdec := Sdec) (Srow := Srow) hSrow hbodyAt'
  have hjmp' : ((zProgDecOfTop Sinit Srow Sdec Sassem Sres Scr ell))[zDRowBase Sinit + 127 + Sdec.len]? = some (iJmp (zDRowBase Sinit)) := by
    have h := hjmp
    rw [show (Stmt.seq Srow (.code d65Inc)).len = Srow.len + 2 from rfl, hSrowLen] at h
    rw [show zDRowBase Sinit + d65Cond.code.length + 1 + ((123 + Sdec.len) + 2)
        = zDRowBase Sinit + 127 + Sdec.len from by
      rw [zD65Cond_code_length]; omega] at h
    exact h
  exact zBody_hbody (b := b) (ι := ι) (dt := dt) LAY hN ht htN h0 hinj hw hdt hclose hSdec
    o1 o2 o3 o4 o5 o6 o7 o8 hinc' hjmp' j hj s hpc hregs hinv


/-! ## 8. A concrete, non-degenerate decoded run at `d = 2` -/

/-- The `rowstage3/Witness.lean` field data, at `N = 1` so that the decoder's injectivity
hypothesis can hold: `F = ZMod 2`, `w = 1`, `b` the singleton basis, `ι ≡ 1`. -/
def zWb : Module.Basis (Fin 1) (ZMod 2) (ZMod 2) := Module.Basis.singleton (Fin 1) (ZMod 2)

def zWi : ℕ → ZMod 2 := fun _ => 1

def zWx : Fin 1 → ZMod 2 := fun _ => 1

def zWy : Fin 1 → ZMod 2 := pinBits zWb (pin zWi 1 zWx)

def zWy2 : Fin 2 → Fin (1 * 1) → ZMod 2 := fun _ => zWy

def zWdt : ℕ → ℕ := zPayDT 1 1 1 zWb zWi 2

def zWE : RAMEnv := zDE 1 zWdt

def zWSdec : Stmt := pinsketchRunStmt 1 1 (stageBase zWE)

def zWcell : ℕ := zCellOf 1 1 1 2

/-- The initial memory: the payload of each of the two rows at the payload region `[196, 198)`. -/
def zWm : ℕ → ℕ :=
  fun a => if a = 196 then packMem 8 zWy 0 else if a = 197 then packMem 8 zWy 0 else 0

/-- The initial state: at the row-loop head with the registers of iteration `0`. -/
def zWS : RAMState := ⟨zDRowBase (Stmt.code []), zHeadsRegs 0 2, zWm⟩

theorem zWL : stageLen zWE = 1 := by
  show zPayDT 1 1 1 zWb zWi 2 4 % 2 ^ (8 * 1) = 1
  rw [zPayDT_four]
  have h : wordsOf 8 1 = 1 := by decide
  rw [h]
  norm_num

theorem zWP : payTabAddr zWE = 196 := by
  show zPayDT 1 1 1 zWb zWi 2 15 % 2 ^ (8 * 1) = 196
  rw [zPayDT_pay]
  show decoderAllocEnd 1 % 2 ^ (8 * 1) = 196
  rw [decoderAllocEnd_eq]
  norm_num

theorem zWR : rowBase zWE = 198 := by
  show zPayDT 1 1 1 zWb zWi 2 3 % 2 ^ (8 * 1) = 198
  rw [zPayDT_three]
  show (decoderAllocEnd 1 + 2 * wordsOf (8 * 1) (1 * 1)) % 2 ^ (8 * 1) = 198
  rw [decoderAllocEnd_eq]
  have h : wordsOf 8 1 = 1 := by decide
  rw [h]
  norm_num

theorem zWLAY : ZRowLayout zWE 1 2 1 1 zWcell := by
  have hroom : decoderAllocEnd 1 + 2 * wordsOf (8 * 1) (1 * 1) + 2 * wordsOf (8 * 1) 1 + 4
      ≤ 2 ^ (8 * 1) := by
    rw [decoderAllocEnd_eq]
    have h : wordsOf 8 1 = 1 := by decide
    rw [h]
    norm_num
  have hK : decoderAllocEnd 1 < 2 ^ (8 * 1) := by
    rw [decoderAllocEnd_eq]; norm_num
  exact zLayout_zPayDT (F := ZMod 2) (b := zWb) (ι := zWi) (t := 1) (N := 1) (d := 2) (w := 1)
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) hK hroom

theorem zWslot (r : ℕ) : rowSlot zWE 1 r = 198 + r := by
  rw [rowSlot, zWR]
  have h : rowWords zWE 1 = 1 := by decide
  rw [h]
  ring

theorem zWpay (r : ℕ) (hr : r < 2) : rowPayBase zWE r = 196 + r := by
  rw [ZRowLayout.hpayMod zWLAY hr, zWP, zWL]
  ring

theorem zWinv : zRowInv zWE 1 2 1 1 zWy2 0 zWm := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr i hi
    have hi0 : i = 0 := by
      have : i < 1 := by rw [← zWL]; exact hi
      omega
    subst hi0
    rw [zWpay r hr]
    have hr2 : r = 0 ∨ r = 1 := by omega
    rcases hr2 with h | h <;> subst h <;> simp [zWm, zWy2]
  · intro r hr
    omega
  · intro r hrj hrd i hi
    have hi0 : i = 0 := by
      have hw1 : wordsOf zWE.W 1 = 1 := by decide
      rw [hw1] at hi
      omega
    subst hi0
    rw [zWslot r]
    have hr2 : r = 0 ∨ r = 1 := by omega
    rcases hr2 with h | h <;> subst h <;> simp [zWm, zWy2]

theorem zWhclose : ∀ (j : ℕ) (hj : j < 2), ∃ x : Fin 1 → ZMod 2,
    (binSupp x).card ≤ 1 ∧ pinBits zWb (pin zWi 1 x) = zWy2 ⟨j, hj⟩ := by
  intro j hj
  exact ⟨zWx, by decide, rfl⟩

/-- **The concrete decoded run.**  The *real* row program (`save | clear | reload | stage | the
Proposition 2.1 decoder | setup | repack | restore | d65Inc | jmp`) is run from the concrete state
`zWS` at `d = 2`, `t = 1`, `w = 1`, `N = 1`, `F = ZMod 2`: it reaches the column-loop head with both
row bitmaps written (`zRowsOut zWE 1 2`) and the column inputs in place (`ColIn 3`). -/
theorem zWrun :
    ∃ (k : ℕ) (s' : RAMState),
      (step (zProgDecOfTop (Stmt.code []) (zBody zWcell 1 zWSdec) zWSdec (Stmt.code [])
        (Stmt.code []) (Stmt.code []) 3) zWE)^[k] zWS = s' ∧
      s'.pc = zDColHead (Stmt.code []) (zBody zWcell 1 zWSdec) 3 ∧
      zRowsOut zWE 1 2 s'.mem ∧ ColIn 3 s' := by
  have h0 : ∀ i < 1, zWi i ≠ 0 := by
    intro i hi
    have : i = 0 := by omega
    subst this
    decide
  have hinj : Set.InjOn zWi (Set.Iio 1) := by
    intro a ha b hb _
    simp only [Set.mem_Iio] at ha hb
    omega
  have hdt := zPayDT_agree_read (b := zWb) (ι := zWi) (t := 1) (N := 1) (w := 1) (d := 2)
  have hdtm := zPayDT_agree_mul (b := zWb) (ι := zWi) (t := 1) (N := 1) (w := 1) (d := 2)
  have hell : 3 < 2 ^ zWE.W := by decide
  have hSR := zRowStage_closed (b := zWb) (ι := zWi) (dt := zWdt)
    (d := 2) (y := zWy2) (Sinit := Stmt.code []) (Sassem := Stmt.code [])
    (Sres := Stmt.code []) (Scr := Stmt.code []) (cell := zWcell) (ell := 3)
    zWLAY (by norm_num) (by norm_num) (by norm_num) h0 hinj (by norm_num)
    ⟨hdt, hdtm⟩ zWhclose hell rfl rfl
  obtain ⟨k, s', -, hstep, hpc, hpost⟩ := hSR zWS rfl ⟨rfl, zWinv⟩
  exact ⟨k, s', hstep, hpc, hpost⟩


/-! ## 9. The `51`-row cap is gone: a layout at `d = 60` -/

/-- A `det` table with only the six slots the row layout reads (no `detStd` at all): the row count
`2 ↦ 8`, the row-output base `3 ↦ 256`, the payload length `4 ↦ 1`, the word width `12 ↦ 16`, the
payload-region base `15 ↦ 196` and the staging base `16 ↦ 1`. -/
def zFlatDT : ℕ → ℕ :=
  fun p => if p = 2 then 8 else if p = 3 then 256 else if p = 4 then 1 else if p = 12 then 16
    else if p = 15 then 196 else if p = 16 then 1 else 0

def zFlatE : RAMEnv := detEnv 16 zFlatDT

/-- **`d = 60` — the old `det`-table layout was capped at `51`, this one is not.**  A fully concrete
`ZRowLayout` at `t = 1`, `w = 2` (`W = 16`), `N = 8`, `d = 60` rows: the payload region is
`[196, 256)`, the row-output region `[256, 316)`, and the two save cells at `318`. -/
theorem zFlatLayout : ZRowLayout zFlatE 8 60 1 2 318 := by
  have hWe : zFlatE.W = 16 := rfl
  have hL : stageLen zFlatE = 1 := by
    show zFlatDT 4 % 2 ^ 16 = 1
    simp [zFlatDT]
  have hB : stageBase zFlatE = 1 := by
    show zFlatDT 16 % 2 ^ 16 = 1
    simp [zFlatDT]
  have hP : payTabAddr zFlatE = 196 := by
    show zFlatDT 15 % 2 ^ 16 = 196
    simp [zFlatDT]
  have hR : rowBase zFlatE = 256 := by
    show zFlatDT 3 % 2 ^ 16 = 256
    simp [zFlatDT]
  have hw1 : wordsOf zFlatE.W 8 = 1 := by
    rw [hWe]; decide
  have hLw : wordsOf (8 * 2) (1 * 2) = 1 := by decide
  have hK : decoderAllocEnd 1 = 196 := by rw [decoderAllocEnd_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hWe]; norm_num
  · rw [hWe]; norm_num
  · rw [hL]; exact hLw
  · rw [hB, hL]
  · rw [hK, hWe]; norm_num
  · rw [hB, hL, hK]; norm_num
  · rw [hB, hL, hWe]; norm_num
  · rw [hP, hWe]; norm_num
  · rw [hP, hK]
  · rw [hP, hL, hR]
  · rw [hP, hL, hWe]; norm_num
  · rw [hR, hK]; norm_num
  · intro r hr
    rw [rowSlot, hR, rowWords, hw1]
    show 256 + r * 1 + 1 ≤ 2 ^ zFlatE.W
    rw [hWe]; omega
  · intro r hr
    rw [rowSlot, hR, rowWords, hw1]
    show 256 + r * 1 < 2 ^ zFlatE.W
    rw [hWe]; omega
  · rw [hWe]; norm_num
  · show zFlatDT 2 % 2 ^ 16 = 8
    simp [zFlatDT]
  · show zFlatDT 12 % 2 ^ 16 = 16
    simp [zFlatDT]
  · rw [hWe]; norm_num
  · rw [hK]; norm_num
  · rw [hP, hL]; norm_num
  · intro r hr
    rw [rowSlot, hR, rowWords, hw1]
    show 256 + r * 1 + 1 ≤ 318
    omega
  · rw [hWe]; norm_num

/-! ## 10. The setup block re-proved against the layout -/

/-- `zSetup_run` with every `det`/arithmetic hypothesis supplied by `ZRowLayout`. -/
theorem zSetup_run_Pay (E : RAMEnv) (pc cell R j : ℕ) (r : Fin 16 → ℕ) (m : ℕ → ℕ)
    {d t w : ℕ} (LAY : ZRowLayout E R d t w cell) (hcellj : m cell = j) (hjw : j < 2 ^ E.W)
    (hsl : rowSlot E R j < 2 ^ E.W) :
    runBlock (zSetupCode cell) E ⟨pc, r, m⟩ = ⟨pc + 17, zSetupRegs E R j r, m⟩ :=
  zSetup_run E pc cell R j r m LAY.hW1 LAY.hW16 LAY.hcellW hcellj hjw LAY.hdet2 LAY.hdet12
    LAY.hRW hsl

/-- `zSetup_lands_RepackPre` with every `det`/arithmetic hypothesis supplied by `ZRowLayout`. -/
theorem zSetup_lands_RepackPre_Pay (E : RAMEnv) (pc cell R j : ℕ) (r : Fin 16 → ℕ) (m : ℕ → ℕ)
    {len listBase : ℕ} (x : Fin R → ZMod 2) {d t w : ℕ}
    (LAY : ZRowLayout E R d t w cell) (hcellj : m cell = j) (hjw : j < 2 ^ E.W) (hj : j < d)
    (hR1 : 1 ≤ R)
    (hr0 : r r0 = listBase) (hr1 : r r1 = len)
    (hlistBase : listBase < 2 ^ E.W) (hlen : len < 2 ^ E.W)
    (hz : ∀ i, i < wordsOf E.W R → m (rowSlot E R j + i) = 0)
    (hval : ∀ v, v ∈ listAt (⟨pc, r, m⟩ : RAMState) listBase len → v < 2 ^ E.W)
    (hRv : ∀ v, v ∈ listAt (⟨pc, r, m⟩ : RAMState) listBase len → v < R)
    (hadr : listBase + len ≤ 2 ^ E.W)
    (hdisj : listBase + len ≤ rowSlot E R j ∨ rowSlot E R j + wordsOf E.W R ≤ listBase)
    (hsupp : ListSupports (listAt (⟨pc, r, m⟩ : RAMState) listBase len) x) :
    RepackPre E R j len listBase x (runBlock (zSetupCode cell) E ⟨pc, r, m⟩) :=
  have hWpos : 0 < E.W := by
    rcases Nat.eq_zero_or_pos E.W with h | h
    · have h1 := LAY.hW1
      rw [h] at h1
      simp at h1
    · exact h
  have hwo : 1 ≤ wordsOf E.W R := by
    rw [wordsOf, Nat.one_le_div_iff hWpos]
    omega
  have hsl : rowSlot E R j < 2 ^ E.W := by
    have := LAY.hslotW j hj
    omega
  zSetup_lands_RepackPre E pc cell R j r m x LAY.hW1 LAY.hW16 LAY.hcellW hcellj hjw
    LAY.hdet2 LAY.hdet12 LAY.hRW hsl
    hr0 hr1 hlistBase hlen (LAY.hslotW j hj) hz hval hRv hadr hdisj hsupp

end RSD6
end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.RSD6.zDecodeStage_sem_loc
#print axioms LinearSetReconciliation327.Main.RSD6.zOutList_len_le
#print axioms LinearSetReconciliation327.Main.RSD6.zRowOut_repackMem
#print axioms LinearSetReconciliation327.Main.RSD6.zRepack_stage
#print axioms LinearSetReconciliation327.Main.RSD6.zRowInv_succ_repack'
#print axioms LinearSetReconciliation327.Main.RSD6.zBody_hbody

#print axioms LinearSetReconciliation327.Main.RSD6.zLayout_zPayDT
#print axioms LinearSetReconciliation327.Main.RSD6.zBody_at
#print axioms LinearSetReconciliation327.Main.RSD6.zRowStage_closed
#print axioms LinearSetReconciliation327.Main.RSD6.zFlatLayout
#print axioms LinearSetReconciliation327.Main.RSD6.zSetup_run_Pay
#print axioms LinearSetReconciliation327.Main.RSD6.zSetup_lands_RepackPre_Pay
#print axioms LinearSetReconciliation327.Main.RSD6.zWrun


