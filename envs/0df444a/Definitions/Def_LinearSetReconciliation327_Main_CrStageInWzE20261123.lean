-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CrStageInWzE20261123
-- name    : LinearSetReconciliation327_Main_CrStageInWzE20261123
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T12:06:21.139798+00:00
-- url     : https://prove2.me/theorems/c619e2db-91dc-4a82-8e28-222c2db78094
-- title:
--   The cr pre with the estimate-payload frame (CrStageInWzE)
-- statement:
--   Theorem 6.5's `cr` block is 2.3's decoder, then `upkSetup`, the 31-instruction unpack and the merge; the published `crMergeInD_of_upk` needs the packed estimate `C8R.HoldsVecPad E.W m xbase s y` at the unpack's entry, because the unpack is what turns the estimate into the merge's A-side list `mList mem ab al = Lx`. The published `cr` pins (`CrStageInW`, `CrStageInWz`) do not mention that buffer. This bundle states the corrected pre `CrStageInWzE` = `CrStageInWz` (the decoder's registers, its payload window `[0, wordsOf E.W M)` and its finite zero window `[wordsOf E.W M, Z)`) **conjoined with the estimate-payload frame**, and proves its six projections, both implications to the weaker pins (`CrStageInWzE => CrStageInWz => CrStageInW`, one-way), and a **non-degenerate** inhabitant (memory `1` at `max Z (xbase+m) + k`, impossible for the old whole-memory pin). It also proves the two reductions the slot needs: memory agreement above a bound transports the estimate frame (`holdsVecPad_of_mem_frame`), and the decoder's exit facts plus that frame give `CrDecOut` (`crDecOut_of_exit`, with the word bound on the output window derived from `OutputsSupport` and `N <= 2^W`). The estimate frame is not invented: the published residual stage `stageRun_resP` posts exactly it.
-- source:
--   arXiv:2611.11409 (Linear Set Reconciliation with O(d) Additive Redundancy), Theorem 6.5 / Proposition 2.3

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CrStageInWz20261123

/-!
# `CrStageInWzE` — the `cr` pre with the estimate-payload frame

The published `cr` pre (`CRS.CrStageInW`, `CrStageInWz`) pins the *decoder's* payload window and the
decoder's finite zero window, and nothing else.  But the `cr` block is

```
2.3's decoder · upkSetup · the 31-instruction unpack · the merge,
```

and `CRS.crMergeInD_of_upk` needs the **packed estimate** `C8R.HoldsVecPad E.W m xbase s y` at the
unpack's entry: the unpack is what turns the estimate into the merge's `A`-side list
`mList mem ab al = Lx`.  Neither `CrStageInW` nor `CrStageInWz` mentions that buffer.

`CrStageInWzE` adds it as a fifth conjunct.  It is not a fabricated conjunct: the published residual
stage `C8R.stageRun_resP` **posts exactly it** —

```
fun s => DecInputOn E.W M 0 (setVec M (symmDiff Aset Bset)) [] s ∧ HoldsVecPad E.W m xhatBase s estVec
```

— so this is the estimate frame the real pipeline carries, made explicit in the `cr` contract.

Contents:

* `CrStageInWzE` and its six projections;
* `crStageInW_of_crStageInWzE` / `crStageInWz_of_crStageInWzE` (every consumer of the weaker pins is
  served) and a **non-degenerate** inhabitant;
* `holdsVecPad_of_mem_frame` — memory-agreement transports the estimate frame (this is what a decoder
  frame lemma feeds);
* `outList_lt_of_outputsSupport` — the word bound on the decoder's output window;
* `crDecOut_of_exit` — the two things a decoder exit has to supply to reach `CrDecOut`: the frame and
  the word bounds.  (The `decOutBase`-specific instantiation lives in
  `Def_…_DecOutBase20261123`, so that this bundle stays importable next to the `z`-address bundles.)

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

/-! ## 1. The corrected `cr` pre -/

/-- **The `cr` entry: the finite-zero pin *plus* the estimate-payload frame.**

`CrStageInWz E M Z y ab al bb bl ob Lx` pins the decoder's registers, its payload window
`[0, wordsOf E.W M)`, its finite zero window `[wordsOf E.W M, Z)` and the merge's block data.
`C8R.HoldsVecPad E.W m xbase yest` pins the packed estimate in `m` words at `xbase` — the buffer
`upkSetup`/`upkStmt` read to produce the merge's `A`-side list. -/
def CrStageInWzE (E : RAMEnv) (M Z : ℕ) (y : Fin M → ZMod 2) (xbase m : ℕ)
    (yest : Fin (E.W * m) → ZMod 2) (ab al bb bl ob : ℕ) (Lx : List ℕ) (t : RAMState) : Prop :=
  CrStageInWz E M Z y ab al bb bl ob Lx t ∧ C8R.HoldsVecPad E.W m xbase t yest

/-! ## 2. Projections -/

/-- The finite-zero pin underneath. -/
theorem crStageInWzE_wz {E : RAMEnv} {M Z xbase m : ℕ} {y : Fin M → ZMod 2}
    {yest : Fin (E.W * m) → ZMod 2} {ab al bb bl ob : ℕ} {Lx : List ℕ} {t : RAMState}
    (h : CrStageInWzE E M Z y xbase m yest ab al bb bl ob Lx t) :
    CrStageInWz E M Z y ab al bb bl ob Lx t := h.1

/-- **The estimate-payload frame**, the new conjunct. -/
theorem crStageInWzE_pad {E : RAMEnv} {M Z xbase m : ℕ} {y : Fin M → ZMod 2}
    {yest : Fin (E.W * m) → ZMod 2} {ab al bb bl ob : ℕ} {Lx : List ℕ} {t : RAMState}
    (h : CrStageInWzE E M Z y xbase m yest ab al bb bl ob Lx t) :
    C8R.HoldsVecPad E.W m xbase t yest := h.2

/-- The all-sixteen register pin. -/
theorem crStageInWzE_regs {E : RAMEnv} {M Z xbase m : ℕ} {y : Fin M → ZMod 2}
    {yest : Fin (E.W * m) → ZMod 2} {ab al bb bl ob : ℕ} {Lx : List ℕ} {t : RAMState}
    (h : CrStageInWzE E M Z y xbase m yest ab al bb bl ob Lx t) :
    t.regs = (decoderStart E.W y []).regs := h.1.1

/-- The decoder's payload window. -/
theorem crStageInWzE_pay {E : RAMEnv} {M Z xbase m : ℕ} {y : Fin M → ZMod 2}
    {yest : Fin (E.W * m) → ZMod 2} {ab al bb bl ob : ℕ} {Lx : List ℕ} {t : RAMState}
    (h : CrStageInWzE E M Z y xbase m yest ab al bb bl ob Lx t) :
    ∀ j : ℕ, j < wordsOf E.W M → t.mem j = packMem E.W y j := h.1.2.1

/-- The decoder's finite zero window. -/
theorem crStageInWzE_zero {E : RAMEnv} {M Z xbase m : ℕ} {y : Fin M → ZMod 2}
    {yest : Fin (E.W * m) → ZMod 2} {ab al bb bl ob : ℕ} {Lx : List ℕ} {t : RAMState}
    (h : CrStageInWzE E M Z y xbase m yest ab al bb bl ob Lx t) :
    ∀ a : ℕ, wordsOf E.W M ≤ a → a < Z → t.mem a = 0 := h.1.2.2.1

/-- The merge's block data. -/
theorem crStageInWzE_data {E : RAMEnv} {M Z xbase m : ℕ} {y : Fin M → ZMod 2}
    {yest : Fin (E.W * m) → ZMod 2} {ab al bb bl ob : ℕ} {Lx : List ℕ} {t : RAMState}
    (h : CrStageInWzE E M Z y xbase m yest ab al bb bl ob Lx t) :
    CrMergeData E ab al bb bl ob Lx := h.1.2.2.2

/-! ## 3. It serves every weaker pin -/

theorem crStageInWz_of_crStageInWzE {E : RAMEnv} {M Z xbase m : ℕ} {y : Fin M → ZMod 2}
    {yest : Fin (E.W * m) → ZMod 2} {ab al bb bl ob : ℕ} {Lx : List ℕ} {t : RAMState}
    (h : CrStageInWzE E M Z y xbase m yest ab al bb bl ob Lx t) :
    CrStageInWz E M Z y ab al bb bl ob Lx t := h.1

theorem crStageInW_of_crStageInWzE {E : RAMEnv} {M Z xbase m : ℕ} {y : Fin M → ZMod 2}
    {yest : Fin (E.W * m) → ZMod 2} {ab al bb bl ob : ℕ} {Lx : List ℕ} {t : RAMState}
    (h : CrStageInWzE E M Z y xbase m yest ab al bb bl ob Lx t) :
    CrStageInW E M y ab al bb bl ob Lx t :=
  crStageInW_of_crStageInWz h.1

/-! ## 4. Memory agreement transports the estimate frame -/

/-- **A memory frame above `B` preserves the estimate buffer.**  If the decoder leaves every address
`≥ B` alone and the estimate sits at `xbase ≥ B`, the buffer survives it.  This is the exact shape a
decoder memory-frame lemma feeds. -/
theorem holdsVecPad_of_mem_frame {W m xbase B : ℕ} {y : Fin (W * m) → ZMod 2} {s s' : RAMState}
    (hframe : ∀ a : ℕ, B ≤ a → s'.mem a = s.mem a) (hpad : C8R.HoldsVecPad W m xbase s y)
    (hxb : B ≤ xbase) : C8R.HoldsVecPad W m xbase s' y := by
  intro j hj
  rw [hframe (xbase + j) (by omega)]
  exact hpad j hj

/-! ## 5. From a decoder exit to `CrDecOut` -/

/-- **The word bound on the decoder's output window.**  The decoded coordinates are `< N`, so each
output word is `< N ≤ 2 ^ E.W`; `CrMergeInD` needs it. -/
theorem outList_lt_of_outputsSupport {N : ℕ} {x : Fin N → ZMod 2} {s : RAMState} {W : ℕ}
    (hout : OutputsSupport s x) (hWN : N ≤ 2 ^ W) :
    ∀ p, p < s.regs 1 → s.mem (s.regs 0 + p) < 2 ^ W := by
  intro p hp
  have hmem : s.mem (s.regs 0 + p) ∈ outList s := by
    unfold outList
    exact List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩
  obtain ⟨i, hi, hx⟩ := (hout.2 _).mp hmem
  rw [← hi]
  exact lt_of_lt_of_le i.isLt hWN

/-- **`CrDecOut` from a decoder exit and a memory frame.**  The two ingredients the published
`crDecOut_of_outputsSupport` was missing are supplied here: the estimate frame at the *exit* state
(transported by `holdsVecPad_of_mem_frame`) and the word bound on the output window. -/
theorem crDecOut_of_exit {E : RAMEnv} {N : ℕ} {x : Fin N → ZMod 2} {xbase m bb bl B : ℕ}
    {y : Fin (E.W * m) → ZMod 2} {s s' : RAMState}
    (hout : OutputsSupport s' x) (h0 : s'.regs 0 = bb) (h1 : s'.regs 1 = bl)
    (hframe : ∀ a : ℕ, B ≤ a → s'.mem a = s.mem a)
    (hpad : C8R.HoldsVecPad E.W m xbase s y) (hxb : B ≤ xbase)
    (hval : ∀ p, p < bl → s'.mem (bb + p) < 2 ^ E.W)
    (hbl : bl < 2 ^ E.W) (hbbbl : bb + bl ≤ 2 ^ E.W) :
    CrDecOut E xbase m bb bl y ((univ.filter fun i : Fin N => x i = 1).image Fin.val) s' :=
  crDecOut_of_outputsSupport hout h0 h1
    (holdsVecPad_of_mem_frame hframe hpad hxb) hval hbl hbbbl

/-- The same with the word bound *derived* from `OutputsSupport` and `N ≤ 2 ^ E.W`. -/
theorem crDecOut_of_exit' {E : RAMEnv} {N : ℕ} {x : Fin N → ZMod 2} {xbase m bb bl B : ℕ}
    {y : Fin (E.W * m) → ZMod 2} {s s' : RAMState}
    (hout : OutputsSupport s' x) (h0 : s'.regs 0 = bb) (h1 : s'.regs 1 = bl)
    (hframe : ∀ a : ℕ, B ≤ a → s'.mem a = s.mem a)
    (hpad : C8R.HoldsVecPad E.W m xbase s y) (hxb : B ≤ xbase)
    (hWN : N ≤ 2 ^ E.W) (hbl : bl < 2 ^ E.W) (hbbbl : bb + bl ≤ 2 ^ E.W) :
    CrDecOut E xbase m bb bl y ((univ.filter fun i : Fin N => x i = 1).image Fin.val) s' := by
  refine crDecOut_of_exit hout h0 h1 hframe hpad hxb ?_ hbl hbbbl
  intro p hp
  have h := outList_lt_of_outputsSupport hout hWN p (by rw [h1]; exact hp)
  rwa [h0] at h

/-! ## 6. Non-degenerately inhabited -/

/-- **A non-degenerate model of the corrected pre.**  Memory is the decoder's payload on
`[0, wordsOf E.W M)`, zero on `[wordsOf E.W M, Z)`, the packed estimate on `[xbase, xbase + m)`, and
`1` everywhere else — so it satisfies `CrStageInWzE` while `mem (max Z (xbase + m) + k) = 1`, which
the old whole-memory `CrStageIn` forbids. -/
theorem crStageInWzE_inhabited_nondegen {E : RAMEnv} {M Z xbase m : ℕ} {y : Fin M → ZMod 2}
    {yest : Fin (E.W * m) → ZMod 2} {ab al bb bl ob : ℕ} {Lx : List ℕ}
    (hW : 0 < E.W) (hZ : wordsOf E.W M ≤ Z) (hZx : Z ≤ xbase)
    (hdata : CrMergeData E ab al bb bl ob Lx) (k : ℕ) :
    ∃ t : RAMState, CrStageInWzE E M Z y xbase m yest ab al bb bl ob Lx t ∧
      t.mem (max Z (xbase + m) + k) = 1 := by
  classical
  have hw : wordsOf E.W (E.W * m) = m := C8R.asm_words_eq_padded E.W m hW
  refine ⟨⟨0, (decoderStart E.W y []).regs,
      fun a => if a < wordsOf E.W M then packMem E.W y a
        else if a < Z then 0
        else if a < xbase then 1
        else if a < xbase + m then packMem E.W yest (a - xbase) else 1⟩,
    ⟨⟨rfl, ?_, ?_, hdata⟩, ?_⟩, ?_⟩
  · intro j hj
    change (if j < wordsOf E.W M then packMem E.W y j else if j < Z then 0
      else if j < xbase then 1 else if j < xbase + m then packMem E.W yest (j - xbase) else 1)
      = packMem E.W y j
    rw [if_pos hj]
  · intro a ha haZ
    change (if a < wordsOf E.W M then packMem E.W y a else if a < Z then 0
      else if a < xbase then 1 else if a < xbase + m then packMem E.W yest (a - xbase) else 1) = 0
    rw [if_neg (by omega), if_pos haZ]
  · intro j hj
    rw [hw] at hj
    change (if xbase + j < wordsOf E.W M then packMem E.W y (xbase + j)
      else if xbase + j < Z then 0
      else if xbase + j < xbase then 1
      else if xbase + j < xbase + m then packMem E.W yest (xbase + j - xbase) else 1)
      = packMem E.W yest j
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      Nat.add_sub_cancel_left]
  · change (if max Z (xbase + m) + k < wordsOf E.W M then packMem E.W y (max Z (xbase + m) + k)
      else if max Z (xbase + m) + k < Z then 0
      else if max Z (xbase + m) + k < xbase then 1
      else if max Z (xbase + m) + k < xbase + m then packMem E.W yest (max Z (xbase + m) + k - xbase)
      else 1) = 1
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end CRS
end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.CRS.crStageInW_of_crStageInWzE
#print axioms LinearSetReconciliation327.Main.CRS.holdsVecPad_of_mem_frame
#print axioms LinearSetReconciliation327.Main.CRS.outList_lt_of_outputsSupport
#print axioms LinearSetReconciliation327.Main.CRS.crDecOut_of_exit
#print axioms LinearSetReconciliation327.Main.CRS.crDecOut_of_exit'
#print axioms LinearSetReconciliation327.Main.CRS.crStageInWzE_inhabited_nondegen


