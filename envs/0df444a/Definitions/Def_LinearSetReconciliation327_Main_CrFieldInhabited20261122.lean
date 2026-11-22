-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CrFieldInhabited20261122
-- name    : LinearSetReconciliation327_Main_CrFieldInhabited20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T10:03:50.552301+00:00
-- url     : https://prove2.me/theorems/c65ce3e5-1ee7-4163-962b-46b5400c7d66
-- title:
--   The restated `cr` field is inhabited at `N = 2`, `t = 1` (the real 282-instruction decoder)
-- statement:
--   The corrected `cr` field of Theorem 6.5 is inhabited at a concrete instance.  The data: `N = 2`, `t = 1`, `D = cr23D 2 = 2048`, `M = cr23M 1 = 2^68`, the sketch map `C v s = v` (injective in `v`, so a layered `(D, 2t, 1/16)`-expander -- there is no obstruction on the expander side), the witness `x = e_1`, the payload `y` = one word with bit 0 set, `eps = 1/16`, `bb = xbase = decOutBase 2 1`, `al = bl = 1`, `ab = bb + 2`, `ob = bb + 4`, `S = {1}` and `x_hat = packedSupp y = {0}`.  `crInst_preInhabited` exhibits the witness of the restated precondition: literally the state `cr23_decoding` starts from, conjoined with the merge's block data.  `crInst_crField` is the field itself at this instance: the real 282-instruction decoder, the five-instruction setup, the 31-instruction repack and the 86-instruction merge run inside the one fixed programme `progDecOfTop ... (CrStage4 decStmt ...)` from `dCrBase` to `dEnd`, at cost `Tdec + 5 + 49169 + 94`, and output `x_hat /\ {1}`; `crInst_decode` exposes the decoder's exit window `r0 = decOutBase 2 1`, which is what `CrDecOut` and the merge consume.  `#print axioms` of every declaration is `[propext, Classical.choice, Quot.sound]`: no `sorryAx`, no new axiom.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's `cr` stage and Proposition 2.3.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CR23DecRun20261122
import Definitions.Def_LinearSetReconciliation327_Main_CR23DecExit20261122
import Definitions.Def_LinearSetReconciliation327_Main_CrPipeline20261122
import Definitions.Def_LinearSetReconciliation327_Main_CrField20261122

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

/-- The concrete sketch map: `C v s = v`. -/
def crInstC : Fin 2 → Fin (cr23D 2) → Fin (cr23M 1) :=
  fun v _ => ⟨v.val, by
    have h := v.isLt
    have h2 : (2 : ℕ) ≤ 2 ^ 68 := by norm_num
    simp only [cr23M, Nat.mul_one]
    omega⟩

theorem crInstC_inj (s : Fin (cr23D 2)) {a b : Fin 2} (h : crInstC a s = crInstC b s) :
    a = b := by
  have h' : a.val = b.val := by simpa [crInstC] using congrArg Fin.val h
  exact Fin.ext h'

theorem crInstC_neigh (S : Finset (Fin 2)) (s : Fin (cr23D 2)) :
    cr23Neigh crInstC S s = S.card := by
  unfold cr23Neigh
  rw [Finset.card_image_of_injOn]
  intro a _ b _ hab
  exact crInstC_inj s hab

/-- **The concrete expander.**  `C` is a layered `(D, 2t, 1/16)`-expander. -/
theorem crInstC_expander : IsLayeredExpander crInstC (2 * 1) (1 / 16 : ℝ) := by
  intro S _
  have hterm : ∀ s : Fin (cr23D 2), ((cr23Neigh crInstC S s : ℕ) : ℝ) = (S.card : ℝ) := by
    intro s
    rw [crInstC_neigh]
  rw [Finset.sum_congr rfl (fun s _ => hterm s)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hD : (0 : ℝ) ≤ (cr23D 2 : ℝ) := by positivity
  have hc : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
  nlinarith

theorem crInst_eps : (16 : ℝ) * (1 / 16) ≤ 1 := by norm_num

/-- The witness vector: coordinate `1`. -/
def crInstX : Fin 2 → ZMod 2 := fun i => if i.val = 1 then 1 else 0

theorem crInstX_supp : (Finset.univ.filter fun i : Fin 2 => crInstX i = 1) = {1} := by
  ext i
  fin_cases i <;> simp [crInstX]

theorem crInstX_card : (cr23Supp crInstX).card ≤ 1 := by
  unfold cr23Supp
  rw [crInstX_supp]
  simp

/-- The word-RAM environment of the instance, at 3072-bit words. -/
abbrev crInstE : RAMEnv := detEnv (cr23Word 2) (cr23DecDet 2 1 crInstC)

/-- **The payload**, at the environment's own width `crInstE.W`: one word, bit `0` set. -/
def crInstY : Fin (crInstE.W * 1) → ZMod 2 := fun i => if i.val = 0 then 1 else 0

theorem crInstY_packMem : packMem crInstE.W crInstY 0 = 1 := by
  unfold packMem
  rw [Finset.sum_eq_single (⟨0, by decide⟩ : Fin (crInstE.W * 1))]
  · simp [crInstY]
  · intro b _ hb
    have hb0 : b.val ≠ 0 := by
      intro h
      exact hb (Fin.ext (by simpa using h))
    simp [crInstY, hb0]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem crInstY_wordsOf : wordsOf crInstE.W (crInstE.W * 1) = 1 :=
  C8R.asm_words_eq_padded (cr23Word 2) 1 (by decide)

/-- The payload frame, read off `mem base = 1`. -/
theorem crInstY_holds (s : RAMState) (base : ℕ) (h : s.mem base = 1) :
    C8R.HoldsVecPad crInstE.W 1 base s crInstY := by
  unfold C8R.HoldsVecPad
  rw [crInstY_wordsOf]
  intro j hj
  have hj0 : j = 0 := by omega
  subst hj0
  rw [Nat.add_zero]
  exact h.trans crInstY_packMem.symm

/-- **The packed support is `{0}`** — in particular nonempty. -/
theorem crInstY_packedSupp_mem (p : ℕ) :
    p ∈ CRS.packedSupp crInstE.W 1 crInstY ↔ p = 0 := by
  unfold CRS.packedSupp
  rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨-, i, hi, hy⟩
    have hi0 : i.val = 0 := by
      by_contra h
      have hz : crInstY i = 0 := by simp [crInstY, h]
      rw [hz] at hy
      exact absurd hy (by decide)
    omega
  · rintro rfl
    refine ⟨by decide, ⟨⟨0, by decide⟩, rfl, by simp [crInstY]⟩⟩

theorem crInstY_packedSupp_toFinset :
    (CRS.packedSupp crInstE.W 1 crInstY).toFinset = {0} := by
  ext p
  rw [List.mem_toFinset, crInstY_packedSupp_mem, Finset.mem_singleton]

theorem crInstY_packedSupp_len : (CRS.packedSupp crInstE.W 1 crInstY).length = 1 := by
  have hnd : (CRS.packedSupp crInstE.W 1 crInstY).Nodup :=
    List.Nodup.filter _ List.nodup_range
  have h := List.toFinset_card_of_nodup hnd
  rw [crInstY_packedSupp_toFinset] at h
  simpa using h.symm

theorem crInstY_packedSupp_ne : CRS.packedSupp crInstE.W 1 crInstY ≠ [] := by
  intro h
  have := crInstY_packedSupp_len
  rw [h] at this
  exact absurd this (by decide)

/-- The decoder's bound at `(N,t) = (2,1)`. -/
abbrev crInstTdec : ℝ :=
  (2 : ℝ) ^ 85 * max 1 (((1 : ℕ) : ℝ) * lg (((1 : ℕ) : ℝ) + 2) * lg (((2 : ℕ) : ℝ) + 2))

/-- **The concrete 2.3 run**, with the decoder's exit register exposed. -/
theorem crInst_decode :
    ∃ s' : RAMState,
      HaltsWithin progDec (detEnv (cr23Word 2) (cr23DecDet 2 1 crInstC)) crInstTdec
        (decoderStart (cr23Word 2) (cr23Sketch 2 1 crInstC crInstX) []) s' ∧
        OutputsSupport s' crInstX ∧ s'.regs r0 = decOutBase 2 1 := by
  obtain ⟨s', hhalt, hout, hr0⟩ :=
    decStmt_halts_exit 2 1 (by norm_num) (by norm_num) (by norm_num)
      crInstC crInstX (1 / 16) crInstC_expander (by norm_num) crInstX_card
  obtain ⟨k, hk, hstep, hstop⟩ := hhalt
  refine ⟨s', ⟨k, ?_, hstep, hstop⟩, hout, hr0⟩
  exact le_trans hk (decStmtCost_le_K 2 1 (by norm_num) (by norm_num) (by norm_num))

/-- **Room above the decoder's output base.**  `decOutBase 2 1 + W + 5 < 2^W`. -/
theorem crInst_room : decOutBase 2 1 + cr23Word 2 + 5 < 2 ^ cr23Word 2 := by
  have h1 : cr23DecEnd 2 1 ≤ 2 ^ (3 * cr23Lb 2 + 83) :=
    cr23DecEnd_le 2 1 (by norm_num) (by norm_num)
  have h2 : cr23DecEnd 2 1 = decOutBase 2 1 + 2 := by rw [cr23DecEnd]
  have h3 : 3 * cr23Lb 2 + 83 = 89 := by decide
  have h4 : decOutBase 2 1 + 2 ≤ 2 ^ 89 := by
    rw [h2, h3] at h1
    exact h1
  have h5 : (2 : ℕ) ^ 89 + 3075 < 2 ^ 90 := by norm_num
  have h6 : (2 : ℕ) ^ 90 ≤ 2 ^ 3072 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have h7 : cr23Word 2 = 3072 := by decide
  rw [h7]
  calc decOutBase 2 1 + 3072 + 5 = decOutBase 2 1 + 2 + 3075 := by ring
    _ ≤ 2 ^ 89 + 3075 := Nat.add_le_add_right h4 3075
    _ < 2 ^ 90 := h5
    _ ≤ 2 ^ 3072 := h6

/-- The decoder's own start state, with the sketch as payload. -/
abbrev crInstPre (Sinit Srow Sdec Sassem Sres : Stmt) : RAMState → Prop :=
  fun q => q = CRS.withPc (dCrBase Sinit Srow Sdec Sassem Sres)
    (decoderStart (cr23Word 2) (cr23Sketch 2 1 crInstC crInstX) [])

/-- **The decoder half**, discharged at the concrete instance. -/
theorem crInst_hdec (Sinit Srow Sdec Sassem Sres : Stmt) :
    ∀ s : RAMState, s.pc = 0 → crInstPre Sinit Srow Sdec Sassem Sres
      (CRS.withPc (dCrBase Sinit Srow Sdec Sassem Sres) s) →
      ∃ s', HaltsWithin (programOfStatement decStmt) crInstE crInstTdec s s' ∧
        CRS.CrDecOut crInstE (decOutBase 2 1) 1 (decOutBase 2 1) 1 crInstY ({1} : Finset ℕ)
          (CRS.withPc (dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len) s') := by
  intro s hpc hPre
  have hs : s = decoderStart (cr23Word 2) (cr23Sketch 2 1 crInstC crInstX) [] := by
    apply ramState_eq_of
    · rw [hpc]
      rfl
    · have h := congrArg RAMState.mem hPre
      simpa [CRS.withPc] using h
    · intro d
      have h := congrArg (fun st => st.regs d) hPre
      simpa [CRS.withPc] using h
  subst hs
  obtain ⟨s', hhalt, hout, hr0⟩ := crInst_decode
  refine ⟨s', ?_, ?_⟩
  · rwa [show programOfStatement decStmt = progDec from rfl]
  · show CRS.CrDecOut crInstE (decOutBase 2 1) 1 (decOutBase 2 1) 1 crInstY ({1} : Finset ℕ) s'
    have hbb : s'.regs 0 = decOutBase 2 1 := hr0
    have hset : (outList s').toFinset = ({1} : Finset ℕ) := by
      ext v
      rw [List.mem_toFinset, hout.2 v]
      constructor
      · rintro ⟨i, rfl, hi⟩
        fin_cases i
        · simp [crInstX] at hi
        · simp
      · intro hv
        rw [Finset.mem_singleton] at hv
        subst hv
        exact ⟨1, rfl, by simp [crInstX]⟩
    have hlen : (outList s').length = 1 := by
      have h := List.toFinset_card_of_nodup hout.1
      rw [hset] at h
      simpa using h.symm
    have hbl : s'.regs 1 = 1 := by
      have h : (outList s').length = s'.regs 1 := by simp [outList]
      omega
    have hmem1 : (1 : ℕ) ∈ outList s' := by
      rw [hout.2]
      exact ⟨1, rfl, by simp [crInstX]⟩
    have hmem : s'.mem (decOutBase 2 1) = 1 := by
      have hh := hmem1
      unfold outList at hh
      rw [hbl] at hh
      simp only [List.mem_map, List.mem_range] at hh
      obtain ⟨i, hi, hii⟩ := hh
      have hi0 : i = 0 := by omega
      subst hi0
      rw [Nat.add_zero, hbb] at hii
      exact hii
    refine ⟨hbb, hbl, ?_, hout.1, hset, ?_, ?_, ?_⟩
    · exact crInstY_holds s' (decOutBase 2 1) hmem
    · intro p hp
      have hp0 : p = 0 := by omega
      subst hp0
      rw [Nat.add_zero, hmem]
      exact cr23_one_lt_word 2 (by norm_num)
    · exact cr23_one_lt_word 2 (by norm_num)
    · show decOutBase 2 1 + 1 ≤ 2 ^ crInstE.W
      exact Nat.succ_le_of_lt
        (dec_out_add_lt_word 2 1 (by norm_num) (by norm_num) (j := 0) (by norm_num))

/-! ## The corrected `cr` field at the concrete instance -/

/-- The number of coordinates of the packed sketch: `cr23R 2 1`. -/
abbrev crInstM : ℕ := cr23R 2 1

/-- The packed sketch of the witness `x = e_1`: Proposition 2.3's input payload. -/
abbrev crInstYs : Fin crInstM → ZMod 2 := cr23Sketch 2 1 crInstC crInstX

/-- The merge's `A`-side list: the estimate `x̂ = {0}` as an explicit coordinate list. -/
abbrev crInstLx : List ℕ := [0]

theorem crInstW : cr23Word 2 = 3072 := by decide

/-- Room below `2 ^ W` for anything at most `cr23Word 2 + 5` past `decOutBase 2 1`. -/
theorem crInst_room_le (k : ℕ) (hk : k ≤ cr23Word 2 + 5) :
    decOutBase 2 1 + k < 2 ^ cr23Word 2 := by
  refine lt_of_le_of_lt ?_ crInst_room
  calc decOutBase 2 1 + k ≤ decOutBase 2 1 + (cr23Word 2 + 5) := Nat.add_le_add_left hk _
    _ = decOutBase 2 1 + cr23Word 2 + 5 := by rw [← Nat.add_assoc]

/-- **The merge's block data at the instance.**  `al = bl = 1`, the decoded residual sits in the
decoder's output window `[bb, bb+1)` with `bb = decOutBase 2 1`, the estimate in `[bb+2, bb+3)`,
the merge's output block at `bb+4`, and every block fits in a word. -/
theorem crInst_mergeData :
    CRS.CrMergeData crInstE (decOutBase 2 1 + 2) 1 (decOutBase 2 1) 1
      (decOutBase 2 1 + 4) crInstLx := by
  have hroom := crInst_room
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cr23_one_lt_word 2 (by norm_num)
  · exact cr23_one_lt_word 2 (by norm_num)
  · show decOutBase 2 1 + 2 + 1 ≤ 2 ^ cr23Word 2
    omega
  · show decOutBase 2 1 + 1 ≤ 2 ^ cr23Word 2
    omega
  · have h7 : decOutBase 2 1 + 4 + (1 + 1) + 1 = decOutBase 2 1 + 7 := by ring
    rw [h7]
    exact crInst_room_le 7 (by rw [crInstW]; norm_num)
  · exact Or.inl (by show decOutBase 2 1 + 2 + 1 ≤ decOutBase 2 1 + 4; omega)
  · exact Or.inl (by show decOutBase 2 1 + 1 ≤ decOutBase 2 1 + 4; omega)

/-- **The decoder half, with the corrected precondition.**  This is `stageRun_crPipeline`'s `hdec`
at the concrete instance: from 2.3's own start state (conjoined with the merge's block data) the
real 282-instruction decoder hands the merge its entry data. -/
theorem crInst_hdecIn (Sinit Srow Sdec Sassem Sres : Stmt) :
    ∀ s : RAMState, s.pc = 0 →
      CRS.CrStageIn crInstE crInstM crInstYs (decOutBase 2 1 + 2) 1 (decOutBase 2 1) 1
        (decOutBase 2 1 + 4) crInstLx
        (CRS.withPc (dCrBase Sinit Srow Sdec Sassem Sres) s) →
      ∃ s', HaltsWithin (programOfStatement decStmt) crInstE crInstTdec s s' ∧
        CRS.CrDecOut crInstE (decOutBase 2 1) 1 (decOutBase 2 1) 1 crInstY ({1} : Finset ℕ)
          (CRS.withPc (dCrBase Sinit Srow Sdec Sassem Sres + decStmt.len) s') := by
  intro s hpc hIn
  obtain ⟨hregs, hmem, -⟩ := hIn
  have hq : CRS.withPc (dCrBase Sinit Srow Sdec Sassem Sres) s
      = CRS.withPc (dCrBase Sinit Srow Sdec Sassem Sres)
        (decoderStart (cr23Word 2) crInstYs []) := by
    refine ramState_eq_of _ _ ?_ ?_ ?_
    · simp only [CRS.withPc]
    · simp only [crInstE, detEnv, CRS.withPc] at hmem ⊢
      exact hmem
    · intro d
      simp only [crInstE, detEnv, CRS.withPc] at hregs ⊢
      exact congrFun hregs d
  exact crInst_hdec Sinit Srow Sdec Sassem Sres s hpc hq

/-- **The corrected `cr` field's precondition is inhabited at the instance.**  The witness is
literally the state `cr23_decoding` starts from: the packed sketch on `[0, wordsOf W M)`, `r0 = 0`,
`r1 = wordsOf W M`, `r2 = 0`, conjoined with the merge's block data. -/
theorem crInst_preInhabited (Sinit Srow Sdec Sassem Sres : Stmt) :
    CRS.CrStageIn crInstE crInstM crInstYs (decOutBase 2 1 + 2) 1 (decOutBase 2 1) 1
      (decOutBase 2 1 + 4) crInstLx
      (CRS.withPc (dCrBase Sinit Srow Sdec Sassem Sres)
        (decoderStart (cr23Word 2) crInstYs [])) := by
  refine ⟨?_, ?_, crInst_mergeData⟩
  · simp only [crInstE, detEnv, CRS.withPc]
  · simp only [crInstE, detEnv, CRS.withPc]

/-! ### The side conditions of `stageRun_crPipeline`, at the instance -/

theorem crInst_hW : 1 < 2 ^ crInstE.W := cr23_one_lt_word 2 (by norm_num)

theorem crInst_hWm : crInstE.W * 1 < 2 ^ crInstE.W := by
  simp only [crInstE, detEnv]
  rw [Nat.mul_one]
  exact Nat.lt_two_pow_self

theorem crInst_hxdisj : decOutBase 2 1 + 1 ≤ decOutBase 2 1 + 2 :=
  Nat.add_le_add_left (by norm_num : 1 ≤ 2) _

theorem crInst_hab : decOutBase 2 1 + 2 + crInstE.W * 1 + 1 < 2 ^ crInstE.W := by
  simp only [crInstE, detEnv]
  rw [Nat.mul_one]
  have h : decOutBase 2 1 + 2 + cr23Word 2 + 1 = decOutBase 2 1 + (cr23Word 2 + 3) := by ring
  rw [h]
  exact crInst_room_le _ (Nat.add_le_add_left (by norm_num : 3 ≤ 5) _)

theorem crInst_hbb : decOutBase 2 1 < 2 ^ crInstE.W := by
  simp only [crInstE, detEnv]
  have h := dec_out_add_lt_word 2 1 (by norm_num) (by norm_num) (j := 0) (by norm_num)
  rw [Nat.add_zero] at h
  exact h

theorem crInst_hbl : 1 < 2 ^ crInstE.W := cr23_one_lt_word 2 (by norm_num)

theorem crInst_hob : decOutBase 2 1 + 4 < 2 ^ crInstE.W := by
  simp only [crInstE, detEnv]
  exact crInst_room_le 4 (by rw [crInstW]; norm_num)

theorem crInst_hdisj : decOutBase 2 1 + 1 ≤ decOutBase 2 1 + 2 ∨
    decOutBase 2 1 + 2 + (1 * crInstE.W + 1) ≤ decOutBase 2 1 := Or.inl crInst_hxdisj

theorem crInst_hobig :
    decOutBase 2 1 + 4 + ((CRS.packedSupp crInstE.W 1 crInstY).length + 1) + 1
      < 2 ^ crInstE.W := by
  rw [crInstY_packedSupp_len]
  have h7 : decOutBase 2 1 + 4 + (1 + 1) + 1 = decOutBase 2 1 + 7 := by ring
  rw [h7]
  show decOutBase 2 1 + 7 < 2 ^ cr23Word 2
  exact crInst_room_le 7 (by rw [crInstW]; norm_num)

theorem crInst_hAob :
    decOutBase 2 1 + 2 + (CRS.packedSupp crInstE.W 1 crInstY).length
      ≤ decOutBase 2 1 + 4 := by
  rw [crInstY_packedSupp_len]
  show decOutBase 2 1 + 2 + 1 ≤ decOutBase 2 1 + 4
  omega

theorem crInst_hBob : decOutBase 2 1 + 1 ≤ decOutBase 2 1 + 4 :=
  Nat.add_le_add_left (by norm_num : 1 ≤ 4) _

/-- **The corrected `cr` field, inhabited at the concrete instance.**  This is the `cr` field of
`TopDecRunsIn` at `N = 2`, `t = 1`, `W = cr23Word 2 = 3072`, `M = cr23R 2 1`, `y` the packed sketch
of `x = e_1`, `S = {1}` (the decoded residual), `x̂ = packedSupp y = {0}`, `Lx = [0]`, `bb = xbase =
decOutBase 2 1`, `al = bl = 1`, `ab = bb + 2`, `ob = bb + 4`: 2.3's real 282-instruction decoder,
the five-instruction setup, the 31-instruction repack and the 86-instruction merge run inside the
one fixed programme `progDecOfTop …` from `dCrBase` to `dEnd`, and output `x̂ △ {1}`. -/
theorem crInst_crField (Sinit Srow Sdec Sassem Sres : Stmt) :
    StageRun
      (progDecOfTop Sinit Srow Sdec Sassem Sres
        (CRS.CrStage4 decStmt crInstE.W (decOutBase 2 1) 1 (decOutBase 2 1 + 2)
          (decOutBase 2 1 + 4)))
      crInstE (dCrBase Sinit Srow Sdec Sassem Sres)
      (dEnd Sinit Srow Sdec Sassem Sres
        (CRS.CrStage4 decStmt crInstE.W (decOutBase 2 1) 1 (decOutBase 2 1 + 2)
          (decOutBase 2 1 + 4)))
      (crInstTdec + 5 + ((16 * (crInstE.W * 1) + 17 : ℕ) : ℝ) +
        RMR.mrgCost (CRS.packedSupp crInstE.W 1 crInstY).length 1)
      (CRS.CrStageIn crInstE crInstM crInstYs (decOutBase 2 1 + 2) 1 (decOutBase 2 1) 1
        (decOutBase 2 1 + 4) crInstLx)
      (fun s' => CRS.OutListIs s'
        (symmDiff (CRS.packedSupp crInstE.W 1 crInstY).toFinset ({1} : Finset ℕ))) :=
  CRS.stageRun_crPipeline (Sinit := Sinit) (Srow := Srow) (Sdec := Sdec) (Sassem := Sassem)
    (Sres := Sres) (E := crInstE) (xbase := decOutBase 2 1) (m := 1) (ab := decOutBase 2 1 + 2)
    (bb := decOutBase 2 1) (bl := 1) (ob := decOutBase 2 1 + 4) (y := crInstY)
    (S := ({1} : Finset ℕ)) (xhat := (CRS.packedSupp crInstE.W 1 crInstY).toFinset)
    (Tdec := crInstTdec)
    (Pre := CRS.CrStageIn crInstE crInstM crInstYs (decOutBase 2 1 + 2) 1 (decOutBase 2 1) 1
      (decOutBase 2 1 + 4) crInstLx)
    (crInst_hdecIn Sinit Srow Sdec Sassem Sres) rfl crInst_hW crInst_hWm crInst_hxdisj crInst_hab
    crInst_hbb crInst_hbl crInst_hob crInst_hdisj crInst_hobig crInst_hAob crInst_hBob

#print axioms crInst_mergeData
#print axioms crInst_hdecIn
#print axioms crInst_preInhabited
#print axioms crInst_crField

end LinearSetReconciliation327.Main


open LinearSetReconciliation327.Main in
/-- The round's theorem: the corrected cr field of Theorem 6.5 is inhabited at the concrete
instance N = 2, 	 = 1. -/
theorem solution (Sinit Srow Sdec Sassem Sres : Stmt) :
    StageRun
      (progDecOfTop Sinit Srow Sdec Sassem Sres
        (CRS.CrStage4 decStmt crInstE.W (decOutBase 2 1) 1 (decOutBase 2 1 + 2)
          (decOutBase 2 1 + 4)))
      crInstE (dCrBase Sinit Srow Sdec Sassem Sres)
      (dEnd Sinit Srow Sdec Sassem Sres
        (CRS.CrStage4 decStmt crInstE.W (decOutBase 2 1) 1 (decOutBase 2 1 + 2)
          (decOutBase 2 1 + 4)))
      (crInstTdec + 5 + ((16 * (crInstE.W * 1) + 17 : ℕ) : ℝ) +
        RMR.mrgCost (CRS.packedSupp crInstE.W 1 crInstY).length 1)
      (CRS.CrStageIn crInstE crInstM crInstYs (decOutBase 2 1 + 2) 1 (decOutBase 2 1) 1
        (decOutBase 2 1 + 4) crInstLx)
      (fun s' => CRS.OutListIs s'
        (symmDiff (CRS.packedSupp crInstE.W 1 crInstY).toFinset ({1} : Finset ℕ))) :=
  crInst_crField Sinit Srow Sdec Sassem Sres

#print axioms solution


