-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_CrStageDec20261122
-- name    : LinearSetReconciliation327_Main_CrStageDec20261122
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T07:06:25.101865+00:00
-- url     : https://prove2.me/theorems/3e609789-9d89-44a3-b217-63c40a80c5d6
-- title:
--   The unpack block of Theorem 6.5's CR stage: program, runs, and its list
-- statement:
--   The `cr` stage of Theorem 6.5 must turn the *packed* estimate $\hat x$ left by the prefix assembly into an explicit coordinate list before the merge can read it, and Proposition 2.3's decoder is not that block.  This bundle publishes the unpack block `upkStmt` together with everything about it that is *straight-line*: its three chunks (`upkPre`, 11 instructions; a single scan loop over $p < mW$ whose body `upkBody` is 13 instructions; `upkEpilogue`, 4 instructions), hence `upkStmt.len = 31`; the exact `runBlock` semantics of each chunk and of the loop head; the scan's bit `upkBit` / list `upkList` and the memory it builds `upkMem`, with the read-back lemma `upkMem_read` (the block at $[ab, ab+\#\mathrm{list})$ *is* the list) and the frame `upkMem_frame` (nothing outside it is written); and the semantic content `upkList W xbase s.mem (W\cdot m) = packedSupp W m y`: walking the $m$ words bit by bit really does enumerate the support of the packed payload, the `HoldsVecPad` \u2192 `testBit` \u2192 `decide` chain included.  It also carries the two predicates `UpkIn` and `UpkOut` that the assembled `StageRun` of `Def_LinearSetReconciliation327_Main_CrUnpackRun20261122` is phrased in.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Theorem 6.5's `cr` stage and \u00a72.3.  The program and its three `runBlock` lemmas are the accepted development `Solutions/Sol_proposition_2_3.lean`'s unpack block, copied byte-identically by line span.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CrStage20261122
import Definitions.Def_LinearSetReconciliation327_Main_DecodeClose20261121

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace CRS

/-! ## 10. The unpack program -/

/-- Register convention at entry:
`r0 = bb` (2.3's output base), `r1 = bl` (2.3's output length), `r2 = xbase` (packed estimate word
base), `r3 = W`, `r4 = ab` (list destination base), `r5 = ob` (merge output base), `r6 = m`. -/
def upkPre : List Instr :=
  [iBor r12 r0 r0, iBor r13 r1 r1, iBor r14 r5 r5, iMul r5 r3 r6,
   iImm r8 1, iImm r9 1, iImm r15 1, iImm r6 0, iImm r7 0, iImm r0 0, iImm r1 0]

/-- One bit of the scan: `p → (p / W, p % W) → bit → maybe emit`.  Branchless: the store is
unconditional and the counter is advanced by the bit, so a clear bit leaves only one stale cell
above the list. -/
def upkBody : List Instr :=
  [iDiv r6 r0 r3, iAdd r6 r2 r6, iLd r6 r6, iMod r7 r0 r3, iShr r6 r6 r7,
   iBand r6 r6 r8, iAdd r7 r4 r1, iSt r7 r0, iAdd r1 r1 r6, iImm r9 1, iAdd r0 r0 r9,
   iImm r6 0, iImm r7 0]

/-- The scan test: `p < m·W`. -/
def upkCond : Cond := .lt r15 r0 r5

/-- The epilogue: restore the decoder's output window `(r0, r1) = (bb, bl)`, and set the merge's
first two arguments `r10 := ab`, `r11 := al`. -/
def upkEpilogue : List Instr := [iBor r11 r1 r1, iBor r10 r4 r4, iBor r0 r12 r12, iBor r1 r13 r13]

/-- **The unpack program.** -/
def upkStmt : Stmt :=
  .seq (.code upkPre) (.seq (.loop upkCond (.code upkBody)) (.code upkEpilogue))

theorem upkPre_length : upkPre.length = 11 := rfl
theorem upkBody_length : upkBody.length = 13 := rfl
theorem upkEpilogue_length : upkEpilogue.length = 4 := rfl
theorem upkLoop_len : (Stmt.loop upkCond (.code upkBody)).len = 16 := by
  simp [Stmt.len, upkBody, upkCond, Cond.code]
theorem upkStmt_len : upkStmt.len = 31 := by
  simp [upkStmt, Stmt.len, upkPre, upkBody, upkEpilogue, upkCond, Cond.code]

theorem upkPre_noBranch : NoBranch upkPre := by simp [upkPre, NoBranch, Instr.NoBranchI]
theorem upkBody_noBranch : NoBranch upkBody := by simp [upkBody, NoBranch, Instr.NoBranchI]
theorem upkEpilogue_noBranch : NoBranch upkEpilogue := by
  simp [upkEpilogue, NoBranch, Instr.NoBranchI]

/-! ## 11. The scan's bit, the list of coordinates found so far, and the memory -/

/-- The scan's bit: bit `p % W` of word `p / W` of the packed payload at `xbase`. -/
def upkBit (W xbase : ℕ) (m0 : ℕ → ℕ) (p : ℕ) : ℕ :=
  m0 (xbase + p / W) / 2 ^ (p % W) % 2

/-- The coordinates found in the first `j` bits. -/
def upkList (W xbase : ℕ) (m0 : ℕ → ℕ) (j : ℕ) : List ℕ :=
  (List.range j).filter (fun p => upkBit W xbase m0 p = 1)

/-- The packed payload's support, as an explicit coordinate list. -/
def packedSupp (W m : ℕ) (y : Fin (W * m) → ZMod 2) : List ℕ :=
  (List.range (W * m)).filter
    (fun p => decide (∃ i : Fin (W * m), i.val = p ∧ y i = 1))

/-- The memory after `j` iterations: every visited position was written at the then-current list
end, so the first `#list` cells of the block are the list itself. -/
def upkMem (W xbase : ℕ) (m0 : ℕ → ℕ) (ab j : ℕ) : ℕ → ℕ :=
  (List.range j).foldl
    (fun m p => Function.update m (ab + (upkList W xbase m0 p).length) p) m0

/-- The loop-head state after `j` iterations.  The registers the scan never writes (`r10`, `r11`)
keep their entry values. -/
def upkSt (W : ℕ) (a : ℕ) (s : RAMState) (xbase m ab bb bl ob j : ℕ) : RAMState where
  pc := a
  regs := fun d =>
    if d = r0 then j
    else if d = r1 then (upkList W xbase s.mem j).length
    else if d = r2 then xbase
    else if d = r3 then W
    else if d = r4 then ab
    else if d = r5 then W * m
    else if d = r6 then 0
    else if d = r7 then 0
    else if d = r8 then 1
    else if d = r9 then 1
    else if d = r12 then bb
    else if d = r13 then bl
    else if d = r14 then ob
    else if d = r15 then 1
    else s.regs d
  mem := upkMem W xbase s.mem ab j

/-! ## 12. The bit-extraction arithmetic -/

theorem div_two_pow_mod_two_eq_testBit (n b : ℕ) :
    n / 2 ^ b % 2 = if n.testBit b then 1 else 0 := by
  have hdef : n.testBit b = ((n / 2 ^ b % 2) != 0) := by
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
  rw [hdef]
  have h2 : n / 2 ^ b % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases Nat.eq_zero_or_pos (n / 2 ^ b % 2) with h | h
  · rw [h]; decide
  · have h1 : n / 2 ^ b % 2 = 1 := by omega
    rw [h1]; decide

theorem upkBit_eq_testBit (W xbase : ℕ) (m0 : ℕ → ℕ) (p : ℕ) :
    upkBit W xbase m0 p = if (m0 (xbase + p / W)).testBit (p % W) then 1 else 0 :=
  div_two_pow_mod_two_eq_testBit _ _

/-- A `0/1` number is its own indicator. -/
theorem bit_ite (b : ℕ) (h : b ≤ 1) : (if b = 1 then 1 else 0) = b := by
  rcases Nat.eq_zero_or_pos b with h0 | h0
  · rw [h0]; simp
  · have h1 : b = 1 := by omega
    rw [h1]; simp

theorem upkBit_le_one (W xbase : ℕ) (m0 : ℕ → ℕ) (p : ℕ) : upkBit W xbase m0 p ≤ 1 := by
  unfold upkBit
  have := Nat.mod_lt (m0 (xbase + p / W) / 2 ^ (p % W)) (by norm_num : 0 < 2)
  omega

/-! ## 13. The scan's list and memory -/

theorem upkList_zero (W xbase : ℕ) (m0 : ℕ → ℕ) : upkList W xbase m0 0 = [] := by
  simp [upkList]

theorem upkList_succ (W xbase : ℕ) (m0 : ℕ → ℕ) (j : ℕ) :
    upkList W xbase m0 (j + 1)
      = upkList W xbase m0 j ++ (if upkBit W xbase m0 j = 1 then [j] else []) := by
  by_cases h : upkBit W xbase m0 j = 1 <;>
    simp [upkList, List.range_succ, List.filter_append, h]

theorem upkList_succ_length (W xbase : ℕ) (m0 : ℕ → ℕ) (j : ℕ) :
    (upkList W xbase m0 (j + 1)).length
      = (upkList W xbase m0 j).length + upkBit W xbase m0 j := by
  rw [upkList_succ]
  by_cases hb : upkBit W xbase m0 j = 1
  · rw [if_pos hb]; simp [hb]
  · have h0 : upkBit W xbase m0 j = 0 := by
      have := upkBit_le_one W xbase m0 j; omega
    rw [if_neg hb, h0]; simp

theorem upkList_length_le (W xbase : ℕ) (m0 : ℕ → ℕ) (j : ℕ) :
    (upkList W xbase m0 j).length ≤ j := by
  unfold upkList
  exact le_trans (List.length_filter_le _ _) (by simp)

theorem upkList_nodup (W xbase : ℕ) (m0 : ℕ → ℕ) (j : ℕ) :
    (upkList W xbase m0 j).Nodup := by
  unfold upkList
  exact List.Nodup.filter _ List.nodup_range

theorem upkList_mem (W xbase : ℕ) (m0 : ℕ → ℕ) (j p : ℕ) :
    p ∈ upkList W xbase m0 j ↔ p < j ∧ upkBit W xbase m0 p = 1 := by
  simp [upkList, List.mem_range]

theorem upkMem_zero (W xbase : ℕ) (m0 : ℕ → ℕ) (ab : ℕ) :
    upkMem W xbase m0 ab 0 = m0 := by
  simp [upkMem]

theorem upkMem_succ (W xbase : ℕ) (m0 : ℕ → ℕ) (ab j : ℕ) :
    upkMem W xbase m0 ab (j + 1)
      = Function.update (upkMem W xbase m0 ab j)
          (ab + (upkList W xbase m0 j).length) j := by
  simp [upkMem, List.range_succ, List.foldl_append]

/-- **What the scan has written**: cell `ab + i` holds the `i`-th coordinate. -/
theorem upkMem_read (W xbase : ℕ) (m0 : ℕ → ℕ) (ab : ℕ) (j : ℕ) :
    ∀ i, i < (upkList W xbase m0 j).length →
      upkMem W xbase m0 ab j (ab + i) = (upkList W xbase m0 j).getD i 0 := by
  induction j with
  | zero => intro i hi; simp [upkList] at hi
  | succ j ih =>
      intro i hi
      rw [upkMem_succ, Function.update_apply]
      rw [upkList_succ_length] at hi
      rw [upkList_succ]
      by_cases hb : upkBit W xbase m0 j = 1
      · rw [if_pos hb] at ⊢
        by_cases hlt : i < (upkList W xbase m0 j).length
        · rw [if_neg (by omega), ih i hlt, RMR.getD_append_left hlt]
        · have hge : (upkList W xbase m0 j).length ≤ i := Nat.not_lt.mp hlt
          rw [if_pos (by omega : ab + i = ab + (upkList W xbase m0 j).length)]
          rw [show i = (upkList W xbase m0 j).length from by omega,
            RMR.getD_append_singleton]
      · rw [if_neg hb] at ⊢
        have h0 : upkBit W xbase m0 j = 0 := by
          have := upkBit_le_one W xbase m0 j; omega
        have hi' : i < (upkList W xbase m0 j).length := by
          rw [h0, Nat.add_zero] at hi; exact hi
        rw [if_neg (by omega), ih i hi', RMR.getD_append_left hi']

/-- **The frame**: outside `[ab, ab + #list]` the scan has not written. -/
theorem upkMem_frame (W xbase : ℕ) (m0 : ℕ → ℕ) (ab : ℕ) (j : ℕ) :
    ∀ a, a < ab ∨ ab + (upkList W xbase m0 j).length < a →
      upkMem W xbase m0 ab j a = m0 a := by
  induction j with
  | zero => intro a _; simp [upkMem]
  | succ j ih =>
      intro a ha
      rw [upkMem_succ, Function.update_apply]
      rw [upkList_succ_length] at ha
      rw [if_neg (by omega)]
      exact ih a (by omega)

/-! ## 14. Modular arithmetic helpers for the straight-line blocks -/

theorem add_mod_lt {a b W : ℕ} (h : a + b < 2 ^ W) : (a + b) % 2 ^ W = a + b :=
  Nat.mod_eq_of_lt h

theorem mul_mod_lt {a b W : ℕ} (h : a * b < 2 ^ W) : (a * b) % 2 ^ W = a * b :=
  Nat.mod_eq_of_lt h

theorem or_self_mod {a W : ℕ} (h : a < 2 ^ W) : (a ||| a) % 2 ^ W = a := by
  rw [Nat.or_self, Nat.mod_eq_of_lt h]

theorem band_one_mod {x W : ℕ} (hW : 0 < W) : (x &&& 1) % 2 ^ W = x % 2 := by
  rw [Nat.and_one_is_mod]
  have h2 : 2 ≤ 2 ^ W := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.succ_le_of_lt hW)
    simpa using h
  exact Nat.mod_eq_of_lt (by have := Nat.mod_lt x (by norm_num : 0 < 2); omega)

theorem shr_mod {x off W : ℕ} (hx : x < 2 ^ W) : (x / 2 ^ off) % 2 ^ W = x / 2 ^ off :=
  Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hx)

theorem load_mod {v W : ℕ} (h : v < 2 ^ W) : v % 2 ^ W = v := Nat.mod_eq_of_lt h

theorem le_two_pow_self : ∀ W : ℕ, W ≤ 2 ^ W
  | 0 => by simp
  | n + 1 => by
      have h : n ≤ 2 ^ n := le_two_pow_self n
      rw [pow_succ]
      have h2 : 0 < 2 ^ n := Nat.two_pow_pos n
      omega

/-! ## 15. The prologue run -/

theorem upkPre_run (E : RAMEnv) (k : ℕ) (s : RAMState) (xbase m ab bb bl ob : ℕ)
    (h0 : s.regs 0 = bb) (h1 : s.regs 1 = bl) (h2 : s.regs 2 = xbase) (h3 : s.regs 3 = E.W)
    (h4 : s.regs 4 = ab) (h5 : s.regs 5 = ob) (h6 : s.regs 6 = m)
    (hW : 1 < 2 ^ E.W) (hWm : E.W * m < 2 ^ E.W) (hbb : bb < 2 ^ E.W)
    (hbl : bl < 2 ^ E.W) (hob : ob < 2 ^ E.W) :
    runBlock upkPre E { s with pc := k }
      = { upkSt E.W (k + 11) s xbase m ab bb bl ob 0 with pc := k + 11 } := by
  apply ramState_eq_of
  · rw [runBlock_pc upkPre E _ upkPre_noBranch]
    simp [upkPre_length, upkSt]
  · show (runBlock upkPre E { s with pc := k }).mem = upkMem E.W xbase s.mem ab 0
    rw [upkMem_zero]
    simp only [upkPre, runBlock_cons, runBlock_nil, execInstr, or_self_mod hbb,
      mul_mod_lt hWm, Nat.mod_eq_of_lt hW, Nat.zero_mod]
  · intro d
    fin_cases d <;>
      simp only [upkPre, upkSt, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, Function.update_apply, ne_eq,
        Fin.reduceEq, not_false_eq_true, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        zero_ne_one, one_ne_zero, upkList_zero, List.length_nil, or_self_mod hbb,
        or_self_mod hbl, or_self_mod hob, mul_mod_lt hWm, Nat.mod_eq_of_lt hW,
        Nat.zero_mod, if_true, if_false, ↓reduceIte, h0, h1, h2, h3, h4, h5, h6]

/-! ## 16. The scan body run -/

theorem upkBody_run (E : RAMEnv) (a k : ℕ) (s : RAMState) (xbase m ab bb bl ob j : ℕ)
    (hW : 1 < 2 ^ E.W) (hj : j < E.W * m) (hWm : E.W * m < 2 ^ E.W)
    (hdisj : xbase + m ≤ ab) (hab : ab + E.W * m + 1 < 2 ^ E.W)
    (hword : s.mem (xbase + j / E.W) < 2 ^ E.W) :
    runBlock upkBody E { upkSt E.W a s xbase m ab bb bl ob j with pc := k }
      = { upkSt E.W a s xbase m ab bb bl ob (j + 1) with pc := k + 13 } := by
  have hWpos : 0 < E.W := by
    rcases Nat.eq_zero_or_pos E.W with h | h
    · rw [h] at hW; simp at hW
    · exact h
  have hle : E.W ≤ 2 ^ E.W := le_two_pow_self E.W
  have hjW : j < 2 ^ E.W := lt_trans hj hWm
  have hab2 : ab < 2 ^ E.W :=
    lt_of_le_of_lt (Nat.le_add_right ab (E.W * m))
      (lt_trans (Nat.lt_succ_self (ab + E.W * m)) hab)
  have hxm : xbase + m < 2 ^ E.W := lt_of_le_of_lt hdisj hab2
  have hdivw : j / E.W % 2 ^ E.W = j / E.W :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self j E.W) hjW)
  have hmodw : j % E.W % 2 ^ E.W = j % E.W :=
    Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt j hWpos) hle)
  have hcw : ab + (upkList E.W xbase s.mem j).length < 2 ^ E.W :=
    lt_of_le_of_lt (Nat.add_le_add_left (upkList_length_le E.W xbase s.mem j) ab)
      (lt_trans (Nat.add_lt_add_left hj ab) (lt_trans (Nat.lt_succ_self _) hab))
  have hjw : j / E.W < m := by
    rw [Nat.div_lt_iff_lt_mul hWpos]; rwa [Nat.mul_comm]
  have hxw : xbase + j / E.W < 2 ^ E.W :=
    lt_of_lt_of_le (Nat.add_lt_add_left hjw xbase) (le_of_lt hxm)
  have hj1 : j + 1 < 2 ^ E.W := lt_of_le_of_lt (Nat.succ_le_of_lt hj) hWm
  have hword2 : s.mem (xbase + j / E.W) / 2 ^ (j % E.W) % 2 ≤ 1 := by
    have := Nat.mod_lt (s.mem (xbase + j / E.W) / 2 ^ (j % E.W)) (by norm_num : 0 < 2)
    omega
  have hc1 : (upkList E.W xbase s.mem j).length + 1 < 2 ^ E.W :=
    lt_of_le_of_lt
      (Nat.succ_le_of_lt (lt_of_le_of_lt (upkList_length_le E.W xbase s.mem j) hj)) hWm
  have hcw2 : (upkList E.W xbase s.mem j).length
      + s.mem (xbase + j / E.W) / 2 ^ (j % E.W) % 2 < 2 ^ E.W :=
    lt_of_le_of_lt (Nat.add_le_add_left hword2 _) hc1
  have hread : upkMem E.W xbase s.mem ab j (xbase + j / E.W) = s.mem (xbase + j / E.W) :=
    upkMem_frame E.W xbase s.mem ab j (xbase + j / E.W)
      (Or.inl (lt_of_lt_of_le (Nat.add_lt_add_left hjw xbase) hdisj))
  apply ramState_eq_of
  · rw [runBlock_pc upkBody E _ upkBody_noBranch]
    simp [upkBody_length, upkSt]
  · simp only [upkSt, upkMem_succ, upkBody, runBlock_cons, runBlock_nil, execInstr, hread,
      hdivw, hmodw, Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq,
      not_false_eq_true, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero,
      add_mod_lt hxw, add_mod_lt hcw, Nat.mod_eq_of_lt hW, mul_mod_lt hWm,
      band_one_mod hWpos, shr_mod hword, load_mod hword, Nat.mod_eq_of_lt hj1,
      Nat.zero_mod, if_true, if_false, ↓reduceIte]
  · intro d
    fin_cases d <;>
      simp only [upkSt, upkBit, upkBody, runBlock_cons, runBlock_nil, execInstr, hread,
        hdivw, hmodw, Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq,
        not_false_eq_true, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero,
        add_mod_lt hxw, add_mod_lt hcw, add_mod_lt hc1, add_mod_lt hcw2, Nat.mod_eq_of_lt hW,
        mul_mod_lt hWm, band_one_mod hWpos, shr_mod hword, load_mod hword,
        Nat.mod_eq_of_lt hj1, Nat.zero_mod, if_true, if_false, ↓reduceIte,
        upkList_succ_length]

/-! ## 19b. The scan test's state -/

/-- The state after the scan test has fired at `p = j`: the loop head itself, since `r15` holds `1`
both before and after (the test is true for every `j < m·W`). -/
theorem upkHead_eq (E : RAMEnv) (A j : ℕ) (s : RAMState) (xbase m ab bb bl ob : ℕ)
    (hW : 1 < 2 ^ E.W) (hj : j < E.W * m) :
    { (runBlock upkCond.code E (upkSt E.W A s xbase m ab bb bl ob j)) with pc := A + 2 }
      = { upkSt E.W A s xbase m ab bb bl ob j with pc := A + 2 } := by
  have hmod : (if j < E.W * m then (1 : ℕ) else 0) % 2 ^ E.W = 1 := by
    rw [if_pos hj, Nat.mod_eq_of_lt hW]
  apply ramState_eq_of
  · rfl
  · simp [upkCond, Cond.code, runBlock_cons, runBlock_nil, execInstr]
  · intro d
    fin_cases d <;>
      simp only [upkCond, Cond.code, upkSt, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero, hmod,
        Nat.zero_mod, if_true, if_false, ↓reduceIte]

/-! ## 17. The epilogue run -/

theorem upkEpilogue_run (E : RAMEnv) (k : ℕ) (s0 : RAMState)
    (h1 : s0.regs 1 < 2 ^ E.W) (h4 : s0.regs 4 < 2 ^ E.W)
    (h12 : s0.regs r12 < 2 ^ E.W) (h13 : s0.regs r13 < 2 ^ E.W) :
    runBlock upkEpilogue E { s0 with pc := k }
      = ⟨k + 4,
          (fun d =>
            (if d = r0 then s0.regs r12 else if d = r1 then s0.regs r13
            else if d = r10 then s0.regs r4 else if d = r11 then s0.regs 1
            else s0.regs d)), s0.mem⟩ := by
  apply ramState_eq_of
  · rw [runBlock_pc upkEpilogue E _ upkEpilogue_noBranch]
    simp [upkEpilogue_length]
  · simp only [upkEpilogue, runBlock_cons, runBlock_nil, execInstr]
  · intro d
    fin_cases d <;>
      simp only [upkEpilogue, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero,
        or_self_mod h1, or_self_mod h4, or_self_mod h12, or_self_mod h13,
        if_true, if_false, ↓reduceIte]

/-! ## 18. The unpack predicates -/

/-- The unpack program's entry predicate. -/
def UpkIn (E : RAMEnv) (xbase m ab bb bl ob : ℕ) (y : Fin (E.W * m) → ZMod 2) :
    RAMState → Prop :=
  fun s => s.regs 0 = bb ∧ s.regs 1 = bl ∧ s.regs 2 = xbase ∧ s.regs 3 = E.W ∧
    s.regs 4 = ab ∧ s.regs 5 = ob ∧ s.regs 6 = m ∧ C8R.HoldsVecPad E.W m xbase s y

/-- The unpack program's exit predicate. -/
def UpkOut (W m : ℕ) (xbase ab bb bl ob : ℕ) (y : Fin (W * m) → ZMod 2) :
    RAMState → Prop :=
  fun s' => s'.regs 0 = bb ∧ s'.regs 1 = bl ∧ s'.regs r10 = ab ∧
    s'.regs r11 = (packedSupp W m y).length ∧ s'.regs r12 = bb ∧ s'.regs r13 = bl ∧
    s'.regs r14 = ob ∧ C8R.HoldsVecPad W m xbase s' y ∧
    RMR.mList s'.mem ab (packedSupp W m y).length = packedSupp W m y

/-! ## 19. The main equivalence: the scan's list is the packed support -/

theorem upkBit_eq_decide {W m xbase : ℕ} (hW : 1 < W) {y : Fin (W * m) → ZMod 2}
    {s : RAMState} (hpad : C8R.HoldsVecPad W m xbase s y) {p : ℕ} (hp : p < W * m) :
    upkBit W xbase s.mem p
      = if decide (∃ i : Fin (W * m), i.val = p ∧ y i = 1) then 1 else 0 := by
  have hWpos : 0 < W := by omega
  have hpw : p / W < m := by
    rw [Nat.div_lt_iff_lt_mul hWpos]; rwa [Nat.mul_comm]
  have hmemp : s.mem (xbase + p / W) = packMem W y (p / W) := by
    have hm := hpad
    unfold C8R.HoldsVecPad at hm
    rw [C8R.asm_words_eq_padded W m hWpos] at hm
    exact hm (p / W) hpw
  show s.mem (xbase + p / W) / 2 ^ (p % W) % 2 = _
  rw [hmemp]
  rw [div_two_pow_mod_two_eq_testBit]
  rw [C8R.RP.testBit_packMem W hWpos y (p / W) (p % W) (Nat.mod_lt p hWpos)]
  rw [show p / W * W + p % W = p from by rw [Nat.mul_comm]; exact Nat.div_add_mod p W]

theorem upkList_eq_packedSupp {W m xbase : ℕ} (hW : 1 < W) {y : Fin (W * m) → ZMod 2}
    {s : RAMState} (hpad : C8R.HoldsVecPad W m xbase s y) :
    upkList W xbase s.mem (W * m) = packedSupp W m y := by
  unfold upkList packedSupp
  refine List.filter_congr ?_
  intro p hp
  have hp' : p < W * m := List.mem_range.mp hp
  rw [upkBit_eq_decide hW hpad hp']
  by_cases h : ∃ i : Fin (W * m), i.val = p ∧ y i = 1
  · simp [h]
  · simp [h]

theorem map_getD_range_self (l : List ℕ) :
    (List.range l.length).map (fun i => l.getD i 0) = l := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem l 0 h2]

end CRS
end LinearSetReconciliation327.Main


