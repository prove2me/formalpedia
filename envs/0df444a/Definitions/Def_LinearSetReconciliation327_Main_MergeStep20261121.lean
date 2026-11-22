-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_MergeStep20261121
-- name    : LinearSetReconciliation327_Main_MergeStep20261121
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T04:07:02.316484+00:00
-- url     : https://prove2.me/theorems/5b4de2bd-ca7e-407c-8c76-ff8d12c0bc85
-- title:
--   The repaired merge of Theorem 6.5's CR stage: mrgStep_sem, the end-to-end contract, its new loop rule, and two non-vacuous runs
-- statement:
--   The merge that Theorem 6.5's CR stage runs between 2.3's decoder and the output: given two blocks of $W$-bit words, $A$ at base `ab` of length `al` and $B$ at base `bb` of length `bl`, it writes the symmetric difference $A\setminus B$ followed by $B\setminus A$ into the output block at base `ob`, using one membership scan per candidate and a genuine register swap between two passes of the *same* pass code. The bundle contains the corrected 86-instruction program `mrgStmtFull` (head, pass, swap, pass, header) together with its exact address decomposition, the two-pass simulation `mrgPass_sem` over a new upper-bounded loop rule `Sem.loopLe` (whose cost is $2+xl(18+14yl)$), the inner-scan invariant `mrgFnd` ($r_3=1$ iff $\exists q<$ cursor, $B[q]=A[j]$), the last-write-wins memory model `mrgMem` and its read/frame lemmas, and the composition `mrgStep_sem`: from any entry state with `r10..r14 = (ab, al, bb, bl, ob)` and the six word bounds and the two two-sided disjointness hypotheses, the machine reaches `base + 86` in at most `mrgCost al bl` steps and the output list is exactly `mrgKept A B.toFinset al ++ mrgKept B A.toFinset bl`.  The contract `SmergeRunsM` is proved (`smergeRunsM_of_at`) and is *inhabited non-vacuously*: two concrete runs at width 8 show `A=[5], B=[7] => [5,7]` and `A=[5], B=[5,7] => [7]` (the symmetric difference, not the union).  The `StageRun` form `mergeStageRun` states the postcondition as `(outList s').toFinset = A △ B`, which is the shape 6.5's `cr` stage needs for `x̂ △ ê = x`.
-- source:
--   Theorem 6.5's CR stage of arXiv:2611.11409 (Liu--Xu--Yang--Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), $2.3's decoder plus the final merge; the loop rule `Sem.loopLe` extends `Sem.loop` of Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas, and `StageRun` is Definitions.Def_LinearSetReconciliation327_Main_Top65Dec.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_DecodeGaps20261121
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
import Definitions.Def_LinearSetReconciliation327_Main_RowScratch20261121
import Definitions.Def_LinearSetReconciliation327_Main_RowDecode20261121
import Definitions.Def_LinearSetReconciliation327_Main_Top65Dec

/-!
# `_mrg_repair` — the merge, rewritten; the repack head, repaired
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Finset

noncomputable section

namespace LinearSetReconciliation327.Main
namespace RMR

open Classical RDG

/-! ## 1. Lists stored in memory, and the two combinatorial kernels -/

def mList (m : ℕ → ℕ) (b len : ℕ) : List ℕ := (List.range len).map (fun i => m (b + i))

theorem mList_length (m : ℕ → ℕ) (b len : ℕ) : (mList m b len).length = len := by
  simp [mList]

theorem mList_getD (m : ℕ → ℕ) (b len p : ℕ) (hp : p < len) :
    (mList m b len).getD p 0 = m (b + p) := by
  unfold mList
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp]
  rfl

theorem mList_mem (m : ℕ → ℕ) (b len v : ℕ) :
    v ∈ mList m b len ↔ ∃ p, p < len ∧ m (b + p) = v := by
  unfold mList
  rw [List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, List.mem_range.mp hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, List.mem_range.mpr hp, rfl⟩

theorem listAt_eq_mList (s : RAMState) (b len : ℕ) : listAt s b len = mList s.mem b len := rfl

theorem take_succ_getD (xs : List ℕ) (j : ℕ) (hj : j < xs.length) :
    xs.take (j + 1) = xs.take j ++ [xs.getD j 0] := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons x tl ih =>
      cases j with
      | zero => rfl
      | succ k =>
          rw [List.take_succ_cons, ih k (by simpa using hj)]
          simp only [List.getD, List.getElem?_cons_succ]
          rfl

/-- The kept elements among the first `j` of the candidate list: skip the members of `ys`. -/
def mrgKept (xs : List ℕ) (ys : Finset ℕ) (j : ℕ) : List ℕ :=
  (xs.take j).filter (fun v => v ∉ ys)

theorem filter_singleton_notMem (ys : Finset ℕ) (v : ℕ) :
    ([v].filter (fun x => x ∉ ys)) = (if v ∈ ys then [] else [v]) := by
  by_cases h : v ∈ ys <;> simp [List.filter_cons, h]

theorem mrgKept_zero (xs : List ℕ) (ys : Finset ℕ) : mrgKept xs ys 0 = [] := by
  simp [mrgKept]

theorem mrgKept_succ {xs : List ℕ} {ys : Finset ℕ} {j : ℕ} (hj : j < xs.length) :
    mrgKept xs ys (j + 1)
      = mrgKept xs ys j ++ (if xs.getD j 0 ∈ ys then [] else [xs.getD j 0]) := by
  unfold mrgKept
  rw [take_succ_getD xs j hj, List.filter_append, filter_singleton_notMem]

theorem mrgKept_eq_filter (xs : List ℕ) (ys : Finset ℕ) (j : ℕ) :
    mrgKept xs ys j = (xs.take j).filter (fun v => v ∉ ys) := rfl

theorem mem_mrgKept {xs : List ℕ} {ys : Finset ℕ} {j : ℕ} (v : ℕ) :
    v ∈ mrgKept xs ys j ↔ v ∈ xs.take j ∧ v ∉ ys := by
  unfold mrgKept
  simp [List.mem_filter]

theorem nodup_take : ∀ (xs : List ℕ) (j : ℕ), xs.Nodup → (xs.take j).Nodup
  | [], j, _ => by simp
  | _ :: _, 0, _ => by simp
  | x :: tl, (k + 1), h => by
      rw [List.take_succ_cons]
      refine List.nodup_cons.mpr ⟨?_, nodup_take tl k (List.nodup_cons.mp h).2⟩
      intro hx
      exact (List.nodup_cons.mp h).1 (List.mem_of_mem_take hx)

theorem mrgKept_nodup {xs : List ℕ} (h : xs.Nodup) (ys : Finset ℕ) (j : ℕ) :
    (mrgKept xs ys j).Nodup := by
  unfold mrgKept
  exact List.Nodup.filter _ (nodup_take xs j h)

theorem mrgKept_toFinset (xs : List ℕ) (ys : Finset ℕ) :
    (mrgKept xs ys xs.length).toFinset = xs.toFinset \ ys := by
  ext v
  rw [List.mem_toFinset, mem_mrgKept, List.take_length, Finset.mem_sdiff, List.mem_toFinset]

/-- **The inner scan's flag**: `1` iff some scanned word `q' < q` equals `v`. -/
def mrgFnd (m : ℕ → ℕ) (b v q : ℕ) : ℕ := if ∃ q' < q, m (b + q') = v then 1 else 0

theorem mrgFnd_zero (m : ℕ → ℕ) (b v : ℕ) : mrgFnd m b v 0 = 0 := by
  simp [mrgFnd]

theorem mrgFnd_le_one (m : ℕ → ℕ) (b v q : ℕ) : mrgFnd m b v q ≤ 1 := by
  unfold mrgFnd
  split <;> omega

theorem mrgFnd_succ (m : ℕ → ℕ) (b v q : ℕ) :
    mrgFnd m b v (q + 1) = if m (b + q) = v then 1 else mrgFnd m b v q := by
  unfold mrgFnd
  by_cases h : m (b + q) = v
  · rw [if_pos ⟨q, by omega, h⟩, if_pos h]
  · rw [if_neg h]
    by_cases h' : ∃ q', q' < q ∧ m (b + q') = v
    · rw [if_pos ⟨h'.choose, by omega, h'.choose_spec.2⟩, if_pos h']
    · rw [if_neg h']
      rw [if_neg]
      rintro ⟨q', hq, he⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hlt | heq
      · exact h' ⟨q', hlt, he⟩
      · exact h (heq ▸ he)

theorem mrgFnd_one_iff (m : ℕ → ℕ) (b v q : ℕ) :
    mrgFnd m b v q = 1 ↔ v ∈ (mList m b q).toFinset := by
  rw [List.mem_toFinset, mList_mem]
  unfold mrgFnd
  by_cases h : ∃ q', q' < q ∧ m (b + q') = v
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun h1 => absurd h1 (by omega), fun h2 => absurd h2 h⟩

/-- The memory after `j` outer iterations, built exactly as the machine builds it. -/
def mrgMem (m : ℕ → ℕ) (ob c0 : ℕ) (xs : List ℕ) (ys : Finset ℕ) : ℕ → ℕ → ℕ
  | 0 => m
  | (j + 1) =>
    Function.update (mrgMem m ob c0 xs ys j) (ob + (c0 + (mrgKept xs ys j).length))
      (xs.getD j 0)

theorem getD_append_left {pre l : List ℕ} {i : ℕ} (h : i < pre.length) :
    (pre ++ l).getD i 0 = pre.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right (pre l : List ℕ) (k : ℕ) :
    (pre ++ l).getD (pre.length + k) 0 = l.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem getD_append_singleton (l : List ℕ) (v : ℕ) : (l ++ [v]).getD l.length 0 = v := by
  have h := getD_append_right l [v] 0
  simpa using h

/-- **The invariant of the output block.** -/
theorem mrgMem_get (m : ℕ → ℕ) (ob c0 : ℕ) (xs : List ℕ) (ys : Finset ℕ) (pre : List ℕ)
    (hpre : pre.length = c0)
    (hm : ∀ i, i < c0 → m (ob + i) = pre.getD i 0) :
    ∀ j, j ≤ xs.length → ∀ i, i < c0 + (mrgKept xs ys j).length →
      mrgMem m ob c0 xs ys j (ob + i) = (pre ++ mrgKept xs ys j).getD i 0
  | 0, _, i, hi => by
      have hk : (mrgKept xs ys 0).length = 0 := by rw [mrgKept_zero]; rfl
      have hi' : i < c0 := by rw [hk] at hi; omega
      show m (ob + i) = (pre ++ ([] : List ℕ)).getD i 0
      rw [hm i hi']
      simp
  | (j + 1), hj, i, hi => by
      have hj' : j < xs.length := by omega
      have hPlen : (pre ++ mrgKept xs ys j).length = c0 + (mrgKept xs ys j).length := by
        rw [List.length_append, hpre]
      show Function.update (mrgMem m ob c0 xs ys j) (ob + (c0 + (mrgKept xs ys j).length))
          (xs.getD j 0) (ob + i) = (pre ++ mrgKept xs ys (j + 1)).getD i 0
      have hkey : pre ++ mrgKept xs ys (j + 1)
          = (pre ++ mrgKept xs ys j) ++ (if xs.getD j 0 ∈ ys then [] else [xs.getD j 0]) := by
        rw [mrgKept_succ hj', List.append_assoc]
      by_cases hin : xs.getD j 0 ∈ ys
      · have hlen : c0 + (mrgKept xs ys (j + 1)).length = c0 + (mrgKept xs ys j).length := by
          rw [mrgKept_succ hj', if_pos hin, List.append_nil]
        rw [hlen] at hi
        rw [hkey, if_pos hin, List.append_nil,
          Function.update_of_ne (by omega : ob + i ≠ ob + (c0 + (mrgKept xs ys j).length))]
        exact mrgMem_get m ob c0 xs ys pre hpre hm j (by omega) i hi
      · have hlen : c0 + (mrgKept xs ys (j + 1)).length
            = c0 + (mrgKept xs ys j).length + 1 := by
          rw [mrgKept_succ hj', if_neg hin, List.length_append, List.length_singleton]
          omega
        rw [hlen] at hi
        rcases Nat.lt_or_ge i (c0 + (mrgKept xs ys j).length) with hlt | hge
        · rw [hkey, if_neg hin, getD_append_left (by rw [hPlen]; omega),
            Function.update_of_ne (by omega : ob + i ≠ ob + (c0 + (mrgKept xs ys j).length))]
          exact mrgMem_get m ob c0 xs ys pre hpre hm j (by omega) i hlt
        · have hie : i = c0 + (mrgKept xs ys j).length := by omega
          rw [hie, hkey, if_neg hin, Function.update_self, ← hPlen, getD_append_singleton]

/-! ## 2. The repaired program -/

/-- The merge head. -/
def mrgHead : List Instr :=
  [iBor r5 r10 r10, iBor r6 r11 r11, iBor r7 r12 r12, iBor r8 r13 r13, iBor r9 r14 r14,
   iImm r0 0, iImm r1 0,
   iImm r10 0, iImm r11 0, iImm r12 0, iImm r13 0, iImm r14 0, iImm r15 0,
   iImm r2 0, iImm r3 0, iImm r4 1]

theorem mrgHead_length : mrgHead.length = 16 := rfl

theorem mrgHead_noBranch : NoBranch mrgHead := by
  simp [mrgHead, NoBranch, Instr.NoBranchI]

/-- The inner membership scan's body. -/
def mrgScanBody : List Instr :=
  [iAdd r15 r7 r2, iLd r13 r15,
   iAdd r15 r5 r0, iLd r14 r15,
   iSub r14 r13 r14,
   iLt r15 r14 r4,
   iBor r3 r3 r15,
   iAdd r2 r2 r4,
   iImm r13 0, iImm r14 0, iImm r15 1]

theorem mrgScanBody_length : mrgScanBody.length = 11 := rfl

/-- The inner scan. -/
def mrgScanStmt : Stmt := .loop (.lt r15 r2 r8) (.code mrgScanBody)

theorem mrgScanStmt_len : mrgScanStmt.len = 14 := by
  simp [mrgScanStmt, Stmt.len, mrgScanBody, Cond.code]

/-- The branchless keep. -/
def mrgKeep : List Instr :=
  [iAdd r15 r5 r0, iLd r4 r15,
   iAdd r15 r9 r1, iSt r15 r4,
   iImm r15 1, iSub r15 r15 r3,
   iAdd r1 r1 r15,
   iImm r4 1, iAdd r0 r0 r4]

theorem mrgKeep_length : mrgKeep.length = 9 := rfl

/-- Restore the scratch bank. -/
def mrgCleanup : List Instr := [iImm r2 0, iImm r3 0, iImm r4 1, iImm r15 0]

theorem mrgCleanup_length : mrgCleanup.length = 4 := rfl

/-- One outer iteration. -/
def mrgBody : Stmt := .seq mrgScanStmt (.seq (.code mrgKeep) (.code mrgCleanup))

theorem mrgBody_len : mrgBody.len = 27 := by
  simp [mrgBody, Stmt.len, mrgScanStmt_len, mrgKeep, mrgCleanup]

/-- One pass. -/
def mrgPass : Stmt := .loop (.lt r15 r0 r6) mrgBody

theorem mrgPass_len : mrgPass.len = 30 := by
  simp [mrgPass, Stmt.len, mrgBody_len, Cond.code]

/-- **The real swap**, with the temporaries `r10`, `r11`, and `r0 := 0`. -/
def mrgSwap : List Instr :=
  [iBor r10 r5 r5, iBor r11 r6 r6,
   iBor r5 r7 r7, iBor r6 r8 r8,
   iBor r7 r10 r10, iBor r8 r11 r11,
   iImm r0 0, iImm r10 0, iImm r11 0]

theorem mrgSwap_length : mrgSwap.length = 9 := rfl

/-- **The repaired merge**. -/
def mrgStmtFull : Stmt :=
  .seq (.code mrgHead)
    (.seq mrgPass (.seq (.code mrgSwap) (.seq mrgPass (.code [iBor r0 r9 r9]))))

theorem mrgStmtFull_len : mrgStmtFull.len = 86 := by
  simp [mrgStmtFull, Stmt.len, mrgHead_length, mrgPass_len, mrgSwap_length]

/-- The compiled shape of the repaired merge. -/
theorem mrgStmtFull_shape (base : ℕ) :
    mrgStmtFull.compile base
      = mrgHead ++ (mrgPass.compile (base + 16)
          ++ (mrgSwap ++ (mrgPass.compile (base + 16 + 30 + 9) ++ [iBor r0 r9 r9]))) := by
  simp [mrgStmtFull, Stmt.compile, Stmt.len, mrgHead_length, mrgPass_len, mrgSwap_length]

/-- The canonical state of the merge. -/
def mrgSt (a : ℕ) (m : ℕ → ℕ) (xb xl yb yl ob : ℕ) (j c q found v15 : ℕ) : RAMState where
  pc := a
  mem := m
  regs := fun d =>
    if d = r0 then j else if d = r1 then c else if d = r2 then q else
      if d = r3 then found else if d = r4 then 1 else if d = r5 then xb else
        if d = r6 then xl else if d = r7 then yb else if d = r8 then yl else
          if d = r9 then ob else if d = r15 then v15 else 0

theorem mrgSt_pc (a m xb xl yb yl ob j c q found v15) :
    (mrgSt a m xb xl yb yl ob j c q found v15).pc = a := rfl

theorem mrgSt_mem (a m xb xl yb yl ob j c q found v15) :
    (mrgSt a m xb xl yb yl ob j c q found v15).mem = m := rfl

theorem mrgSt_r0 (a m xb xl yb yl ob j c q found v15) :
    (mrgSt a m xb xl yb yl ob j c q found v15).regs r0 = j := by simp [mrgSt]

theorem mrgSt_r1 (a m xb xl yb yl ob j c q found v15) :
    (mrgSt a m xb xl yb yl ob j c q found v15).regs r1 = c := by simp [mrgSt]

theorem mrgSt_r2 (a m xb xl yb yl ob j c q found v15) :
    (mrgSt a m xb xl yb yl ob j c q found v15).regs r2 = q := by simp [mrgSt]

theorem mrgSt_r3 (a m xb xl yb yl ob j c q found v15) :
    (mrgSt a m xb xl yb yl ob j c q found v15).regs r3 = found := by simp [mrgSt]

theorem mrgSt_r4 (a m xb xl yb yl ob j c q found v15) :
    (mrgSt a m xb xl yb yl ob j c q found v15).regs r4 = 1 := by simp [mrgSt]

theorem mrgSt_r5 (a m xb xl yb yl ob j c q found v15) :
    (mrgSt a m xb xl yb yl ob j c q found v15).regs r5 = xb := by simp [mrgSt]

theorem mrgSt_r6 (a m xb xl yb yl ob j c q found v15) :
    (mrgSt a m xb xl yb yl ob j c q found v15).regs r6 = xl := by simp [mrgSt]

theorem mrgSt_r7 (a m xb xl yb yl ob j c q found v15) :
    (mrgSt a m xb xl yb yl ob j c q found v15).regs r7 = yb := by simp [mrgSt]

theorem mrgSt_r8 (a m xb xl yb yl ob j c q found v15) :
    (mrgSt a m xb xl yb yl ob j c q found v15).regs r8 = yl := by simp [mrgSt]

theorem mrgSt_r9 (a m xb xl yb yl ob j c q found v15) :
    (mrgSt a m xb xl yb yl ob j c q found v15).regs r9 = ob := by simp [mrgSt]

theorem mrgSt_r15 (a m xb xl yb yl ob j c q found v15) :
    (mrgSt a m xb xl yb yl ob j c q found v15).regs r15 = v15 := by simp [mrgSt]

/-! ## 3. Arithmetic facts of the two bodies -/

/-- `(p + 2^W - q) % 2^W = 0 ↔ p = q` for two words. -/
theorem sub_mod_eq_zero {p q W : ℕ} (hp : p < 2 ^ W) (hq : q < 2 ^ W) :
    (p + 2 ^ W - q) % 2 ^ W = 0 ↔ p = q := by
  rcases Nat.lt_or_ge p q with h | h
  · have hlt : p + 2 ^ W - q < 2 ^ W := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega
  · rw [show p + 2 ^ W - q = (p - q) + 2 ^ W from by omega, Nat.add_mod_right]
    have hlt : p - q < 2 ^ W := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

/-- The keep body's count update: `count += 1 - found`, exactly. -/
theorem keep_count {W c found : ℕ} (hW : 1 < 2 ^ W) (hc : c + 1 < 2 ^ W) (hf : found ≤ 1) :
    (c + ((1 + 2 ^ W - found) % 2 ^ W)) % 2 ^ W = c + 1 - found := by
  have hmod0 : (1 + 2 ^ W) % 2 ^ W = 1 := by
    rw [show 1 + 2 ^ W = 2 ^ W + 1 from by omega, Nat.add_mod, Nat.mod_self, Nat.zero_add,
      Nat.mod_mod, Nat.mod_eq_of_lt hW]
  rcases Nat.eq_zero_or_pos found with h | h
  · subst h
    rw [show 1 + 2 ^ W - 0 = 1 + 2 ^ W from by omega, hmod0,
      show c + 1 - 0 = c + 1 from by omega, Nat.mod_eq_of_lt hc]
  · have hf1 : found = 1 := by omega
    subst hf1
    rw [show 1 + 2 ^ W - 1 = 2 ^ W from by omega, Nat.mod_self, Nat.add_zero,
      Nat.mod_eq_of_lt (by omega : c < 2 ^ W)]
    omega

/-- The scan body's flag update: `found |= (B[q] == v)`, exactly `mrgFnd (q+1)`. -/
theorem scan_flag (W : ℕ) (m : ℕ → ℕ) (b v q : ℕ) (hW : 1 < 2 ^ W) :
    (mrgFnd m b v q ||| ((if m (b + q) = v then 1 else 0) % 2 ^ W)) % 2 ^ W
      = mrgFnd m b v (q + 1) := by
  have hib : ((if m (b + q) = v then 1 else 0) % 2 ^ W)
      = (if m (b + q) = v then 1 else 0) := by
    by_cases h : m (b + q) = v <;> simp [h, Nat.mod_eq_of_lt hW]
  rw [hib, mrgFnd_succ]
  by_cases he : m (b + q) = v
  · rw [if_pos he, if_pos he]
    obtain h0 | h1 : mrgFnd m b v q = 0 ∨ mrgFnd m b v q = 1 := by
      have := mrgFnd_le_one m b v q; omega
    · rw [h0]; simp [Nat.mod_eq_of_lt hW]
    · rw [h1]; simp [Nat.mod_eq_of_lt hW]
  · rw [if_neg he, if_neg he, Nat.or_zero]
    exact Nat.mod_eq_of_lt (by have := mrgFnd_le_one m b v q; omega)

/-- The scan body's equality test: `(p - q) % 2^W < 1` is the equality bit. -/
theorem scan_eq_bit (W : ℕ) (p q : ℕ) (hp : p < 2 ^ W) (hq : q < 2 ^ W) :
    (if (p + 2 ^ W - q) % 2 ^ W < 1 then 1 else 0) = (if p = q then 1 else 0) := by
  have h : ((p + 2 ^ W - q) % 2 ^ W < 1) ↔ p = q := by
    rw [Nat.lt_one_iff, sub_mod_eq_zero hp hq]
  by_cases hp' : p = q
  · rw [if_pos (h.mpr hp'), if_pos hp']
  · rw [if_neg (fun hc => hp' (h.mp hc)), if_neg hp']

/-! ## 4. The four straight-line blocks, proved -/

theorem mrgHead_run (E : RAMEnv) (pc ab al bb bl ob : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ)
    (hW : 1 < 2 ^ E.W)
    (hab : r r10 = ab) (hal : r r11 = al) (hbb : r r12 = bb) (hbl : r r13 = bl)
    (hob : r r14 = ob)
    (habw : ab < 2 ^ E.W) (halw : al < 2 ^ E.W) (hbbw : bb < 2 ^ E.W)
    (hblw : bl < 2 ^ E.W) (hobw : ob < 2 ^ E.W) :
    runBlock mrgHead E ⟨pc, r, m⟩ = mrgSt (pc + 16) m ab al bb bl ob 0 0 0 0 0 := by
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  apply ramState_eq_of
  · simp only [mrgHead, mrgSt, runBlock_cons, runBlock_nil, execInstr] <;> omega
  · simp only [mrgHead, mrgSt, runBlock_cons, runBlock_nil, execInstr, Function.update_self,
      Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, zero_ne_one, one_ne_zero, Nat.zero_mod, Nat.mod_self, h1]
  · intro d
    fin_cases d <;>
      simp only [mrgHead, mrgSt, Fin.isValue, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero, Nat.zero_mod,
        Nat.or_self, Nat.mod_eq_of_lt habw, Nat.mod_eq_of_lt halw, Nat.mod_eq_of_lt hbbw,
        Nat.mod_eq_of_lt hblw, Nat.mod_eq_of_lt hobw, h1, hab, hal, hbb, hbl, hob, ↓reduceIte]

theorem mrgSwap_run (E : RAMEnv) (pc xb xl yb yl ob j c : ℕ) (m : ℕ → ℕ)
    (hW : 1 < 2 ^ E.W)
    (hxb : xb < 2 ^ E.W) (hxl : xl < 2 ^ E.W) (hyb : yb < 2 ^ E.W) (hyl : yl < 2 ^ E.W)
    (hob : ob < 2 ^ E.W) (hj : j < 2 ^ E.W) (hc : c < 2 ^ E.W) :
    runBlock mrgSwap E (mrgSt pc m xb xl yb yl ob j c 0 0 0) =
      mrgSt (pc + 9) m yb yl xb xl ob 0 c 0 0 0 := by
  apply ramState_eq_of
  · simp only [mrgSwap, mrgSt, runBlock_cons, runBlock_nil, execInstr] <;> omega
  · simp only [mrgSwap, mrgSt, runBlock_cons, runBlock_nil, execInstr, Function.update_self,
      Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, zero_ne_one, one_ne_zero, Nat.zero_mod, Nat.mod_self]
  · intro d
    fin_cases d <;>
      simp only [mrgSwap, mrgSt, Fin.isValue, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero, Nat.zero_mod,
        Nat.or_self, Nat.mod_eq_of_lt hxb, Nat.mod_eq_of_lt hxl, Nat.mod_eq_of_lt hyb,
        Nat.mod_eq_of_lt hyl, Nat.mod_eq_of_lt hob, Nat.mod_eq_of_lt (by omega : (0:ℕ) < 2 ^ E.W),
        ↓reduceIte]

theorem mrgKeep_run (E : RAMEnv) (pc xb xl yb yl ob j c q found : ℕ) (m : ℕ → ℕ)
    (hW : 1 < 2 ^ E.W) (hfound : found ≤ 1)
    (hxj : xb + j < 2 ^ E.W) (hoc : ob + c < 2 ^ E.W) (hc1 : c + 1 < 2 ^ E.W)
    (hj1 : j + 1 < 2 ^ E.W) (hv : m (xb + j) < 2 ^ E.W) :
    runBlock (mrgKeep ++ mrgCleanup) E (mrgSt pc m xb xl yb yl ob j c q found 0) =
      mrgSt (pc + 13) (Function.update m (ob + c) (m (xb + j))) xb xl yb yl ob (j + 1)
        (c + 1 - found) 0 0 0 := by
  have hcnt := keep_count (W := E.W) hW hc1 hfound
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  apply ramState_eq_of
  · simp only [mrgKeep, mrgCleanup, mrgSt, runBlock_append, runBlock_cons, runBlock_nil,
      execInstr] <;> omega
  · simp only [mrgKeep, mrgCleanup, mrgSt, runBlock_append, runBlock_cons, runBlock_nil,
      execInstr, Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq,
      not_false_eq_true, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero,
      Nat.zero_mod, Nat.mod_self, h1, Nat.mod_eq_of_lt hxj, Nat.mod_eq_of_lt hoc,
      Nat.mod_eq_of_lt hv, hv, ↓reduceIte]
  · intro d
    fin_cases d <;>
      simp only [mrgKeep, mrgCleanup, mrgSt, Fin.isValue, runBlock_append, runBlock_cons,
        runBlock_nil, execInstr, Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq,
        not_false_eq_true, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero,
        Nat.zero_mod, Nat.or_self, h1, Nat.mod_eq_of_lt hxj, Nat.mod_eq_of_lt hoc,
        Nat.mod_eq_of_lt hv, hv, Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hj1, hcnt, ↓reduceIte]

theorem mrgScanBody_run (E : RAMEnv) (pc xb xl yb yl ob j c q : ℕ) (m : ℕ → ℕ)
    (hW : 1 < 2 ^ E.W) (hxj : xb + j < 2 ^ E.W) (hyq : yb + q < 2 ^ E.W)
    (hq1 : q + 1 < 2 ^ E.W) (hvx : m (xb + j) < 2 ^ E.W) (hby : m (yb + q) < 2 ^ E.W) :
    runBlock mrgScanBody E (mrgSt pc m xb xl yb yl ob j c q (mrgFnd m yb (m (xb + j)) q) 1) =
      mrgSt (pc + 11) m xb xl yb yl ob j c (q + 1) (mrgFnd m yb (m (xb + j)) (q + 1)) 1 := by
  have hbit := scan_eq_bit E.W (m (yb + q)) (m (xb + j)) hby hvx
  have hflag := scan_flag E.W m yb (m (xb + j)) q hW
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  apply ramState_eq_of
  · simp only [mrgScanBody, mrgSt, runBlock_cons, runBlock_nil, execInstr] <;> omega
  · simp only [mrgScanBody, mrgSt, runBlock_cons, runBlock_nil, execInstr, Function.update_self,
      Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, zero_ne_one, one_ne_zero, Nat.zero_mod, Nat.mod_self, h1, ↓reduceIte]
  · intro d
    fin_cases d <;>
      simp only [mrgScanBody, mrgSt, Fin.isValue, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero, Nat.zero_mod,
        Nat.or_self, h1, Nat.mod_eq_of_lt hxj, Nat.mod_eq_of_lt hyq, Nat.mod_eq_of_lt hvx,
        Nat.mod_eq_of_lt hby, Nat.mod_eq_of_lt hq1, hbit, hflag, ↓reduceIte]

/-! ## 5. The two tests, and the inner scan simulated -/

theorem mrgSt_setPc (a a' : ℕ) (m : ℕ → ℕ) (xb xl yb yl ob j c q found v15 : ℕ) :
    { mrgSt a m xb xl yb yl ob j c q found v15 with pc := a' }
      = mrgSt a' m xb xl yb yl ob j c q found v15 := by
  apply ramState_eq_of
  · rfl
  · rfl
  · intro d; rfl

/-- The outer test `r0 < r6`, taken when it holds: only `pc` and `r15` move, and `r15` becomes `1`. -/
theorem mrgOuterTest_true (E : RAMEnv) (a : ℕ) (m : ℕ → ℕ) (xb xl yb yl ob j c : ℕ)
    (hW : 1 < 2 ^ E.W) (hj : j < xl) :
    { runBlock (Cond.lt r15 r0 r6).code E (mrgSt a m xb xl yb yl ob j c 0 0 0) with pc := a + 2 }
      = mrgSt (a + 2) m xb xl yb yl ob j c 0 0 1 := by
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  apply ramState_eq_of
  · rfl
  · rfl
  · intro d
    fin_cases d <;>
      simp only [Cond.code, mrgSt, Fin.isValue, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero, Nat.zero_mod,
        Nat.or_self, h1, hj, ↓reduceIte]

/-- The outer test, failing: `r15` becomes `0`. -/
theorem mrgOuterTest_false (E : RAMEnv) (a : ℕ) (m : ℕ → ℕ) (xb xl yb yl ob c : ℕ)
    (hW : 1 < 2 ^ E.W) :
    runBlock (Cond.lt r15 r0 r6).code E (mrgSt a m xb xl yb yl ob xl c 0 0 0)
      = mrgSt (a + 1) m xb xl yb yl ob xl c 0 0 0 := by
  apply ramState_eq_of
  · simp only [Cond.code, mrgSt, runBlock_cons, runBlock_nil, execInstr] <;> omega
  · rfl
  · intro d
    fin_cases d <;>
      simp only [Cond.code, mrgSt, Fin.isValue, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero, Nat.zero_mod,
        Nat.or_self, Nat.lt_irrefl, ↓reduceIte]

/-- The inner test `r2 < r8`, taken: `r15` stays `1`. -/
theorem mrgScanTest_true (E : RAMEnv) (a : ℕ) (m : ℕ → ℕ) (xb xl yb yl ob j c q found : ℕ)
    (hW : 1 < 2 ^ E.W) (hq : q < yl) :
    { runBlock (Cond.lt r15 r2 r8).code E (mrgSt a m xb xl yb yl ob j c q found 1)
        with pc := a + 2 }
      = mrgSt (a + 2) m xb xl yb yl ob j c q found 1 := by
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  apply ramState_eq_of
  · rfl
  · rfl
  · intro d
    fin_cases d <;>
      simp only [Cond.code, mrgSt, Fin.isValue, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero, Nat.zero_mod,
        Nat.or_self, h1, hq, ↓reduceIte]

/-- The inner test, failing: `r15` becomes `0`. -/
theorem mrgScanTest_false (E : RAMEnv) (a : ℕ) (m : ℕ → ℕ) (xb xl yb yl ob j c found : ℕ)
    (hW : 1 < 2 ^ E.W) :
    runBlock (Cond.lt r15 r2 r8).code E (mrgSt a m xb xl yb yl ob j c yl found 1)
      = mrgSt (a + 1) m xb xl yb yl ob j c yl found 0 := by
  apply ramState_eq_of
  · simp only [Cond.code, mrgSt, runBlock_cons, runBlock_nil, execInstr] <;> omega
  · rfl
  · intro d
    fin_cases d <;>
      simp only [Cond.code, mrgSt, Fin.isValue, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero, Nat.zero_mod,
        Nat.or_self, Nat.lt_irrefl, ↓reduceIte]

/-- **The loop rule with upper-bounded iterations.**  `Sem.loop` demands an exact cost per
iteration; the nested merge needs only an upper bound, so it is re-proved here with `≤`. -/
theorem Sem.loopLe (P : Program) (E : RAMEnv) (a : ℕ) (c : Cond) (b : Stmt)
    (hAt : At P a (Stmt.compile (Stmt.loop c b) a)) (hW : 1 < 2 ^ E.W) :
    ∀ (n : ℕ) (s : ℕ → RAMState) (cost : ℕ → ℕ),
      (∀ j, (s j).pc = a) →
      (∀ j < n, c.eval (s j)) →
      (¬ c.eval (s n)) →
      (∀ j < n, Sem P E (a + c.code.length + 1) a
        { runBlock c.code E (s j) with pc := a + c.code.length + 1 }
        (fun k s' => k ≤ cost j ∧ s' = s (j + 1))) →
      Sem P E a (a + c.code.length + b.len + 2) (s 0)
        (fun k s' => k ≤ (c.code.length + 1) +
            ∑ j ∈ Finset.range n, (c.code.length + 1 + cost j) ∧
          s' = { runBlock c.code E (s n) with pc := a + c.code.length + b.len + 2 }) := by
  intro n
  induction n with
  | zero =>
      intro s cost hpc _ hstop _
      refine Sem.mono (Sem.loopExit P E a c b (s 0) hAt hW (hpc 0) hstop) ?_
      intro k s' h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, rfl⟩
  | succ n ih =>
      intro s cost hpc hgo hstop hstep
      obtain ⟨hcode, hjz, -, -⟩ := at_loop hAt
      have htest : Sem P E a (a + c.code.length) (s 0)
          (fun k s' => k ≤ c.code.length ∧ s' = runBlock c.code E (s 0)) := by
        refine Sem.mono (Sem.block P E a c.code (s 0) hcode (Cond.noBranch_code c) (hpc 0)) ?_
        intro k s' h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨le_rfl, rfl⟩
      have hpcT : (runBlock c.code E (s 0)).pc = a + c.code.length := by
        rw [runBlock_pc c.code E (s 0) (Cond.noBranch_code c), hpc 0]
      have hne : (runBlock c.code E (s 0)).regs c.test ≠ 0 :=
        (Cond.eval_iff c E (s 0) hW).mp (hgo 0 (by omega))
      have hfall : Sem P E (a + c.code.length) (a + c.code.length + 1) (runBlock c.code E (s 0))
          (fun k s' => k ≤ 1 ∧
            s' = { runBlock c.code E (s 0) with pc := a + c.code.length + 1 }) := by
        refine Sem.mono (Sem.jz_next P E (a + c.code.length)
          (a + c.code.length + b.len + 2) c _ hjz hpcT hne) ?_
        intro k s' h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨le_rfl, rfl⟩
      have hfirst : Sem P E a a (s 0)
          (fun k s' => k ≤ (c.code.length + 1) + cost 0 ∧ s' = s 1) :=
        R66.Sem.trans_le (R66.Sem.trans_le htest hfall) (hstep 0 (by omega))
      have hrest : Sem P E a (a + c.code.length + b.len + 2) (s 1)
          (fun k s' => k ≤ (c.code.length + 1) +
              ∑ j ∈ Finset.range n, (c.code.length + 1 + cost (j + 1)) ∧
            s' = { runBlock c.code E (s (n + 1)) with pc := a + c.code.length + b.len + 2 }) :=
        ih (fun j => s (j + 1)) (fun j => cost (j + 1)) (fun j => hpc (j + 1))
          (fun j hj => hgo (j + 1) (by omega)) (by simpa using hstop)
          (fun j hj => hstep (j + 1) (by omega))
      refine Sem.mono (R66.Sem.trans_le hfirst hrest) ?_
      intro k s' h
      obtain ⟨hk, hs⟩ := h
      rw [Finset.sum_range_succ']
      exact ⟨by omega, hs⟩

/-- **The inner membership scan, simulated.**  Its invariant is exactly the one asked for:
`r3 = 1 ↔ ∃ q < cursor, B[q] = A[j]`, carried as `mrgFnd`. -/
theorem mrgScan_sem {P : Program} {E : RAMEnv} (a2 : ℕ)
    (hAt : At P a2 (Stmt.compile mrgScanStmt a2)) (hW : 1 < 2 ^ E.W)
    (xb xl yb yl ob j c : ℕ) (m : ℕ → ℕ)
    (hjw : xb + j < 2 ^ E.W) (hyl : yl < 2 ^ E.W)
    (hyw : ∀ q, q < yl → yb + q < 2 ^ E.W)
    (hv : m (xb + j) < 2 ^ E.W) (hyv : ∀ q, q < yl → m (yb + q) < 2 ^ E.W) :
    Sem P E a2 (a2 + mrgScanStmt.len) (mrgSt a2 m xb xl yb yl ob j c 0 0 1)
      (fun k s' => k ≤ 2 + 14 * yl ∧
        s' = mrgSt (a2 + mrgScanStmt.len) m xb xl yb yl ob j c yl
          (mrgFnd m yb (m (xb + j)) yl) 0) := by
  obtain ⟨-, hjz, hbodyAt, hjmp⟩ := at_loop hAt
  have hbodyAt' : At P (a2 + 2) mrgScanBody := by
    have h := hbodyAt
    rw [show (Cond.lt r15 r2 r8).code.length = 1 from rfl,
      show a2 + 1 + 1 = a2 + 2 from by omega] at h
    simpa only [Stmt.compile] using h
  have hjmp' : P[a2 + 2 + mrgScanBody.length]? = some (iJmp a2) := by
    have h := hjmp
    rw [show (Cond.lt r15 r2 r8).code.length = 1 from rfl,
      show (Stmt.code mrgScanBody).len = 11 from rfl,
      show a2 + 1 + 1 + 11 = a2 + 2 + 11 from by omega] at h
    exact h
  have hfam : ∀ q, mrgSt a2 m xb xl yb yl ob j c q (mrgFnd m yb (m (xb + j)) q) 1
      = mrgSt a2 m xb xl yb yl ob j c q (mrgFnd m yb (m (xb + j)) q) 1 := fun _ => rfl
  have hloop := Sem.loop P E a2 (Cond.lt r15 r2 r8) (.code mrgScanBody) hAt hW yl
    (fun q => mrgSt a2 m xb xl yb yl ob j c q (mrgFnd m yb (m (xb + j)) q) 1)
    (fun _ => 12)
    (fun q => mrgSt_pc a2 m xb xl yb yl ob j c q (mrgFnd m yb (m (xb + j)) q) 1)
    (fun q hq => by
      have h2 := mrgSt_r2 a2 m xb xl yb yl ob j c q (mrgFnd m yb (m (xb + j)) q) 1
      have h8 := mrgSt_r8 a2 m xb xl yb yl ob j c q (mrgFnd m yb (m (xb + j)) q) 1
      simp only [Cond.eval, h2, h8]
      exact hq)
    (fun hf => by
      have h2 := mrgSt_r2 a2 m xb xl yb yl ob j c yl (mrgFnd m yb (m (xb + j)) yl) 1
      have h8 := mrgSt_r8 a2 m xb xl yb yl ob j c yl (mrgFnd m yb (m (xb + j)) yl) 1
      simp only [Cond.eval, h2, h8] at hf
      exact absurd hf (lt_irrefl yl))
    (fun q hq => by
      show Sem P E (a2 + 2) a2
        { runBlock (Cond.lt r15 r2 r8).code E
            (mrgSt a2 m xb xl yb yl ob j c q (mrgFnd m yb (m (xb + j)) q) 1) with pc := a2 + 2 }
        (fun k s' => k = 12 ∧ s' = mrgSt a2 m xb xl yb yl ob j c (q + 1)
          (mrgFnd m yb (m (xb + j)) (q + 1)) 1)
      rw [mrgScanTest_true E a2 m xb xl yb yl ob j c q (mrgFnd m yb (m (xb + j)) q) hW hq]
      refine Sem.jmp_append (hAt := hjmp') (Sem.mono (Sem.block P E (a2 + 2) mrgScanBody _
        hbodyAt' (by simp [mrgScanBody]) rfl) ?_)
      intro k s' h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_⟩
      · rw [show mrgScanBody.length = 11 from rfl]
      · rw [mrgScanBody_run E (a2 + 2) xb xl yb yl ob j c q m hW hjw (hyw q hq)
          (by omega) hv (hyv q hq)]
        exact mrgSt_setPc _ _ _ _ _ _ _ _ _ _ _ _ _)
  refine Sem.mono hloop ?_
  intro k s' h
  obtain ⟨hk, hs⟩ := h
  have hsum : (∑ t ∈ Finset.range yl, (1 + 1 + 12 : ℕ)) = 14 * yl := by
    rw [show (1 + 1 + 12 : ℕ) = 14 from rfl]
    exact sum_range_const_mul yl 14
  refine ⟨?_, ?_⟩
  · rw [show (Cond.lt r15 r2 r8).code.length = 1 from rfl, hsum] at hk
    omega
  · rw [hs]
    show { runBlock (Cond.lt r15 r2 r8).code E
          (mrgSt a2 m xb xl yb yl ob j c yl (mrgFnd m yb (m (xb + j)) yl) 1) with pc := a2 + 14 }
        = mrgSt (a2 + mrgScanStmt.len) m xb xl yb yl ob j c yl
          (mrgFnd m yb (m (xb + j)) yl) 0
    rw [mrgScanTest_false E a2 m xb xl yb yl ob j c (mrgFnd m yb (m (xb + j)) yl) hW]
    exact mrgSt_setPc _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The kept list is no longer than the candidate list. -/
theorem mrgKept_length_le (xs : List ℕ) (ys : Finset ℕ) (j : ℕ) :
    (mrgKept xs ys j).length ≤ xs.length := by
  unfold mrgKept
  have h1 : ((xs.take j).filter (fun v => v ∉ ys)).length ≤ (xs.take j).length :=
    List.length_filter_le _ _
  have h2 : (xs.take j).length ≤ xs.length := by
    rw [List.length_take]
    omega
  omega

/-- The kept list is no longer than the cursor. -/
theorem mrgKept_length_le_j (xs : List ℕ) (ys : Finset ℕ) (j : ℕ) :
    (mrgKept xs ys j).length ≤ j := by
  unfold mrgKept
  have h1 : ((xs.take j).filter (fun v => v ∉ ys)).length ≤ (xs.take j).length :=
    List.length_filter_le _ _
  have h2 : (xs.take j).length ≤ j := by
    rw [List.length_take]
    omega
  omega

/-- `mrgMem` only writes inside `[ob, ob + c0 + |kept j|]`, which for `j < xs.length` lies strictly
below `ob + c0 + xs.length`. -/
theorem mrgMem_frame (m : ℕ → ℕ) (ob c0 : ℕ) (xs : List ℕ) (ys : Finset ℕ) :
    ∀ (j a : ℕ), j ≤ xs.length → (a < ob ∨ ob + (c0 + xs.length) ≤ a) →
      mrgMem m ob c0 xs ys j a = m a
  | 0, a, _, _ => rfl
  | (j + 1), a, hj, ha => by
      have hkj : (mrgKept xs ys j).length ≤ j := by
        unfold mrgKept
        have h1 : ((xs.take j).filter (fun v => v ∉ ys)).length ≤ (xs.take j).length :=
          List.length_filter_le _ _
        have h2 : (xs.take j).length ≤ j := by
          rw [List.length_take]
          omega
        omega
      show Function.update (mrgMem m ob c0 xs ys j) (ob + (c0 + (mrgKept xs ys j).length))
        (xs.getD j 0) a = m a
      have hne : a ≠ ob + (c0 + (mrgKept xs ys j).length) := by
        rcases ha with h | h
        · omega
        · omega
      rw [Function.update_of_ne hne]
      exact mrgMem_frame m ob c0 xs ys j a (by omega) ha

/-- `mrgFnd` only looks at `[b, b+q)`. -/
theorem mrgFnd_congr {m m' : ℕ → ℕ} {b v q : ℕ}
    (h : ∀ p, p < q → m' (b + p) = m (b + p)) : mrgFnd m' b v q = mrgFnd m b v q := by
  unfold mrgFnd
  congr 1
  apply propext
  constructor
  · rintro ⟨p, hp, he⟩
    exact ⟨p, hp, by rw [← h p hp]; exact he⟩
  · rintro ⟨p, hp, he⟩
    exact ⟨p, hp, by rw [h p hp]; exact he⟩

/-- The count after a keep step, in the shape the invariant needs. -/
theorem keep_count_eq (xs : List ℕ) (ys : Finset ℕ) (m : ℕ → ℕ) (yb c0 j yl : ℕ)
    (hys : ys = (mList m yb yl).toFinset) (hj : j < xs.length) :
    (c0 + (mrgKept xs ys j).length) + 1 - mrgFnd m yb (xs.getD j 0) yl
      = c0 + (mrgKept xs ys (j + 1)).length := by
  have hstep := mrgKept_succ (ys := ys) hj
  have hlen : (mrgKept xs ys (j + 1)).length
      = (mrgKept xs ys j).length + (if xs.getD j 0 ∈ ys then 0 else 1) := by
    rw [hstep, List.length_append]
    by_cases h : xs.getD j 0 ∈ ys
    · rw [if_pos h, List.length_nil, if_pos h]
    · rw [if_neg h, List.length_singleton, if_neg h]
  have hiff : (xs.getD j 0 ∈ ys) ↔ mrgFnd m yb (xs.getD j 0) yl = 1 := by
    rw [hys, ← mrgFnd_one_iff]
  by_cases h : xs.getD j 0 ∈ ys
  · rw [hlen, if_pos h, Nat.add_zero, hiff.mp h]
    omega
  · rw [hlen, if_neg h]
    have hf : mrgFnd m yb (xs.getD j 0) yl = 0 := by
      have h1 := mrgFnd_le_one m yb (xs.getD j 0) yl
      have h2 : mrgFnd m yb (xs.getD j 0) yl ≠ 1 := fun hc => h (hiff.mpr hc)
      omega
    rw [hf, Nat.sub_zero]
    omega

/-! ## 6. The outer pass, simulated -/

/-- **One outer iteration**: the inner scan, then the branchless keep (last write wins), then the
restore.  The output count becomes `c0 + |kept (j+1)|` and the memory becomes `mrgMem (j+1)`. -/
theorem mrgBody_sem {P : Program} {E : RAMEnv} (a : ℕ)
    (hAt : At P a (Stmt.compile mrgPass a)) (hW : 1 < 2 ^ E.W)
    (xb xl yb yl ob c0 j : ℕ) (m : ℕ → ℕ)
    (hj : j < xl) (hxl : xl < 2 ^ E.W) (hyl : yl < 2 ^ E.W)
    (hxb : xb + xl ≤ 2 ^ E.W) (hyb : yb + yl ≤ 2 ^ E.W)
    (hoc1 : ob + (c0 + xl) + 1 < 2 ^ E.W)
    (hdX : xb + xl ≤ ob ∨ ob + (c0 + xl) ≤ xb)
    (hdY : yb + yl ≤ ob ∨ ob + (c0 + xl) ≤ yb)
    (hxv : ∀ p, p < xl → m (xb + p) < 2 ^ E.W)
    (hyv : ∀ p, p < yl → m (yb + p) < 2 ^ E.W) :
    Sem P E (a + 2) a
      { runBlock (Cond.lt r15 r0 r6).code E
          (mrgSt a (mrgMem m ob c0 (mList m xb xl) (mList m yb yl).toFinset j) xb xl yb yl ob j
            (c0 + (mrgKept (mList m xb xl) (mList m yb yl).toFinset j).length) 0 0 0)
        with pc := a + 2 }
      (fun k s' => k ≤ 16 + 14 * yl ∧
        s' = mrgSt a (mrgMem m ob c0 (mList m xb xl) (mList m yb yl).toFinset (j + 1)) xb xl yb yl
          ob (j + 1)
          (c0 + (mrgKept (mList m xb xl) (mList m yb yl).toFinset (j + 1)).length) 0 0 0) := by
  obtain ⟨-, -, hbodyAt, hjmp⟩ := at_loop hAt
  have hbodyAt1 : At P (a + 2) (Stmt.compile mrgBody (a + 2)) := by
    have h := hbodyAt
    rw [show (Cond.lt r15 r0 r6).code.length = 1 from rfl,
      show a + 1 + 1 = a + 2 from rfl] at h
    exact h
  have hsplit : At P (a + 2) (Stmt.compile mrgScanStmt (a + 2) ++ (mrgKeep ++ mrgCleanup)) := by
    simpa [mrgBody, Stmt.compile] using hbodyAt1
  have hscanAt : At P (a + 2) (Stmt.compile mrgScanStmt (a + 2)) := (At.append.mp hsplit).1
  have hkeepAt : At P ((a + 2) + 14) (mrgKeep ++ mrgCleanup) := by
    have h2 := (At.append.mp hsplit).2
    rwa [Stmt.length_compile, mrgScanStmt_len] at h2
  have hjmp' : P[(a + 2) + 14 + 13]? = some (iJmp a) := by
    have h := hjmp
    rw [show (Cond.lt r15 r0 r6).code.length = 1 from rfl,
      show mrgBody.len = 27 from mrgBody_len,
      show a + 1 + 1 + 27 = (a + 2) + 14 + 13 from by omega] at h
    exact h
  set xs := mList m xb xl with hxs
  set ys := (mList m yb yl).toFinset with hys
  set cj := c0 + (mrgKept xs ys j).length with hcj
  set mj := mrgMem m ob c0 xs ys j with hmj
  have hxlen : xs.length = xl := by rw [hxs, mList_length]
  have hfx : ∀ p, p < xl → mj (xb + p) = m (xb + p) := by
    intro p hp
    rw [hmj]
    refine mrgMem_frame m ob c0 xs ys j (xb + p) (by omega) ?_
    rcases hdX with h | h
    · left; omega
    · right; rw [hxlen]; omega
  have hfy : ∀ p, p < yl → mj (yb + p) = m (yb + p) := by
    intro p hp
    rw [hmj]
    refine mrgMem_frame m ob c0 xs ys j (yb + p) (by omega) ?_
    rcases hdY with h | h
    · left; omega
    · right; rw [hxlen]; omega
  have hval : mj (xb + j) = xs.getD j 0 := by
    rw [hfx j hj, hxs, mList_getD m xb xl j hj]
  have hvj : mj (xb + j) < 2 ^ E.W := by
    rw [hval, hxs, mList_getD m xb xl j hj]
    exact hxv j hj
  have hkj : (mrgKept xs ys j).length ≤ j := mrgKept_length_le_j xs ys j
  have hmem : Function.update mj (ob + cj) (mj (xb + j))
      = mrgMem m ob c0 (mList m xb xl) (mList m yb yl).toFinset (j + 1) := by
    rw [hval, hcj, hmj]
    rfl
  have hcnt : cj + 1 - mrgFnd mj yb (mj (xb + j)) yl
      = c0 + (mrgKept (mList m xb xl) (mList m yb yl).toFinset (j + 1)).length := by
    have hfind : mrgFnd mj yb (mj (xb + j)) yl = mrgFnd m yb (xs.getD j 0) yl := by
      rw [hval]
      refine mrgFnd_congr ?_
      intro p hp
      exact hfy p hp
    rw [hfind, hcj]
    exact keep_count_eq xs ys m yb c0 j yl hys (by rw [hxlen]; omega)
  rw [mrgOuterTest_true E a mj xb xl yb yl ob j cj hW hj]
  have hscan := mrgScan_sem (P := P) (E := E) (a2 := a + 2) hscanAt hW xb xl yb yl ob j cj mj
    (by omega) hyl (fun q hq => by omega) hvj
    (fun q hq => by rw [hfy q hq]; exact hyv q hq)
  have hscan' : Sem P E (a + 2) ((a + 2) + 14)
      (mrgSt (a + 2) mj xb xl yb yl ob j cj 0 0 1)
      (fun k s' => k ≤ 2 + 14 * yl ∧
        s' = mrgSt ((a + 2) + 14) mj xb xl yb yl ob j cj yl
          (mrgFnd mj yb (mj (xb + j)) yl) 0) := by
    simpa only [mrgScanStmt_len] using hscan
  have hkeep : Sem P E ((a + 2) + 14) (((a + 2) + 14) + 13)
      (mrgSt ((a + 2) + 14) mj xb xl yb yl ob j cj yl (mrgFnd mj yb (mj (xb + j)) yl) 0)
      (fun k s' => k ≤ 13 ∧
        s' = mrgSt (((a + 2) + 14) + 13) (Function.update mj (ob + cj) (mj (xb + j)))
          xb xl yb yl ob (j + 1) (cj + 1 - mrgFnd mj yb (mj (xb + j)) yl) 0 0 0) := by
    refine Sem.mono (Sem.block P E ((a + 2) + 14) (mrgKeep ++ mrgCleanup) _ hkeepAt
      (by simp [mrgKeep, mrgCleanup, NoBranch, Instr.NoBranchI]) rfl) ?_
    intro k s' h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, ?_⟩
    · show (mrgKeep ++ mrgCleanup).length ≤ 13
      rw [show (mrgKeep ++ mrgCleanup).length = 13 from by
        simp [mrgKeep_length, mrgCleanup_length]]
    · exact mrgKeep_run E ((a + 2) + 14) xb xl yb yl ob j cj yl
        (mrgFnd mj yb (mj (xb + j)) yl) mj hW
        (mrgFnd_le_one mj yb (mj (xb + j)) yl)
        (by omega) (by rw [hcj]; omega) (by rw [hcj]; omega) (by omega) hvj
  refine Sem.jmp_append (hAt := hjmp') (Sem.mono (R66.Sem.trans_le hscan' hkeep) ?_)
  intro k s' h
  obtain ⟨hk, hs⟩ := h
  refine ⟨by omega, ?_⟩
  rw [hmem, hcnt] at hs
  rw [hs]
  exact mrgSt_setPc _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The pass's exit: the failing test and the wrap-around. -/
theorem mrgPassExit (E : RAMEnv) (a : ℕ) (m : ℕ → ℕ) (xb xl yb yl ob c : ℕ)
    (hW : 1 < 2 ^ E.W) :
    { runBlock (Cond.lt r15 r0 r6).code E (mrgSt a m xb xl yb yl ob xl c 0 0 0)
        with pc := ((a + 1) + 27) + 2 }
      = mrgSt (((a + 1) + 27) + 2) m xb xl yb yl ob xl c 0 0 0 := by
  apply ramState_eq_of
  · rfl
  · rfl
  · intro d
    fin_cases d <;>
      simp only [Cond.code, mrgSt, Fin.isValue, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero, Nat.zero_mod,
        Nat.or_self, Nat.lt_irrefl, ↓reduceIte]

/-- **One whole pass, simulated.**  From the pass's head it reaches its exit in
`2 + xl * (18 + 14 * yl)` steps, having written `pre ++ kept` into the output block. -/
theorem mrgPass_sem {P : Program} {E : RAMEnv} (a : ℕ)
    (hAt : At P a (Stmt.compile mrgPass a)) (hW : 1 < 2 ^ E.W)
    (xb xl yb yl ob c0 : ℕ) (m : ℕ → ℕ)
    (hxl : xl < 2 ^ E.W) (hyl : yl < 2 ^ E.W)
    (hxb : xb + xl ≤ 2 ^ E.W) (hyb : yb + yl ≤ 2 ^ E.W)
    (hoc1 : ob + (c0 + xl) + 1 < 2 ^ E.W)
    (hdX : xb + xl ≤ ob ∨ ob + (c0 + xl) ≤ xb)
    (hdY : yb + yl ≤ ob ∨ ob + (c0 + xl) ≤ yb)
    (hxv : ∀ p, p < xl → m (xb + p) < 2 ^ E.W)
    (hyv : ∀ p, p < yl → m (yb + p) < 2 ^ E.W) :
    Sem P E a (a + mrgPass.len) (mrgSt a m xb xl yb yl ob 0 c0 0 0 0)
      (fun k s' => k ≤ 2 + xl * (18 + 14 * yl) ∧
        s' = mrgSt (a + mrgPass.len)
          (mrgMem m ob c0 (mList m xb xl) (mList m yb yl).toFinset xl) xb xl yb yl ob xl
          (c0 + (mrgKept (mList m xb xl) (mList m yb yl).toFinset xl).length) 0 0 0) := by
  have hloop := Sem.loopLe P E a (Cond.lt r15 r0 r6) mrgBody hAt hW xl
    (fun j => mrgSt a (mrgMem m ob c0 (mList m xb xl) (mList m yb yl).toFinset j) xb xl yb yl ob j
      (c0 + (mrgKept (mList m xb xl) (mList m yb yl).toFinset j).length) 0 0 0)
    (fun _ => 16 + 14 * yl)
    (fun j => mrgSt_pc a (mrgMem m ob c0 (mList m xb xl) (mList m yb yl).toFinset j) xb xl yb yl
      ob j (c0 + (mrgKept (mList m xb xl) (mList m yb yl).toFinset j).length) 0 0 0)
    (fun j hj => by
      have h1 := mrgSt_r0 a (mrgMem m ob c0 (mList m xb xl) (mList m yb yl).toFinset j) xb xl yb yl
        ob j (c0 + (mrgKept (mList m xb xl) (mList m yb yl).toFinset j).length) 0 0 0
      have h2 := mrgSt_r6 a (mrgMem m ob c0 (mList m xb xl) (mList m yb yl).toFinset j) xb xl yb yl
        ob j (c0 + (mrgKept (mList m xb xl) (mList m yb yl).toFinset j).length) 0 0 0
      simp only [Cond.eval, h1, h2]
      exact hj)
    (fun hf => by
      have h1 := mrgSt_r0 a (mrgMem m ob c0 (mList m xb xl) (mList m yb yl).toFinset xl) xb xl yb yl
        ob xl (c0 + (mrgKept (mList m xb xl) (mList m yb yl).toFinset xl).length) 0 0 0
      have h2 := mrgSt_r6 a (mrgMem m ob c0 (mList m xb xl) (mList m yb yl).toFinset xl) xb xl yb yl
        ob xl (c0 + (mrgKept (mList m xb xl) (mList m yb yl).toFinset xl).length) 0 0 0
      simp only [Cond.eval, h1, h2] at hf
      exact absurd hf (lt_irrefl xl))
    (fun j hj => by
      simpa only [show (Cond.lt r15 r0 r6).code.length = 1 from rfl] using
        (mrgBody_sem a hAt hW xb xl yb yl ob c0 j m hj hxl hyl hxb hyb hoc1 hdX hdY hxv hyv))
  refine Sem.mono hloop ?_
  intro k s' h
  obtain ⟨hk, hs⟩ := h
  have hsum : (∑ t ∈ Finset.range xl, (1 + 1 + (16 + 14 * yl) : ℕ)) = xl * (18 + 14 * yl) := by
    have hc : (1 + 1 + (16 + 14 * yl) : ℕ) = 18 + 14 * yl := by omega
    rw [hc, sum_range_const_mul, Nat.mul_comm]
  refine ⟨?_, ?_⟩
  · rw [show (Cond.lt r15 r0 r6).code.length = 1 from rfl, hsum] at hk
    omega
  · rw [hs]
    show { runBlock (Cond.lt r15 r0 r6).code E
          (mrgSt a (mrgMem m ob c0 (mList m xb xl) (mList m yb yl).toFinset xl) xb xl yb yl ob xl
            (c0 + (mrgKept (mList m xb xl) (mList m yb yl).toFinset xl).length) 0 0 0)
        with pc := ((a + 1) + 27) + 2 }
        = mrgSt (a + mrgPass.len)
          (mrgMem m ob c0 (mList m xb xl) (mList m yb yl).toFinset xl) xb xl yb yl ob xl
          (c0 + (mrgKept (mList m xb xl) (mList m yb yl).toFinset xl).length) 0 0 0
    rw [mrgPassExit E a _ xb xl yb yl ob _ hW]
    rw [show ((a + 1) + 27) + 2 = a + mrgPass.len from by rw [mrgPass_len]]

/-! ## 7. The output list: duplicate-free, and its value set

The two passes produce `A \ B` followed by `B \ A`.  With `Nodup` on both input lists this is
duplicate-free, and its value set is the symmetric difference. -/

/-- Lists of equal length with equal words are equal. -/
theorem list_eq_of_getD {l₁ l₂ : List ℕ} (h : l₁.length = l₂.length)
    (hg : ∀ i, i < l₁.length → l₁.getD i 0 = l₂.getD i 0) : l₁ = l₂ := by
  apply List.ext_getElem h
  intro n h1 h2
  rw [← List.getD_eq_getElem l₁ 0 h1, ← List.getD_eq_getElem l₂ 0 h2]
  exact hg n h1

/-- The output list of the canonical final state, with `r0` at the output base. -/
theorem outList_mrgSt (a m xb xl yb yl ob c : ℕ) :
    outList (mrgSt a m xb xl yb yl ob ob c 0 0 0) = mList m ob c := by
  simp only [outList, mList, mrgSt_r1, mrgSt_r0, mrgSt_mem]

/-- The merge's cost: head, `A \ B`, the swap, `B \ A`, the header. -/
def mrgCost (al bl : ℕ) : ℕ :=
  16 + (2 + al * (18 + 14 * bl)) + (9 + ((2 + bl * (18 + 14 * al)) + 1))

theorem merge_out_nodup (xs ys : List ℕ) (hx : xs.Nodup) (hy : ys.Nodup) :
    (mrgKept xs ys.toFinset xs.length ++ mrgKept ys xs.toFinset ys.length).Nodup := by
  refine List.Nodup.append (mrgKept_nodup hx _ _) (mrgKept_nodup hy _ _) ?_
  intro z hz hz'
  have h1 := (mem_mrgKept (xs := xs) (ys := ys.toFinset) (j := xs.length) z).mp hz
  have h2 := (mem_mrgKept (xs := ys) (ys := xs.toFinset) (j := ys.length) z).mp hz'
  rw [List.take_length] at h1 h2
  exact h1.2 (by simpa using h2.1)

theorem merge_out_toFinset (xs ys : List ℕ) :
    (mrgKept xs ys.toFinset xs.length ++ mrgKept ys xs.toFinset ys.length).toFinset
      = symmDiff xs.toFinset ys.toFinset := by
  rw [List.toFinset_append, mrgKept_toFinset, mrgKept_toFinset]
  ext v
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_symmDiff]

/-- **The corrected merge contract.**  It differs from the retired `SmergeRuns` in exactly the ways
the old one was false:

* `Nodup` **on both input lists** (the branchless keep preserves multiplicities: `A = [5,5]`,
  `B = []` would otherwise violate `(outList s').Nodup`);
* an explicit word bound for **every** address the program computes (`ab + al`, `bb + bl`,
  `outBase + al + bl + 1`) and for every stored value;
* both input blocks disjoint from the output block, so the second pass still reads the original `A`;
* the exit address is the **repaired** program's `base + mrgStmtFull.len = base + 86`, and the
  second pass is the *same* `mrgPass` after a real swap, so the output is `(A \ B) ++ (B \ A)`.

The conclusion is the list identity, which implies both `(outList s').Nodup` and the symmetric
difference statement of the published contract. -/
def SmergeRunsM (P : Program) (E : RAMEnv) (base ab al bb bl ob : ℕ) : Prop :=
  ∀ s : RAMState, s.pc = base →
    s.regs r10 = ab ∧ s.regs r11 = al ∧ s.regs r12 = bb ∧ s.regs r13 = bl ∧ s.regs r14 = ob →
    (mList s.mem ab al).Nodup → (mList s.mem bb bl).Nodup →
    (∀ p, p < al → s.mem (ab + p) < 2 ^ E.W) → (∀ p, p < bl → s.mem (bb + p) < 2 ^ E.W) →
    al < 2 ^ E.W → bl < 2 ^ E.W →
    ab + al ≤ 2 ^ E.W → bb + bl ≤ 2 ^ E.W → ob + (al + bl) + 1 < 2 ^ E.W →
    (ab + al ≤ ob ∨ ob + (al + bl) ≤ ab) → (bb + bl ≤ ob ∨ ob + (al + bl) ≤ bb) →
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ mrgCost al bl ∧ (step P E)^[k] s = s' ∧
      s'.pc = base + mrgStmtFull.len ∧
      outList s' = mrgKept (mList s.mem ab al) (mList s.mem bb bl).toFinset al ++
        mrgKept (mList s.mem bb bl) (mList s.mem ab al).toFinset bl

/-- The contract implies the published shape: duplicate-free, with value set `A △ B`. -/
theorem smergeRunsM_implies (P : Program) (E : RAMEnv) (base ab al bb bl ob : ℕ)
    (h : SmergeRunsM P E base ab al bb bl ob) (s : RAMState) (hpc : s.pc = base)
    (hregs : s.regs r10 = ab ∧ s.regs r11 = al ∧ s.regs r12 = bb ∧ s.regs r13 = bl ∧
      s.regs r14 = ob)
    (hndA : (mList s.mem ab al).Nodup) (hndB : (mList s.mem bb bl).Nodup)
    (hvA : ∀ p, p < al → s.mem (ab + p) < 2 ^ E.W)
    (hvB : ∀ p, p < bl → s.mem (bb + p) < 2 ^ E.W)
    (hal : al < 2 ^ E.W) (hbl : bl < 2 ^ E.W)
    (hab : ab + al ≤ 2 ^ E.W) (hbb : bb + bl ≤ 2 ^ E.W) (hob : ob + (al + bl) + 1 < 2 ^ E.W)
    (hdA : ab + al ≤ ob ∨ ob + (al + bl) ≤ ab)
    (hdB : bb + bl ≤ ob ∨ ob + (al + bl) ≤ bb) :
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ mrgCost al bl ∧ (step P E)^[k] s = s' ∧
      s'.pc = base + mrgStmtFull.len ∧ (outList s').Nodup ∧
      (outList s').toFinset = symmDiff (mList s.mem ab al).toFinset (mList s.mem bb bl).toFinset := by
  obtain ⟨k, s', hk, hstep, hpc', hout⟩ := h s hpc hregs hndA hndB hvA hvB hal hbl hab hbb hob hdA hdB
  have hnd : (outList s').Nodup := by
    rw [hout]
    have hh := merge_out_nodup (mList s.mem ab al) (mList s.mem bb bl) hndA hndB
    simpa [mList_length] using hh
  have hset : (outList s').toFinset
      = symmDiff (mList s.mem ab al).toFinset (mList s.mem bb bl).toFinset := by
    rw [hout]
    have hh := merge_out_toFinset (mList s.mem ab al) (mList s.mem bb bl)
    simpa [mList_length] using hh
  exact ⟨k, s', hk, hstep, hpc', hnd, hset⟩

/-! ## 8. The composition of the four blocks, and the output list -/

/-- The memory after the first pass: the kept prefix of `A` written from `ob` upwards. -/
def mrgMem1 (m : ℕ → ℕ) (ab al bb bl ob : ℕ) : ℕ → ℕ :=
  mrgMem m ob 0 (mList m ab al) (mList m bb bl).toFinset al

/-- The output count after the first pass. -/
def mrgCnt1 (m : ℕ → ℕ) (ab al bb bl : ℕ) : ℕ :=
  (mrgKept (mList m ab al) (mList m bb bl).toFinset al).length

/-- The memory after the second pass: `A \ B` followed by `B \ A`. -/
def mrgMem2 (m : ℕ → ℕ) (ab al bb bl ob : ℕ) : ℕ → ℕ :=
  mrgMem (mrgMem1 m ab al bb bl ob) ob (mrgCnt1 m ab al bb bl)
    (mList (mrgMem1 m ab al bb bl ob) bb bl)
    (mList (mrgMem1 m ab al bb bl ob) ab al).toFinset bl

/-- The output count after the second pass. -/
def mrgCnt2 (m : ℕ → ℕ) (ab al bb bl ob : ℕ) : ℕ :=
  mrgCnt1 m ab al bb bl +
    (mrgKept (mList (mrgMem1 m ab al bb bl ob) bb bl)
      (mList (mrgMem1 m ab al bb bl ob) ab al).toFinset bl).length

/-- The exact state the merge leaves behind. -/
def mrgFin (a : ℕ) (m : ℕ → ℕ) (ab al bb bl ob : ℕ) : RAMState :=
  mrgSt a (mrgMem2 m ab al bb bl ob) bb bl ab al ob ob (mrgCnt2 m ab al bb bl ob) 0 0 0

/-- The address at which the composed merge ends (before rewriting to `base + 86`). -/
def mrgEnd (base : ℕ) : ℕ :=
  (((((base + 16) + mrgPass.len) + mrgSwap.length) + mrgPass.len) + 1)

theorem mrgEnd_eq (base : ℕ) : mrgEnd base = base + mrgStmtFull.len := by
  rw [mrgEnd, mrgStmtFull_len, mrgPass_len, mrgSwap_length]

/-- The head only sees its argument registers **modulo the word size**: `r → r % 2^W`. -/
theorem mrgHead_run_mod (E : RAMEnv) (pc ab al bb bl ob : ℕ) (m : ℕ → ℕ) (r : Fin 16 → ℕ)
    (hW : 1 < 2 ^ E.W)
    (hab : r r10 % 2 ^ E.W = ab) (hal : r r11 % 2 ^ E.W = al)
    (hbb : r r12 % 2 ^ E.W = bb) (hbl : r r13 % 2 ^ E.W = bl)
    (hob : r r14 % 2 ^ E.W = ob) :
    runBlock mrgHead E ⟨pc, r, m⟩ = mrgSt (pc + 16) m ab al bb bl ob 0 0 0 0 0 := by
  have h1 : (1 : ℕ) % 2 ^ E.W = 1 := Nat.mod_eq_of_lt hW
  apply ramState_eq_of
  · simp only [mrgHead, mrgSt, runBlock_cons, runBlock_nil, execInstr]
  · simp only [mrgHead, mrgSt, runBlock_cons, runBlock_nil, execInstr]
  · intro d
    fin_cases d <;>
      simp only [mrgHead, mrgSt, Fin.isValue, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero, Nat.zero_mod,
        Nat.or_self, h1, hab, hal, hbb, hbl, hob, ↓reduceIte]

/-- `r0 := r9` costs one step and moves the output cursor to the output base. -/
theorem mrgHdr_run (E : RAMEnv) (pc xb xl yb yl ob j c : ℕ) (m : ℕ → ℕ)
    (hob : ob < 2 ^ E.W) :
    runBlock [iBor r0 r9 r9] E (mrgSt pc m xb xl yb yl ob j c 0 0 0) =
      mrgSt (pc + 1) m xb xl yb yl ob ob c 0 0 0 := by
  have h1 : (ob ||| ob) % 2 ^ E.W = ob := by
    rw [Nat.or_self, Nat.mod_eq_of_lt hob]
  apply ramState_eq_of
  · simp only [mrgSt, runBlock_cons, runBlock_nil, execInstr]
  · simp only [mrgSt, runBlock_cons, runBlock_nil, execInstr]
  · intro d
    fin_cases d <;>
      simp only [mrgSt, Fin.isValue, runBlock_cons, runBlock_nil, execInstr,
        Function.update_self, Function.update_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, zero_ne_one, one_ne_zero, Nat.zero_mod, h1,
        ↓reduceIte]

/-- **The merge, composed**: `head → pass → swap → pass → header`.  Each block is proved against
its own named state; no `simp` ever sees a `runBlock` of the concatenation. -/
theorem mrgStep_state {P : Program} {E : RAMEnv} {base ab al bb bl ob : ℕ} {s : RAMState}
    (hAt : At P base (mrgStmtFull.compile base)) (hW : 1 < 2 ^ E.W) (hpc : s.pc = base)
    (h10 : s.regs r10 % 2 ^ E.W = ab) (h11 : s.regs r11 % 2 ^ E.W = al)
    (h12 : s.regs r12 % 2 ^ E.W = bb) (h13 : s.regs r13 % 2 ^ E.W = bl)
    (h14 : s.regs r14 % 2 ^ E.W = ob)
    (habW : ab < 2 ^ E.W) (halW : al < 2 ^ E.W) (hbbW : bb < 2 ^ E.W)
    (hblW : bl < 2 ^ E.W) (hobW : ob < 2 ^ E.W)
    (hab : ab + al ≤ 2 ^ E.W) (hbb : bb + bl ≤ 2 ^ E.W)
    (hob : ob + (al + bl) + 1 < 2 ^ E.W)
    (hdA : ab + al ≤ ob ∨ ob + (al + bl) ≤ ab)
    (hdB : bb + bl ≤ ob ∨ ob + (al + bl) ≤ bb)
    (hvA : ∀ p, p < al → s.mem (ab + p) < 2 ^ E.W)
    (hvB : ∀ p, p < bl → s.mem (bb + p) < 2 ^ E.W) :
    Sem P E base (mrgEnd base) s
      (fun k s' => k ≤ mrgCost al bl ∧ s' = mrgFin (mrgEnd base) s.mem ab al bb bl ob) := by
  obtain ⟨pc, rg, mm⟩ := s
  have hpc' : pc = base := hpc
  rw [hpc']
  rw [mrgStmtFull_shape] at hAt
  obtain ⟨hheadAt, hrest⟩ := At.append.mp hAt
  rw [mrgHead_length] at hrest
  obtain ⟨hpass1At, hrest⟩ := At.append.mp hrest
  rw [Stmt.length_compile] at hrest
  obtain ⟨hswapAt, hrest⟩ := At.append.mp hrest
  obtain ⟨hpass2At, hfinalAt⟩ := At.append.mp hrest
  rw [Stmt.length_compile] at hfinalAt
  let A : List ℕ := mList mm ab al
  let B : List ℕ := mList mm bb bl
  let Bf : Finset ℕ := B.toFinset
  let m1 : ℕ → ℕ := mrgMem mm ob 0 A Bf al
  let K1 : List ℕ := mrgKept A Bf al
  let c1 : ℕ := K1.length
  let B1 : List ℕ := mList m1 bb bl
  let A1 : List ℕ := mList m1 ab al
  let K2 : List ℕ := mrgKept B1 A1.toFinset bl
  let m2 : ℕ → ℕ := mrgMem m1 ob c1 B1 A1.toFinset bl
  let s1 : RAMState := mrgSt (base + 16) mm ab al bb bl ob 0 0 0 0 0
  let s2 : RAMState := mrgSt ((base + 16) + mrgPass.len) m1 ab al bb bl ob al c1 0 0 0
  let s3 : RAMState :=
    mrgSt (((base + 16) + mrgPass.len) + mrgSwap.length) m1 bb bl ab al ob 0 c1 0 0 0
  let s4 : RAMState :=
    mrgSt ((((base + 16) + mrgPass.len) + mrgSwap.length) + mrgPass.len) m2 bb bl ab al ob bl
      (c1 + K2.length) 0 0 0
  let s5 : RAMState :=
    mrgSt (((((base + 16) + mrgPass.len) + mrgSwap.length) + mrgPass.len) + 1) m2 bb bl ab al ob ob
      (c1 + K2.length) 0 0 0
  have hAlen : A.length = al := by
    rw [show A = mList mm ab al from rfl, mList_length]
  have hBlen : B.length = bl := by
    rw [show B = mList mm bb bl from rfl, mList_length]
  have hc1le : c1 ≤ al := by
    rw [show c1 = K1.length from rfl, show K1 = mrgKept A Bf al from rfl,
      show Bf = B.toFinset from rfl]
    calc (mrgKept A B.toFinset al).length ≤ A.length := mrgKept_length_le A B.toFinset al
      _ = al := hAlen
  have hc1W : c1 < 2 ^ E.W := by omega
  have hhead : Sem P E base (base + 16) ⟨base, rg, mm⟩ (fun k s' => k ≤ 16 ∧ s' = s1) := by
    refine Sem.mono (Sem.block P E base mrgHead ⟨base, rg, mm⟩ hheadAt mrgHead_noBranch rfl) ?_
    intro k s' h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨le_rfl, ?_⟩
    exact mrgHead_run_mod E base ab al bb bl ob mm rg hW h10 h11 h12 h13 h14
  have hp1 : Sem P E (base + 16) ((base + 16) + mrgPass.len) s1
      (fun k s' => k ≤ 2 + al * (18 + 14 * bl) ∧ s' = s2) := by
    have h := mrgPass_sem (P := P) (E := E) (a := base + 16) hpass1At hW ab al bb bl ob 0 mm
      halW hblW hab hbb (by omega)
      (by rcases hdA with h | h
          · exact Or.inl h
          · exact Or.inr (by omega))
      (by rcases hdB with h | h
          · exact Or.inl h
          · exact Or.inr (by omega))
      hvA hvB
    rw [Nat.zero_add] at h
    exact h
  have hsw : Sem P E ((base + 16) + mrgPass.len)
      (((base + 16) + mrgPass.len) + mrgSwap.length) s2
      (fun k s' => k ≤ mrgSwap.length ∧ s' = s3) := by
    refine Sem.mono (Sem.block P E ((base + 16) + mrgPass.len) mrgSwap s2 hswapAt
      (by simp [mrgSwap, NoBranch, Instr.NoBranchI]) rfl) ?_
    intro k s' h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨le_rfl, ?_⟩
    exact mrgSwap_run E ((base + 16) + mrgPass.len) ab al bb bl ob al c1 m1 hW habW halW
      hbbW hblW hobW halW hc1W
  have hmA : ∀ p, p < al → m1 (ab + p) = mm (ab + p) := by
    intro p hp
    have h := mrgMem_frame mm ob 0 A Bf al (ab + p) (by omega) ?_
    · rw [show m1 = mrgMem mm ob 0 A Bf al from rfl]; exact h
    · rcases hdA with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  have hmB : ∀ p, p < bl → m1 (bb + p) = mm (bb + p) := by
    intro p hp
    have h := mrgMem_frame mm ob 0 A Bf al (bb + p) (by omega) ?_
    · rw [show m1 = mrgMem mm ob 0 A Bf al from rfl]; exact h
    · rcases hdB with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  have hp2 : Sem P E (((base + 16) + mrgPass.len) + mrgSwap.length)
      ((((base + 16) + mrgPass.len) + mrgSwap.length) + mrgPass.len) s3
      (fun k s' => k ≤ 2 + bl * (18 + 14 * al) ∧ s' = s4) := by
    exact mrgPass_sem (P := P) (E := E)
      (a := ((base + 16) + mrgPass.len) + mrgSwap.length) hpass2At hW bb bl ab al ob c1 m1
      hblW halW hbb hab (by omega)
      (by rcases hdB with h | h
          · exact Or.inl h
          · exact Or.inr (by omega))
      (by rcases hdA with h | h
          · exact Or.inl h
          · exact Or.inr (by omega))
      (fun p hp => by rw [hmB p hp]; exact hvB p hp)
      (fun p hp => by rw [hmA p hp]; exact hvA p hp)
  have hdr : Sem P E ((((base + 16) + mrgPass.len) + mrgSwap.length) + mrgPass.len)
      (((((base + 16) + mrgPass.len) + mrgSwap.length) + mrgPass.len) + 1) s4
      (fun k s' => k ≤ 1 ∧ s' = s5) := by
    refine Sem.mono (Sem.block P E ((((base + 16) + mrgPass.len) + mrgSwap.length) + mrgPass.len)
      [iBor r0 r9 r9] s4 hfinalAt ?_ rfl) ?_
    · simp [NoBranch, Instr.NoBranchI]
    · intro k s' h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨le_rfl, ?_⟩
      exact mrgHdr_run E ((((base + 16) + mrgPass.len) + mrgSwap.length) + mrgPass.len)
        bb bl ab al ob bl (c1 + K2.length) m2 hobW
  have h12 := R66.Sem.trans_le hhead hp1
  have h123 := R66.Sem.trans_le h12 hsw
  have h1234 := R66.Sem.trans_le h123 hp2
  have hfull := R66.Sem.trans_le h1234 hdr
  refine Sem.mono hfull ?_
  intro k s' h
  obtain ⟨hk, rfl⟩ := h
  rw [mrgSwap_length] at hk
  refine ⟨by rw [mrgCost]; omega, ?_⟩
  rfl

/-! ### 8.1 The output list of the composed state -/

/-- Reading a list at a base that differs from the true base only by `% 2^W` is harmless: if the
block is nonempty the two bases agree, and if it is empty both lists are empty. -/
theorem mList_mod (m : ℕ → ℕ) (b len W : ℕ) (h : b + len ≤ 2 ^ W) (hl : len < 2 ^ W) :
    mList m (b % 2 ^ W) len = mList m b len := by
  rcases Nat.eq_zero_or_pos len with h0 | hpos
  · rw [h0]; simp [mList]
  · have hb : b < 2 ^ W := by omega
    rw [Nat.mod_eq_of_lt hb]

/-- **The output list of the merge.**  The final memory is exactly `A \ B` followed by `B \ A`. -/
theorem mrgFin_out (a : ℕ) (m : ℕ → ℕ) (ab al bb bl ob : ℕ)
    (hdA : ab + al ≤ ob ∨ ob + (al + bl) ≤ ab)
    (hdB : bb + bl ≤ ob ∨ ob + (al + bl) ≤ bb) :
    outList (mrgFin a m ab al bb bl ob)
      = mrgKept (mList m ab al) (mList m bb bl).toFinset al ++
        mrgKept (mList m bb bl) (mList m ab al).toFinset bl := by
  rw [mrgFin]
  have hout : outList (mrgSt a (mrgMem2 m ab al bb bl ob) bb bl ab al ob ob
      (mrgCnt2 m ab al bb bl ob) 0 0 0)
      = mList (mrgMem2 m ab al bb bl ob) ob (mrgCnt2 m ab al bb bl ob) := by
    simp only [outList, mList, mrgSt_r1, mrgSt_r0, mrgSt_mem]
  rw [hout]
  rw [mrgMem2, mrgCnt2, mrgMem1, mrgCnt1]
  set A : List ℕ := mList m ab al with hA
  set B : List ℕ := mList m bb bl with hB
  set m1 : ℕ → ℕ := mrgMem m ob 0 A B.toFinset al with hm1
  set K1 : List ℕ := mrgKept A B.toFinset al with hK1
  set c1 : ℕ := K1.length with hc1
  set B1 : List ℕ := mList m1 bb bl with hB1
  set A1 : List ℕ := mList m1 ab al with hA1
  set K2 : List ℕ := mrgKept B1 A1.toFinset bl with hK2
  set m2 : ℕ → ℕ := mrgMem m1 ob c1 B1 A1.toFinset bl with hm2
  have hAlen : A.length = al := by rw [hA, mList_length]
  have hBlen : B.length = bl := by rw [hB, mList_length]
  have hpre : ∀ i, i < c1 → m1 (ob + i) = K1.getD i 0 := by
    intro i hi
    have h := mrgMem_get m ob 0 A B.toFinset ([] : List ℕ) (by simp)
      (by intro j hj; omega) al (by rw [hAlen]) i (by rw [Nat.zero_add]; exact hi)
    simpa [← hm1, hK1] using h
  have hmA : ∀ p, p < al → m1 (ab + p) = m (ab + p) := by
    intro p hp
    have h := mrgMem_frame m ob 0 A B.toFinset al (ab + p) (by rw [hAlen]) ?_
    · simpa [← hm1] using h
    · rcases hdA with hh | hh
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  have hmB : ∀ p, p < bl → m1 (bb + p) = m (bb + p) := by
    intro p hp
    have h := mrgMem_frame m ob 0 A B.toFinset al (bb + p) (by rw [hAlen]) ?_
    · simpa [← hm1] using h
    · rcases hdB with hh | hh
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  have hA1eq : A1 = A := by
    rw [hA1, hA]
    apply list_eq_of_getD
    · simp [mList_length]
    · intro i hi
      rw [mList_length] at hi
      rw [mList_getD m1 ab al i hi, mList_getD m ab al i hi]
      exact hmA i hi
  have hB1eq : B1 = B := by
    rw [hB1, hB]
    apply list_eq_of_getD
    · simp [mList_length]
    · intro i hi
      rw [mList_length] at hi
      rw [mList_getD m1 bb bl i hi, mList_getD m bb bl i hi]
      exact hmB i hi
  have hK2eq : K2 = mrgKept B A.toFinset bl := by
    simp only [hK2, hB1eq, hA1eq]
  have hfull : ∀ i, i < c1 + K2.length → m2 (ob + i) = (K1 ++ K2).getD i 0 := by
    intro i hi
    have h := mrgMem_get m1 ob c1 B1 A1.toFinset K1 hc1.symm hpre bl
      (by rw [hB1eq, hBlen]) i hi
    simpa [← hm2, ← hK2] using h
  have hlist : mList m2 ob (c1 + K2.length) = K1 ++ K2 := by
    apply list_eq_of_getD
    · simp [mList_length, hc1]
    · intro i hi
      rw [mList_length] at hi
      rw [mList_getD m2 ob (c1 + K2.length) i hi]
      exact hfull i hi
  have hR : mrgKept (mList m ab al) (mList m bb bl).toFinset al ++
      mrgKept (mList m bb bl) (mList m ab al).toFinset bl = K1 ++ K2 := by
    rw [← hA, ← hB, ← hK1, ← hK2eq]
  exact hlist.trans hR.symm

/-! ### 8.2 The contract -/

/-- **The merge, end to end**: from *any* entry state whose `r10 … r14` hold the two bases and the
output base, the program reaches the final state in at most `mrgCost al bl` steps, and the output
list is `A \ B` followed by `B \ A`. -/
theorem mrgStep_sem {P : Program} {E : RAMEnv} {base ab al bb bl ob : ℕ} {s : RAMState}
    (hAt : At P base (mrgStmtFull.compile base)) (hW : 1 < 2 ^ E.W) (hpc : s.pc = base)
    (h10 : s.regs r10 = ab) (h11 : s.regs r11 = al) (h12 : s.regs r12 = bb)
    (h13 : s.regs r13 = bl) (h14 : s.regs r14 = ob)
    (halW : al < 2 ^ E.W) (hblW : bl < 2 ^ E.W)
    (hab : ab + al ≤ 2 ^ E.W) (hbb : bb + bl ≤ 2 ^ E.W)
    (hob : ob + (al + bl) + 1 < 2 ^ E.W)
    (hdA : ab + al ≤ ob ∨ ob + (al + bl) ≤ ab)
    (hdB : bb + bl ≤ ob ∨ ob + (al + bl) ≤ bb)
    (hvA : ∀ p, p < al → s.mem (ab + p) < 2 ^ E.W)
    (hvB : ∀ p, p < bl → s.mem (bb + p) < 2 ^ E.W) :
    Sem P E base (base + mrgStmtFull.len) s
      (fun k s' => k ≤ mrgCost al bl ∧
        outList s' = mrgKept (mList s.mem ab al) (mList s.mem bb bl).toFinset al ++
          mrgKept (mList s.mem bb bl) (mList s.mem ab al).toFinset bl) := by
  set ab' : ℕ := ab % 2 ^ E.W with hab'
  set bb' : ℕ := bb % 2 ^ E.W with hbb'
  have h10' : s.regs r10 % 2 ^ E.W = ab' := by rw [h10, hab']
  have h11' : s.regs r11 % 2 ^ E.W = al := by rw [h11, Nat.mod_eq_of_lt halW]
  have h12' : s.regs r12 % 2 ^ E.W = bb' := by rw [h12, hbb']
  have h13' : s.regs r13 % 2 ^ E.W = bl := by rw [h13, Nat.mod_eq_of_lt hblW]
  have hobW : ob < 2 ^ E.W := by omega
  have h14' : s.regs r14 % 2 ^ E.W = ob := by rw [h14, Nat.mod_eq_of_lt hobW]
  have hmodA : ab' ≤ ab := by rw [hab']; exact Nat.mod_le ab (2 ^ E.W)
  have hmodB : bb' ≤ bb := by rw [hbb']; exact Nat.mod_le bb (2 ^ E.W)
  have habW' : ab' < 2 ^ E.W := by
    rw [hab']; exact Nat.mod_lt ab (Nat.two_pow_pos E.W)
  have hbbW' : bb' < 2 ^ E.W := by
    rw [hbb']; exact Nat.mod_lt bb (Nat.two_pow_pos E.W)
  have hdA' : ab' + al ≤ ob ∨ ob + (al + bl) ≤ ab' := by
    rcases Nat.lt_or_ge ab (2 ^ E.W) with h | h
    · rw [hab', Nat.mod_eq_of_lt h]; exact hdA
    · have he : ab = 2 ^ E.W := by omega
      have hl0 : al = 0 := by omega
      rw [hab', he, Nat.mod_self, hl0]
      omega
  have hdB' : bb' + bl ≤ ob ∨ ob + (al + bl) ≤ bb' := by
    rcases Nat.lt_or_ge bb (2 ^ E.W) with h | h
    · rw [hbb', Nat.mod_eq_of_lt h]; exact hdB
    · have he : bb = 2 ^ E.W := by omega
      have hl0 : bl = 0 := by omega
      rw [hbb', he, Nat.mod_self, hl0]
      omega
  have hvA' : ∀ p, p < al → s.mem (ab' + p) < 2 ^ E.W := by
    rcases Nat.lt_or_ge ab (2 ^ E.W) with h | h
    · have he : ab' = ab := by rw [hab', Nat.mod_eq_of_lt h]
      rw [he]; exact hvA
    · have he : ab = 2 ^ E.W := by omega
      have hl0 : al = 0 := by omega
      intro p hp; omega
  have hvB' : ∀ p, p < bl → s.mem (bb' + p) < 2 ^ E.W := by
    rcases Nat.lt_or_ge bb (2 ^ E.W) with h | h
    · have he : bb' = bb := by rw [hbb', Nat.mod_eq_of_lt h]
      rw [he]; exact hvB
    · have he : bb = 2 ^ E.W := by omega
      have hl0 : bl = 0 := by omega
      intro p hp; omega
  have hstep := mrgStep_state (P := P) (E := E) (base := base) (ab := ab') (al := al)
    (bb := bb') (bl := bl) (ob := ob) hAt hW hpc h10' h11' h12' h13' h14'
    habW' halW hbbW' hblW hobW (by omega) (by omega) hob hdA' hdB' hvA' hvB'
  rw [mrgEnd_eq] at hstep
  refine Sem.mono hstep ?_
  intro k s' h
  obtain ⟨hk, rfl⟩ := h
  refine ⟨hk, ?_⟩
  rw [mrgFin_out _ _ _ _ _ _ _ hdA' hdB']
  have hlistA : mList s.mem ab' al = mList s.mem ab al := by
    rw [hab']
    exact mList_mod s.mem ab al E.W (by omega) halW
  have hlistB : mList s.mem bb' bl = mList s.mem bb bl := by
    rw [hbb']
    exact mList_mod s.mem bb bl E.W (by omega) hblW
  rw [hlistA, hlistB]

/-- **`SmergeRunsM`, proved**: the contract of the repaired merge follows from `mrgStep_sem`. -/
theorem smergeRunsM_of_at {P : Program} {E : RAMEnv} {base ab al bb bl ob : ℕ}
    (hAt : At P base (mrgStmtFull.compile base)) (hW : 1 < 2 ^ E.W) :
    SmergeRunsM P E base ab al bb bl ob := by
  intro s hpc hregs hndA hndB hvA hvB hal hbl hab hbb hob hdA hdB
  obtain ⟨h10, h11, h12, h13, h14⟩ := hregs
  obtain ⟨-, k, s', hstep, hb, hk, hout⟩ :=
    mrgStep_sem hAt hW hpc h10 h11 h12 h13 h14 hal hbl hab hbb hob hdA hdB hvA hvB
  exact ⟨k, s', by exact_mod_cast hk, hstep, hb, hout⟩

/-! ### 8.3 Non-vacuity: two concrete runs -/

/-- The merge program, compiled at `0`, followed by the trailing `halt`. -/
def mrgProg : Program := mrgStmtFull.compile 0 ++ [iHalt]

/-- An eight-bit environment with the all-zero query table. -/
def mrgEnv8 : RAMEnv := ⟨8, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩

/-- The entry registers: `r10 … r14` carry `ab, al, bb, bl, ob`. -/
def mrgIn (ab al bb bl ob : ℕ) : Fin 16 → ℕ :=
  fun d => if d = r10 then ab else if d = r11 then al else if d = r12 then bb else
    if d = r13 then bl else if d = r14 then ob else 0

theorem mrgProg_at : At mrgProg 0 (mrgStmtFull.compile 0) := by
  intro r hr
  rw [Nat.zero_add]
  show (mrgStmtFull.compile 0 ++ [iHalt])[r]? = (mrgStmtFull.compile 0)[r]?
  rw [List.getElem?_append_left (by simpa using hr)]

theorem mrgIn_r10 (ab al bb bl ob : ℕ) : mrgIn ab al bb bl ob r10 = ab := by simp [mrgIn]
theorem mrgIn_r11 (ab al bb bl ob : ℕ) : mrgIn ab al bb bl ob r11 = al := by simp [mrgIn]
theorem mrgIn_r12 (ab al bb bl ob : ℕ) : mrgIn ab al bb bl ob r12 = bb := by simp [mrgIn]
theorem mrgIn_r13 (ab al bb bl ob : ℕ) : mrgIn ab al bb bl ob r13 = bl := by simp [mrgIn]
theorem mrgIn_r14 (ab al bb bl ob : ℕ) : mrgIn ab al bb bl ob r14 = ob := by simp [mrgIn]

def mrgW1mem : ℕ → ℕ := fun a => if a = 10 then 5 else if a = 20 then 7 else 0

theorem mrgW1mem_10 : mrgW1mem 10 = 5 := by decide
theorem mrgW1mem_20 : mrgW1mem 20 = 7 := by decide

def mrgW2mem : ℕ → ℕ :=
  fun a => if a = 10 then 5 else if a = 20 then 5 else if a = 21 then 7 else 0

theorem mrgW2mem_10 : mrgW2mem 10 = 5 := by decide
theorem mrgW2mem_20 : mrgW2mem 20 = 5 := by decide
theorem mrgW2mem_21 : mrgW2mem 21 = 7 := by decide

/-- **Non-vacuity, first witness**: A = [5], B = [7], and the run produces [5, 7]. -/
theorem smergeRunsM_witness_5_7 :
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ mrgCost 1 1 ∧
      (step mrgProg mrgEnv8)^[k] { pc := 0, regs := mrgIn 10 1 20 1 40, mem := mrgW1mem } = s' ∧
      s'.pc = 0 + mrgStmtFull.len ∧ outList s' = [5, 7] := by
  have hcont := smergeRunsM_of_at (P := mrgProg) (E := mrgEnv8) (base := 0) (ab := 10) (al := 1)
    (bb := 20) (bl := 1) (ob := 40) mrgProg_at (by decide)
    { pc := 0, regs := mrgIn 10 1 20 1 40, mem := mrgW1mem } rfl
    (by simp [mrgIn]) (by decide) (by decide)
    (by intro p hp
        have hp0 : p = 0 := by omega
        rw [hp0]
        show mrgW1mem (10 + 0) < 2 ^ mrgEnv8.W
        rw [Nat.add_zero, mrgW1mem_10]
        decide)
    (by intro p hp
        have hp0 : p = 0 := by omega
        rw [hp0]
        show mrgW1mem (20 + 0) < 2 ^ mrgEnv8.W
        rw [Nat.add_zero, mrgW1mem_20]
        decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k, s', hk, hstep, hpc, hout⟩ := hcont
  exact ⟨k, s', hk, hstep, hpc, by rw [hout]; decide⟩

/-- **Non-vacuity, second witness**: A = [5] and B = [5, 7]; the run produces [7], i.e. the
symmetric difference, not the union. -/
theorem smergeRunsM_witness_5_57 :
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ mrgCost 1 2 ∧
      (step mrgProg mrgEnv8)^[k] { pc := 0, regs := mrgIn 10 1 20 2 40, mem := mrgW2mem } = s' ∧
      s'.pc = 0 + mrgStmtFull.len ∧ outList s' = [7] := by
  have hcont := smergeRunsM_of_at (P := mrgProg) (E := mrgEnv8) (base := 0) (ab := 10) (al := 1)
    (bb := 20) (bl := 2) (ob := 40) mrgProg_at (by decide)
    { pc := 0, regs := mrgIn 10 1 20 2 40, mem := mrgW2mem } rfl
    (by simp [mrgIn]) (by decide) (by decide)
    (by intro p hp
        have hp0 : p = 0 := by omega
        rw [hp0]
        show mrgW2mem (10 + 0) < 2 ^ mrgEnv8.W
        rw [Nat.add_zero, mrgW2mem_10]
        decide)
    (by intro p hp
        interval_cases p
        · show mrgW2mem (20 + 0) < 2 ^ mrgEnv8.W
          rw [Nat.add_zero, mrgW2mem_20]; decide
        · show mrgW2mem (20 + 1) < 2 ^ mrgEnv8.W
          rw [mrgW2mem_21]; decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k, s', hk, hstep, hpc, hout⟩ := hcont
  exact ⟨k, s', hk, hstep, hpc, by rw [hout]; decide⟩


/-! ### 8.4 The merge as a StageRun -/

/-- **The merge StageRun.**  This is the form Theorem 6.5's cr stage consumes: from any entry
state that carries the decoded x̂ at [ab, ab+al) and the residual ê at [bb, bb+bl)
(and puts b, al, bb, bl, ob in 
10 … r14), the merge reaches ase + 86 in at most
mrgCost al bl steps, leaving a duplicate-free output whose value set is x̂ △ ê. -/
theorem mergeStageRun {P : Program} {E : RAMEnv} {base ab al bb bl ob : ℕ} (A B : List ℕ)
    (hAt : At P base (mrgStmtFull.compile base)) (hW : 1 < 2 ^ E.W) :
    StageRun P E base (base + mrgStmtFull.len) (mrgCost al bl)
      (fun s => s.regs r10 = ab ∧ s.regs r11 = al ∧ s.regs r12 = bb ∧ s.regs r13 = bl ∧
        s.regs r14 = ob ∧
        mList s.mem ab al = A ∧ mList s.mem bb bl = B ∧
        A.Nodup ∧ B.Nodup ∧
        (∀ p, p < al → s.mem (ab + p) < 2 ^ E.W) ∧
        (∀ p, p < bl → s.mem (bb + p) < 2 ^ E.W) ∧
        al < 2 ^ E.W ∧ bl < 2 ^ E.W ∧
        ab + al ≤ 2 ^ E.W ∧ bb + bl ≤ 2 ^ E.W ∧
        ob + (al + bl) + 1 < 2 ^ E.W ∧
        (ab + al ≤ ob ∨ ob + (al + bl) ≤ ab) ∧ (bb + bl ≤ ob ∨ ob + (al + bl) ≤ bb))
      (fun s' => (outList s').Nodup ∧
        (outList s').toFinset = symmDiff A.toFinset B.toFinset) := by
  intro s hpc hI
  obtain ⟨h10, h11, h12, h13, h14, hA, hB, hndA, hndB, hvA, hvB, hal, hbl, hab, hbb, hob, hdA, hdB⟩ := hI
  obtain ⟨-, k, s', hstep, hb, hk, hout⟩ :=
    mrgStep_sem hAt hW hpc h10 h11 h12 h13 h14 hal hbl hab hbb hob hdA hdB hvA hvB
  have hAlen : A.length = al := by rw [← hA, mList_length]
  have hBlen : B.length = bl := by rw [← hB, mList_length]
  refine ⟨k, s', by exact_mod_cast hk, hstep, hb, ?_, ?_⟩
  · rw [hout, hA, hB, ← hAlen, ← hBlen]
    exact merge_out_nodup A B hndA hndB
  · rw [hout, hA, hB, ← hAlen, ← hBlen]
    exact merge_out_toFinset A B

end RMR
end LinearSetReconciliation327.Main


