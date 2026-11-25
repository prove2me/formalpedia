-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_02
-- name    : LinearSetReconciliation327_Main_B65_02
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-25T01:04:59.942003+00:00
-- url     : https://prove2.me/theorems/97ad468f-fdf1-4853-b498-cf5a7ee07158
-- title:
--   Theorem 6.5 dependency bundle 02
-- statement:
--   Theorem 6.5 dependency bundle 02
-- source:
--   arXiv:2611.11409, Theorem 6.5 dependency closure (bundled for publication).

import Definitions.Def_LinearSetReconciliation327_Main_B65_01
set_option autoImplicit false

section S_HintRhsQuery20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRhsQueryFields : List (Fin 16 × ℕ) :=
  [(4, 4), (6, 0), (10, 10), (5, 11), (8, 13), (7, 12), (11, 15)]
def hintRhsQueryTail : List Instr :=
  [.mul 5 5 8, .mul 5 5 7, .imm 15 1, .add 3 11 12, .add 3 3 15, .load 9 3, .add 5 5 9]
def hintRhsQuerySetup : List Instr := hintLoadFields hintRhsQueryFields ++ hintRhsQueryTail
theorem hintRhsQuerySetup_length : hintRhsQuerySetup.length = 28 := rfl

theorem hintRhsQueryTail_spec (E : RAMEnv) (state : RAMState)
    (dest count buckets key row steps outsideBase index outsideCount context : ℕ) (v : Fin buckets)
    (hWord : 1 < 2 ^ E.W) (hBuckets : buckets < 2 ^ E.W)
    (hOutsideAddr : outsideBase + 1 + index < 2 ^ E.W)
    (hOffset : row * steps * buckets + v.val < 2 ^ E.W)
    (h4 : state.regs 4 = dest) (h6 : state.regs 6 = count) (h7 : state.regs 7 = buckets)
    (h10 : state.regs 10 = key) (h5 : state.regs 5 = row) (h8 : state.regs 8 = steps)
    (h11 : state.regs 11 = outsideBase) (h12 : state.regs 12 = index)
    (h13 : state.regs 13 = outsideCount) (h14 : state.regs 14 = context)
    (hOutside : state.mem (outsideBase + 1 + index) = v.val) :
    let out := runBlock hintRhsQueryTail E state
    HintCoeffCopyParams dest (row * steps * buckets + v.val) buckets count key out ∧
      out.mem = state.mem ∧ out.regs 12 = index ∧ out.regs 13 = outsideCount ∧ out.regs 14 = context := by
  have hPositive : 0 < buckets := by have := v.isLt; omega
  have hMulLe : row * steps ≤ row * steps * buckets := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (row * steps) (Nat.succ_le_of_lt hPositive)
  have hFirst : row * steps < 2 ^ E.W := by omega
  have hSecond : row * steps * buckets < 2 ^ E.W := by omega
  have hV : v.val < 2 ^ E.W := v.isLt.trans hBuckets
  have hAdd : outsideBase + index < 2 ^ E.W := by omega
  have hAddr : outsideBase + index + 1 < 2 ^ E.W := by omega
  have hRead : state.mem (outsideBase + index + 1) = v.val := by
    rw [show outsideBase + index + 1 = outsideBase + 1 + index from by omega]
    exact hOutside
  dsimp only
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp [hintRhsQueryTail, runBlock, execInstr, h4, h6, h7, h10, h5, h8, h11, h12, h13, h14,
      hRead, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hAdd, Nat.mod_eq_of_lt hAddr,
      Nat.mod_eq_of_lt hFirst, Nat.mod_eq_of_lt hSecond, Nat.mod_eq_of_lt hV, Nat.mod_eq_of_lt hOffset]

theorem hintRhsQuerySetup_spec (E : RAMEnv) (G : HintGaussArea) (r : ℕ) (j : Fin r)
    (outsideBase : ℕ) (v : Fin G.buckets) (state : RAMState)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context) (hCounter : state.regs 12 = j.val) (hCount : state.regs 13 = r)
    (hPointer : state.mem (G.context + 15) = outsideBase)
    (hOutsideSpan : outsideBase + 1 + r ≤ G.hintList)
    (hOutside : state.mem (outsideBase + 1 + j.val) = v.val)
    (hOffset : G.row * G.steps * G.buckets + v.val < 2 ^ E.W) :
    let out := runBlock hintRhsQuerySetup E state
    HintCoeffCopyParams G.column (G.row * G.steps * G.buckets + v.val) G.buckets G.rows G.node out ∧
      out.mem = state.mem ∧ out.regs 12 = j.val ∧ out.regs 13 = r ∧ out.regs 14 = G.context := by
  have hWord := hGeometry.word_bound
  have h0 := hGeometry.residual_before
  have h1 := hGeometry.lift_before
  have h2 := hGeometry.column_before
  have h3 := hGeometry.residualVec_before
  have h4 := hGeometry.kernelVec_before
  have h5 := hGeometry.span
  have hHintList : G.hintList < 2 ^ E.W := hFits.values 9 (by decide)
  have hBase : outsideBase < 2 ^ E.W := by omega
  have hValid : ∀ pair ∈ hintRhsQueryFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintRhsQueryFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by omega⟩
  have hLoad := hintLoadFields_spec E G.context hintRhsQueryFields state hContext hValid
  have hValues := hintGaussHeader_mod E G 0 state.mem hHeader hFits
  generalize hMid : runBlock (hintLoadFields hintRhsQueryFields) E state = mid at hLoad
  have hZero : state.mem G.context % 2 ^ E.W = hintGaussHeaderValue G 0 0 := by
    simpa only [Nat.add_zero] using hValues 0 (by decide)
  have hFifteen : state.mem (G.context + 15) % 2 ^ E.W = outsideBase := by
    rw [hPointer, Nat.mod_eq_of_lt hBase]
  have hR4 : mid.regs 4 = hintGaussHeaderValue G 0 4 := by
    simpa [hintRhsQueryFields, hintLoadedValue, hZero, hFifteen,
      hValues 4 (by decide), hValues 10 (by decide), hValues 11 (by decide),
      hValues 12 (by decide), hValues 13 (by decide)] using hLoad.2.2.2 4 (by decide)
  have hR6 : mid.regs 6 = hintGaussHeaderValue G 0 0 := by
    simpa [hintRhsQueryFields, hintLoadedValue, hZero, hFifteen,
      hValues 4 (by decide), hValues 10 (by decide), hValues 11 (by decide),
      hValues 12 (by decide), hValues 13 (by decide)] using hLoad.2.2.2 6 (by decide)
  have hR10 : mid.regs 10 = hintGaussHeaderValue G 0 10 := by
    simpa [hintRhsQueryFields, hintLoadedValue, hZero, hFifteen,
      hValues 4 (by decide), hValues 10 (by decide), hValues 11 (by decide),
      hValues 12 (by decide), hValues 13 (by decide)] using hLoad.2.2.2 10 (by decide)
  have hR5 : mid.regs 5 = hintGaussHeaderValue G 0 11 := by
    simpa [hintRhsQueryFields, hintLoadedValue, hZero, hFifteen,
      hValues 4 (by decide), hValues 10 (by decide), hValues 11 (by decide),
      hValues 12 (by decide), hValues 13 (by decide)] using hLoad.2.2.2 5 (by decide)
  have hR8 : mid.regs 8 = hintGaussHeaderValue G 0 13 := by
    simpa [hintRhsQueryFields, hintLoadedValue, hZero, hFifteen,
      hValues 4 (by decide), hValues 10 (by decide), hValues 11 (by decide),
      hValues 12 (by decide), hValues 13 (by decide)] using hLoad.2.2.2 8 (by decide)
  have hR7 : mid.regs 7 = hintGaussHeaderValue G 0 12 := by
    simpa [hintRhsQueryFields, hintLoadedValue, hZero, hFifteen,
      hValues 4 (by decide), hValues 10 (by decide), hValues 11 (by decide),
      hValues 12 (by decide), hValues 13 (by decide)] using hLoad.2.2.2 7 (by decide)
  have hR11 : mid.regs 11 = outsideBase := by
    simpa [hintRhsQueryFields, hintLoadedValue, hFifteen] using hLoad.2.2.2 11 (by decide)
  have hR12 : mid.regs 12 = j.val := by
    simpa [hintRhsQueryFields, hintLoadedValue, hCounter] using hLoad.2.2.2 12 (by decide)
  have hR13 : mid.regs 13 = r := by
    simpa [hintRhsQueryFields, hintLoadedValue, hCount] using hLoad.2.2.2 13 (by decide)
  have hOutside' : mid.mem (outsideBase + 1 + j.val) = v.val := by rw [hLoad.2.1]; exact hOutside
  have hTail := hintRhsQueryTail_spec E mid G.column G.rows G.buckets G.node G.row G.steps outsideBase j.val r G.context v
    hWord (hFits.values 12 (by decide)) (by have := j.isLt; omega) hOffset
    hR4 hR6 hR7 hR10 hR5 hR8 hR11 hR12 hR13 hLoad.2.2.1 hOutside'
  dsimp only
  rw [hintRhsQuerySetup, runBlock_append, hMid]
  exact ⟨hTail.1, hTail.2.1.trans hLoad.2.1, hTail.2.2.1, hTail.2.2.2.1, hTail.2.2.2.2⟩

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintRhsQueryStmt : Stmt := .seq (.code hintRhsQuerySetup) hintCoeffCopyStmt
theorem hintRhsQueryStmt_len : hintRhsQueryStmt.len = 38 := rfl

theorem hintRhsQueryStmt_sem (G : HintGaussArea) (r : ℕ) (j : Fin r) (outsideBase : ℕ)
    (v : Fin G.buckets) (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context) (hCounter : state.regs 12 = j.val) (hCount : state.regs 13 = r)
    (hPointer : state.mem (G.context + 15) = outsideBase)
    (hOutsideSpan : outsideBase + 1 + r ≤ G.hintList)
    (hOutside : state.mem (outsideBase + 1 + j.val) = v.val)
    (hOffset : G.row * G.steps * G.buckets + v.val < 2 ^ E.W)
    (hQuerySpan : ∀ s < G.rows, G.row * G.steps * G.buckets + v.val + s * G.buckets < 2 ^ E.W)
    (hCoeff : ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + v.val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ v).val)
    (hAt : At P base (hintRhsQueryStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 38) state (fun k out => k = 9 * G.rows + 31 ∧
      (∀ s : Fin G.rows, out.mem (G.column + s.val) = (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ v).val) ∧
      CRMemFrame G.column (G.column + G.rows) state.mem out.mem ∧ HintGaussHeader G 0 out.mem ∧
      out.mem (G.context + 15) = outsideBase ∧ out.regs 12 = j.val ∧ out.regs 13 = r ∧
      out.regs 14 = G.context ∧
      HintCoeffCopyParams G.column (G.row * G.steps * G.buckets + v.val) G.buckets G.rows G.node out) := by
  have hWord := hGeometry.word_bound
  have hWidth := hGeometry.width_bound
  have h0 := hGeometry.residual_before
  have h1 := hGeometry.lift_before
  have h2 := hGeometry.column_before
  have h3 := hGeometry.residualVec_before
  have h4 := hGeometry.kernelVec_before
  have h5 := hGeometry.span
  obtain ⟨hSetupAt, hBodyAt⟩ := At.seqStmt hAt
  change At P base hintRhsQuerySetup at hSetupAt
  change At P (base + 28) (hintCoeffCopyStmt.compile (base + 28)) at hBodyAt
  have hNo : NoBranch hintRhsQuerySetup := by
    rw [hintRhsQuerySetup, upNoBranch_append]
    exact ⟨hintLoadFields_noBranch _, by simp [hintRhsQueryTail, NoBranch, Instr.NoBranchI]⟩
  have hSetup := hintRhsQuerySetup_spec E G r j outsideBase v state hGeometry hReserve hHeader hFits hContext
    hCounter hCount hPointer hOutsideSpan hOutside hOffset
  generalize hMid : runBlock hintRhsQuerySetup E state = mid at hSetup
  obtain ⟨hArgs, hMem, h12, h13, h14⟩ := hSetup
  have hRunSetup : (step P E)^[28] state = mid := by
    have hh := iterate_runBlock_of_at P E hintRhsQuerySetup state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hMidPc : mid.pc = base + 28 := by
    have hh := runBlock_pc hintRhsQuerySetup E state hNo
    rw [hMid, hPc] at hh
    exact hh
  let vec : HintVec G.rows := fun s => beta ⟨s.val, s.isLt.trans_le hPrefix⟩ v
  have hCoeff' : ∀ s < G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + v.val + s * G.buckets) = (hintDenseVec vec s).val := by
    intro s hs
    simpa only [hintDenseVec, dif_pos hs] using hCoeff ⟨s, hs⟩
  obtain ⟨_, kBody, out, hRunBody, hOutPc, hCost, _, hOutMem, hOutArgs, hFrame, hRegs⟩ :=
    hintCoeffCopyStmt_sem P E mid G.column (G.row * G.steps * G.buckets + v.val) G.buckets G.rows G.node
      (base + 28) (hintDenseVec vec) hWord hWidth (by intro s hs; omega) hQuerySpan hCoeff' hBodyAt hMidPc hArgs
  have hFrame' : CRMemFrame G.column (G.column + G.rows) state.mem out.mem := by
    intro addr hOutside
    exact (hFrame addr hOutside).trans (congrFun hMem addr)
  refine ⟨hPc, kBody + 28, out, hintIterate_then (step P E) hRunSetup hRunBody, ?_, by omega,
    ?_, hFrame', ?_, ?_, ?_, ?_, ?_, hOutArgs⟩
  · simpa only [Nat.add_assoc] using hOutPc
  · intro s
    rw [hOutMem]
    have hRange : G.column ≤ G.column + s.val ∧ G.column + s.val < G.column + G.rows := by have := s.isLt; omega
    simp only [hintCopyMem, hintAxpyMem, if_pos hRange, Nat.add_sub_cancel_left, zero_mul, add_zero,
      hintDenseVec, dif_pos s.isLt]
    rfl
  · exact hintGaussHeader_of_frame G 0 G.column (G.column + G.rows) state.mem out.mem hHeader hFrame' (Or.inl (by omega))
  · rw [hFrame' _ (Or.inl (by omega))]
    exact hPointer
  · exact (hRegs 12 (by decide) (by decide) (by decide) (by decide)).trans h12
  · exact (hRegs 13 (by decide) (by decide) (by decide) (by decide)).trans h13
  · exact (hRegs 14 (by decide) (by decide) (by decide) (by decide)).trans h14

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRhsQueryStmt_sem
end S_HintRhsQuery20261120
section S_HintRhsPrimitives20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRhsEntry : List Instr := hintLoadField 11 15 ++ [.load 13 11, .imm 12 0]
theorem hintRhsEntry_length : hintRhsEntry.length = 5 := rfl

theorem hintRhsEntry_spec (E : RAMEnv) (G : HintGaussArea) (r outsideBase : ℕ) (state : RAMState)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hFits : HintGaussHeaderFits E G 0) (hContext : state.regs 14 = G.context)
    (hPointer : state.mem (G.context + 15) = outsideBase) (hCount : state.mem outsideBase = r)
    (hOutsideSpan : outsideBase + 1 + r ≤ G.hintList) :
    let out := runBlock hintRhsEntry E state
    out.pc = state.pc + 5 ∧ out.mem = state.mem ∧ out.regs 12 = 0 ∧ out.regs 13 = r ∧ out.regs 14 = G.context := by
  have h0 := hGeometry.residual_before
  have h1 := hGeometry.lift_before
  have h2 := hGeometry.column_before
  have h3 := hGeometry.residualVec_before
  have h4 := hGeometry.kernelVec_before
  have h5 := hGeometry.span
  have hHintList : G.hintList < 2 ^ E.W := hFits.values 9 (by decide)
  have hBase : outsideBase < 2 ^ E.W := by omega
  have hR : r < 2 ^ E.W := by omega
  have hRead := hintLoadField_spec E state 11 15 G.context hContext (by omega)
  generalize hMid : runBlock (hintLoadField 11 15) E state = mid at hRead
  have h11 : mid.regs 11 = outsideBase := by rw [hRead.2.2.1, hPointer, Nat.mod_eq_of_lt hBase]
  have hCountMid : mid.mem outsideBase = r := by rw [hRead.2.1]; exact hCount
  have h14 : mid.regs 14 = G.context := (hRead.2.2.2 14 (by decide) (by decide)).trans hContext
  dsimp only
  rw [hintRhsEntry, runBlock_append, hMid]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [runBlock, execInstr, h11, h14, hCountMid, hRead.1, hRead.2.1, Nat.mod_eq_of_lt hBase, Nat.mod_eq_of_lt hR, Nat.add_assoc]

def hintRhsCloneFields : List (Fin 16 × ℕ) := [(4, 9), (5, 1), (6, 0)]
def hintRhsCloneTail : List Instr := [.add 4 4 5, .add 5 4 6, .imm 7 1, .imm 15 1]
def hintRhsCloneSetup : List Instr := hintLoadFields hintRhsCloneFields ++ hintRhsCloneTail
theorem hintRhsCloneSetup_length : hintRhsCloneSetup.length = 13 := rfl

theorem hintRhsCloneSetup_spec (E : RAMEnv) (G : HintGaussArea) (state : RAMState)
    (hGeometry : HintGaussGeometry E G) (hHeader : HintGaussHeader G 0 state.mem)
    (hFits : HintGaussHeaderFits E G 0) (hContext : state.regs 14 = G.context)
    (hSource : G.hintList + G.hints + 2 * G.rows ≤ G.context) :
    let out := runBlock hintRhsCloneSetup E state
    HintCopyParams (G.hintList + G.hints) (G.hintList + G.hints + G.rows) 1 G.rows out ∧
      out.mem = state.mem ∧ out.regs 12 = state.regs 12 ∧ out.regs 13 = state.regs 13 ∧ out.regs 14 = G.context := by
  have hWord := hGeometry.word_bound
  have h0 := hGeometry.header_before
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  have h3 := hGeometry.column_before
  have h4 := hGeometry.residualVec_before
  have h5 := hGeometry.kernelVec_before
  have h6 := hGeometry.span
  have hDest : G.hintList + G.hints < 2 ^ E.W := by omega
  have hBackup : G.hintList + G.hints + G.rows < 2 ^ E.W := by omega
  have hValid : ∀ pair ∈ hintRhsCloneFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintRhsCloneFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨by decide, by have := hFits.span; omega⟩
  have hLoad := hintLoadFields_spec E G.context hintRhsCloneFields state hContext hValid
  have hValues := hintGaussHeader_mod E G 0 state.mem hHeader hFits
  generalize hMid : runBlock (hintLoadFields hintRhsCloneFields) E state = mid at hLoad
  have hZero : state.mem G.context % 2 ^ E.W = hintGaussHeaderValue G 0 0 := by
    simpa only [Nat.add_zero] using hValues 0 (by decide)
  have hR4 : mid.regs 4 = hintGaussHeaderValue G 0 9 := by
    simpa [hintRhsCloneFields, hintLoadedValue, hZero, hValues 1 (by decide), hValues 9 (by decide)] using hLoad.2.2.2 4 (by decide)
  have hR5 : mid.regs 5 = hintGaussHeaderValue G 0 1 := by
    simpa [hintRhsCloneFields, hintLoadedValue, hZero, hValues 1 (by decide), hValues 9 (by decide)] using hLoad.2.2.2 5 (by decide)
  have hR6 : mid.regs 6 = hintGaussHeaderValue G 0 0 := by
    simpa [hintRhsCloneFields, hintLoadedValue, hZero, hValues 1 (by decide), hValues 9 (by decide)] using hLoad.2.2.2 6 (by decide)
  have hR12 : mid.regs 12 = state.regs 12 := by
    simpa [hintRhsCloneFields, hintLoadedValue] using hLoad.2.2.2 12 (by decide)
  have hR13 : mid.regs 13 = state.regs 13 := by
    simpa [hintRhsCloneFields, hintLoadedValue] using hLoad.2.2.2 13 (by decide)
  dsimp only
  rw [hintRhsCloneSetup, runBlock_append, hMid]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp [hintRhsCloneTail, runBlock, execInstr, hR4, hR5, hR6, hR12, hR13, hintGaussHeaderValue,
      Nat.mod_eq_of_lt hDest, Nat.mod_eq_of_lt hBackup, Nat.mod_eq_of_lt hWord, hLoad.2.1, hLoad.2.2.1]

def hintRhsAxpyFields : List (Fin 16 × ℕ) := [(4, 9), (8, 1), (5, 4)]
def hintRhsAxpyTail : List Instr := [.add 4 4 8, .imm 8 1]
def hintRhsAxpySetup : List Instr := hintLoadFields hintRhsAxpyFields ++ hintRhsAxpyTail
theorem hintRhsAxpySetup_length : hintRhsAxpySetup.length = 11 := rfl

theorem hintRhsAxpySetup_spec (E : RAMEnv) (G : HintGaussArea) (state : RAMState)
    (hGeometry : HintGaussGeometry E G) (hHeader : HintGaussHeader G 0 state.mem)
    (hFits : HintGaussHeaderFits E G 0) (hContext : state.regs 14 = G.context)
    (hSource : G.hintList + G.hints + 2 * G.rows ≤ G.context)
    (hCount : state.regs 6 = G.rows) (hOne : state.regs 15 = 1) :
    let out := runBlock hintRhsAxpySetup E state
    HintAxpyParams (G.hintList + G.hints) G.column G.rows 1 out ∧ out.mem = state.mem ∧
      out.regs 12 = state.regs 12 ∧ out.regs 13 = state.regs 13 ∧ out.regs 14 = G.context := by
  have hWord := hGeometry.word_bound
  have h0 := hGeometry.header_before
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  have h3 := hGeometry.column_before
  have h4 := hGeometry.residualVec_before
  have h5 := hGeometry.kernelVec_before
  have h6 := hGeometry.span
  have hDest : G.hintList + G.hints < 2 ^ E.W := by omega
  have hValid : ∀ pair ∈ hintRhsAxpyFields, pair.1 ≠ 14 ∧ G.context + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [hintRhsAxpyFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨by decide, by have := hFits.span; omega⟩
  have hLoad := hintLoadFields_spec E G.context hintRhsAxpyFields state hContext hValid
  have hValues := hintGaussHeader_mod E G 0 state.mem hHeader hFits
  generalize hMid : runBlock (hintLoadFields hintRhsAxpyFields) E state = mid at hLoad
  have hR4 : mid.regs 4 = hintGaussHeaderValue G 0 9 := by
    simpa [hintRhsAxpyFields, hintLoadedValue, hValues 1 (by decide), hValues 4 (by decide), hValues 9 (by decide)] using hLoad.2.2.2 4 (by decide)
  have hR8 : mid.regs 8 = hintGaussHeaderValue G 0 1 := by
    simpa [hintRhsAxpyFields, hintLoadedValue, hValues 1 (by decide), hValues 4 (by decide), hValues 9 (by decide)] using hLoad.2.2.2 8 (by decide)
  have hR5 : mid.regs 5 = hintGaussHeaderValue G 0 4 := by
    simpa [hintRhsAxpyFields, hintLoadedValue, hValues 1 (by decide), hValues 4 (by decide), hValues 9 (by decide)] using hLoad.2.2.2 5 (by decide)
  have hR6 : mid.regs 6 = G.rows := by
    simpa [hintRhsAxpyFields, hintLoadedValue, hCount] using hLoad.2.2.2 6 (by decide)
  have hR15 : mid.regs 15 = 1 := by
    simpa [hintRhsAxpyFields, hintLoadedValue, hOne] using hLoad.2.2.2 15 (by decide)
  have hR12 : mid.regs 12 = state.regs 12 := by
    simpa [hintRhsAxpyFields, hintLoadedValue] using hLoad.2.2.2 12 (by decide)
  have hR13 : mid.regs 13 = state.regs 13 := by
    simpa [hintRhsAxpyFields, hintLoadedValue] using hLoad.2.2.2 13 (by decide)
  dsimp only
  rw [hintRhsAxpySetup, runBlock_append, hMid]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp [hintRhsAxpyTail, runBlock, execInstr, hR4, hR8, hR5, hR6, hR12, hR13, hR15, hintGaussHeaderValue,
      Nat.mod_eq_of_lt hDest, Nat.mod_eq_of_lt hWord, hLoad.2.1, hLoad.2.2.1,
      show (1 : ZMod 2).val = 1 from rfl]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintRhsCloneStmt : Stmt := .seq (.code hintRhsCloneSetup) hintCopyStmt
theorem hintRhsCloneStmt_len : hintRhsCloneStmt.len = 23 := rfl

theorem hintRhsCloneStmt_sem (G : HintGaussArea) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hSource : G.hintList + G.hints + 2 * G.rows ≤ G.context)
    (hVector : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + G.rows + s.val) = (v s).val)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context)
    (hAt : At P base (hintRhsCloneStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 23) state (fun k out => k = 9 * G.rows + 16 ∧
      (∀ s : Fin G.rows, out.mem (G.hintList + G.hints + s.val) = (v s).val) ∧
      CRMemFrame (G.hintList + G.hints) (G.hintList + G.hints + G.rows) state.mem out.mem ∧
      HintGaussHeader G 0 out.mem ∧ out.regs 12 = state.regs 12 ∧ out.regs 13 = state.regs 13 ∧ out.regs 14 = G.context) := by
  have hWord := hGeometry.word_bound
  have hWidth := hGeometry.width_bound
  have h0 := hGeometry.header_before
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  have h3 := hGeometry.column_before
  have h4 := hGeometry.residualVec_before
  have h5 := hGeometry.kernelVec_before
  have h6 := hGeometry.span
  obtain ⟨hSetupAt, hBodyAt⟩ := At.seqStmt hAt
  change At P base hintRhsCloneSetup at hSetupAt
  change At P (base + 13) (hintCopyStmt.compile (base + 13)) at hBodyAt
  have hNo : NoBranch hintRhsCloneSetup := by
    rw [hintRhsCloneSetup, upNoBranch_append]
    exact ⟨hintLoadFields_noBranch _, by simp [hintRhsCloneTail, NoBranch, Instr.NoBranchI]⟩
  have hSetup := hintRhsCloneSetup_spec E G state hGeometry hHeader hFits hContext hSource
  generalize hMid : runBlock hintRhsCloneSetup E state = mid at hSetup
  obtain ⟨hArgs, hMem, h12, h13, h14⟩ := hSetup
  have hRunSetup : (step P E)^[13] state = mid := by
    have hh := iterate_runBlock_of_at P E hintRhsCloneSetup state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hMidPc : mid.pc = base + 13 := by
    have hh := runBlock_pc hintRhsCloneSetup E state hNo
    rw [hMid, hPc] at hh
    exact hh
  have hVector' : ∀ s < G.rows,
      mid.mem (G.hintList + G.hints + G.rows + s * 1) = (hintDenseVec v s).val := by
    intro s hs
    rw [hMem]
    simpa only [hintDenseVec, dif_pos hs, Nat.mul_one] using hVector ⟨s, hs⟩
  obtain ⟨_, kBody, out, hRunBody, hOutPc, hCost, _, hOutMem, _, hFrame, hRegs⟩ :=
    hintCopyStmt_sem P E mid (G.hintList + G.hints) (G.hintList + G.hints + G.rows) 1 G.rows (base + 13) (hintDenseVec v)
      hWord hWidth (by intro s hs; omega) (by intro s hs; simp only [Nat.mul_one]; omega)
      (by intro s hs; simp only [Nat.mul_one]; exact Or.inr (by omega)) hVector' hBodyAt hMidPc hArgs
  have hFrame' : CRMemFrame (G.hintList + G.hints) (G.hintList + G.hints + G.rows) state.mem out.mem := by
    intro addr hOutside
    exact (hFrame addr hOutside).trans (congrFun hMem addr)
  refine ⟨hPc, kBody + 13, out, hintIterate_then (step P E) hRunSetup hRunBody, ?_, by omega,
    ?_, hFrame', ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hOutPc
  · intro s
    rw [hOutMem]
    have hRange : G.hintList + G.hints ≤ G.hintList + G.hints + s.val ∧
        G.hintList + G.hints + s.val < G.hintList + G.hints + G.rows := by have := s.isLt; omega
    simp only [hintCopyMem, hintAxpyMem, if_pos hRange, Nat.add_sub_cancel_left, zero_mul, add_zero,
      hintDenseVec, dif_pos s.isLt]
  · intro i hi
    rw [hFrame' _ (Or.inr (by omega))]
    exact hHeader i hi
  · exact (hRegs 12 (by decide) (by decide) (by decide) (by decide)).trans h12
  · exact (hRegs 13 (by decide) (by decide) (by decide) (by decide)).trans h13
  · exact (hRegs 14 (by decide) (by decide) (by decide) (by decide)).trans h14

def hintRhsAxpyStmt : Stmt := .seq (.code hintRhsAxpySetup) hintAxpyStmt
theorem hintRhsAxpyStmt_len : hintRhsAxpyStmt.len = 24 := rfl

theorem hintRhsAxpyStmt_sem (G : HintGaussArea) (f g : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hSource : G.hintList + G.hints + 2 * G.rows ≤ G.context)
    (hF : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + s.val) = (f s).val)
    (hG : ∀ s : Fin G.rows, state.mem (G.column + s.val) = (g s).val)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context) (hCount : state.regs 6 = G.rows) (hOne : state.regs 15 = 1)
    (hAt : At P base (hintRhsAxpyStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 24) state (fun k out => k = 11 * G.rows + 15 ∧
      (∀ s : Fin G.rows, out.mem (G.hintList + G.hints + s.val) = (f s + g s).val) ∧
      CRMemFrame (G.hintList + G.hints) (G.hintList + G.hints + G.rows) state.mem out.mem ∧
      HintGaussHeader G 0 out.mem ∧ out.regs 12 = state.regs 12 ∧ out.regs 13 = state.regs 13 ∧
      out.regs 14 = G.context ∧ out.regs 15 = 1) := by
  have hWord := hGeometry.word_bound
  have hWidth := hGeometry.width_bound
  have h0 := hGeometry.header_before
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  have h3 := hGeometry.column_before
  have h4 := hGeometry.residualVec_before
  have h5 := hGeometry.kernelVec_before
  have h6 := hGeometry.span
  obtain ⟨hSetupAt, hBodyAt⟩ := At.seqStmt hAt
  change At P base hintRhsAxpySetup at hSetupAt
  change At P (base + 11) (hintAxpyStmt.compile (base + 11)) at hBodyAt
  have hNo : NoBranch hintRhsAxpySetup := by
    rw [hintRhsAxpySetup, upNoBranch_append]
    exact ⟨hintLoadFields_noBranch _, by simp [hintRhsAxpyTail, NoBranch, Instr.NoBranchI]⟩
  have hSetup := hintRhsAxpySetup_spec E G state hGeometry hHeader hFits hContext hSource hCount hOne
  generalize hMid : runBlock hintRhsAxpySetup E state = mid at hSetup
  obtain ⟨hArgs, hMem, h12, h13, h14⟩ := hSetup
  have hRunSetup : (step P E)^[11] state = mid := by
    have hh := iterate_runBlock_of_at P E hintRhsAxpySetup state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hMidPc : mid.pc = base + 11 := by
    have hh := runBlock_pc hintRhsAxpySetup E state hNo
    rw [hMid, hPc] at hh
    exact hh
  have hF' : ∀ s < G.rows, mid.mem (G.hintList + G.hints + s) = (hintDenseVec f s).val := by
    intro s hs
    rw [hMem]
    simpa only [hintDenseVec, dif_pos hs] using hF ⟨s, hs⟩
  have hG' : ∀ s < G.rows, mid.mem (G.column + s) = (hintDenseVec g s).val := by
    intro s hs
    rw [hMem]
    simpa only [hintDenseVec, dif_pos hs] using hG ⟨s, hs⟩
  obtain ⟨_, kBody, out, hRunBody, hOutPc, hCost, _, hOutMem, hOutArgs, hFrame, hRegs⟩ :=
    hintAxpyStmt_sem P E mid (G.hintList + G.hints) G.column G.rows (base + 11) 1 (hintDenseVec f) (hintDenseVec g)
      hWord hWidth (by intro s hs; omega) (by intro s hs; omega) hF' hG'
      (Or.inl (by omega)) hBodyAt hMidPc hArgs
  have hFrame' : CRMemFrame (G.hintList + G.hints) (G.hintList + G.hints + G.rows) state.mem out.mem := by
    intro addr hOutside
    exact (hFrame addr hOutside).trans (congrFun hMem addr)
  refine ⟨hPc, kBody + 11, out, hintIterate_then (step P E) hRunSetup hRunBody, ?_, by omega,
    ?_, hFrame', ?_, ?_, ?_, ?_, hOutArgs.one_value⟩
  · simpa only [Nat.add_assoc] using hOutPc
  · intro s
    rw [hOutMem]
    have hRange : G.hintList + G.hints ≤ G.hintList + G.hints + s.val ∧
        G.hintList + G.hints + s.val < G.hintList + G.hints + G.rows := by have := s.isLt; omega
    simp only [hintAxpyMem, if_pos hRange, Nat.add_sub_cancel_left, hintDenseVec, dif_pos s.isLt, one_mul]
  · intro i hi
    rw [hFrame' _ (Or.inr (by omega))]
    exact hHeader i hi
  · exact (hRegs 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h12
  · exact (hRegs 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13
  · exact (hRegs 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h14

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRhsCloneStmt_sem
#print axioms LinearSetReconciliation327.Main.hintRhsAxpyStmt_sem

namespace LinearSetReconciliation327.Main
open HintParams

noncomputable def hintRhsValue (G : HintGaussArea) {r : ℕ} (outside : Fin r → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (v : HintVec G.rows) (j : ℕ) : HintVec G.rows :=
  fun s => v s + ∑ i ∈ hintGaussDone r j, beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (outside i)

theorem hintRhsValue_zero (G : HintGaussArea) {r : ℕ} (outside : Fin r → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps) (v : HintVec G.rows) :
    hintRhsValue G outside beta hPrefix v 0 = v := by
  funext s
  simp [hintRhsValue, hintGaussDone]

theorem hintRhsValue_step (G : HintGaussArea) {r : ℕ} (outside : Fin r → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (v : HintVec G.rows) (j : Fin r) :
    hintRhsValue G outside beta hPrefix v (j.val + 1) =
      hintRhsValue G outside beta hPrefix v j.val +
        (fun s : Fin G.rows => beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (outside j)) := by
  funext s
  unfold hintRhsValue
  rw [← hintGaussDone_succ j, Finset.sum_insert (hintGaussDone_fresh j)]
  simp only [Pi.add_apply]
  abel

theorem hintRowBit_image {r ell K : ℕ} (outside : Fin r → Fin K) (hInj : Function.Injective outside)
    (beta : Fin ell → Fin K → ZMod 2) (s : Fin ell) :
    rowBit beta (Finset.univ.image (fun i => (outside i).val)) s = ∑ i : Fin r, beta s (outside i) := by
  have hNatInj : Function.Injective (fun i => (outside i).val) := by
    intro i j hEq
    exact hInj (Fin.ext hEq)
  have hh := hintBitsSet_rowBit (fun i => (outside i).val) hNatInj (fun i => (outside i).isLt)
    beta (fun _ => 1) s
  simpa [hintBitsSet] using hh

theorem hintRhsValue_full (G : HintGaussArea) {r : ℕ} (outside : Fin r → Fin G.buckets)
    (hInj : Function.Injective outside) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (v : HintVec G.rows) :
    hintRhsValue G outside beta hPrefix v r =
      hintOutsideRhs G beta hPrefix (Finset.univ.image (fun i => (outside i).val)) v := by
  funext s
  simp only [hintRhsValue, hintGaussDone_full, hintOutsideRhs]
  rw [hintRowBit_image outside hInj]

def HintRhsFrame (G : HintGaussArea) (original memory : ℕ → ℕ) : Prop :=
  ∀ addr, (addr < G.hintList + G.hints ∨ G.hintList + G.hints + G.rows ≤ addr) →
    (addr < G.column ∨ G.column + G.rows ≤ addr) → memory addr = original addr

theorem HintRhsFrame.refl (G : HintGaussArea) (memory : ℕ → ℕ) : HintRhsFrame G memory memory := by
  intro addr _ _
  rfl

theorem HintRhsFrame.trans {G : HintGaussArea} {first middle last : ℕ → ℕ}
    (hFirst : HintRhsFrame G first middle) (hLast : HintRhsFrame G middle last) : HintRhsFrame G first last := by
  intro addr hRhs hColumn
  exact (hLast addr hRhs hColumn).trans (hFirst addr hRhs hColumn)

theorem HintRhsFrame.of_rhs {G : HintGaussArea} {original memory : ℕ → ℕ}
    (h : CRMemFrame (G.hintList + G.hints) (G.hintList + G.hints + G.rows) original memory) :
    HintRhsFrame G original memory := by
  intro addr hRhs _
  exact h addr hRhs

theorem HintRhsFrame.of_column {G : HintGaussArea} {original memory : ℕ → ℕ}
    (h : CRMemFrame G.column (G.column + G.rows) original memory) : HintRhsFrame G original memory := by
  intro addr _ hColumn
  exact h addr hColumn

theorem HintRhsFrame.header {E : RAMEnv} {G : HintGaussArea} {original memory : ℕ → ℕ}
    (hFrame : HintRhsFrame G original memory) (hGeometry : HintGaussGeometry E G)
    (hSource : G.hintList + G.hints + G.rows ≤ G.context) (hHeader : HintGaussHeader G 0 original) :
    HintGaussHeader G 0 memory := by
  have h0 := hGeometry.header_before
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  intro i hi
  rw [hFrame _ (Or.inr (by omega)) (Or.inl (by omega))]
  exact hHeader i hi

theorem HintRhsFrame.pointer {E : RAMEnv} {G : HintGaussArea} {original memory : ℕ → ℕ}
    (hFrame : HintRhsFrame G original memory) (hGeometry : HintGaussGeometry E G)
    (hReserve : G.context + 16 ≤ G.residual) (hSource : G.hintList + G.hints + G.rows ≤ G.context) :
    memory (G.context + 15) = original (G.context + 15) := by
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  exact hFrame _ (Or.inr (by omega)) (Or.inl (by omega))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRhsValue_full
#print axioms LinearSetReconciliation327.Main.HintRhsFrame.header
end S_HintRhsPrimitives20261120
section S_HintRhsLoop20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRhsAdvanceCode : List Instr := [.add 12 12 15]

theorem hintRhsAdvance_spec (E : RAMEnv) (state : RAMState) (j r context : ℕ)
    (hNext : j + 1 < 2 ^ E.W) (hCounter : state.regs 12 = j)
    (hCount : state.regs 13 = r) (hContext : state.regs 14 = context) (hOne : state.regs 15 = 1) :
    let out := runBlock hintRhsAdvanceCode E state
    out.pc = state.pc + 1 ∧ out.mem = state.mem ∧ out.regs 12 = j + 1 ∧
      out.regs 13 = r ∧ out.regs 14 = context := by
  simp [hintRhsAdvanceCode, runBlock, execInstr, hCounter, hCount, hContext, hOne, Nat.mod_eq_of_lt hNext]

def hintRhsBody : Stmt := .seq hintRhsQueryStmt (.seq hintRhsAxpyStmt (.code hintRhsAdvanceCode))
theorem hintRhsBody_len : hintRhsBody.len = 63 := rfl

theorem hintRhsBody_sem (G : HintGaussArea) (r : ℕ) (j : Fin r) (outsideBase : ℕ)
    (outside : Fin r → Fin G.buckets) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hSource : G.hintList + G.hints + 2 * G.rows ≤ G.context)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context) (hCounter : state.regs 12 = j.val) (hCount : state.regs 13 = r)
    (hPointer : state.mem (G.context + 15) = outsideBase)
    (hOutsideSpan : outsideBase + 1 + r ≤ G.hintList)
    (hOutside : state.mem (outsideBase + 1 + j.val) = (outside j).val)
    (hRhs : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + s.val) =
      (hintRhsValue G outside beta hPrefix v j.val s).val)
    (hOffset : G.row * G.steps * G.buckets + (outside j).val < 2 ^ E.W)
    (hQuerySpan : ∀ s < G.rows, G.row * G.steps * G.buckets + (outside j).val + s * G.buckets < 2 ^ E.W)
    (hCoeff : ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + (outside j).val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (outside j)).val)
    (hAt : At P base (hintRhsBody.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 63) state (fun k out => k = 20 * G.rows + 47 ∧
      (∀ s : Fin G.rows, out.mem (G.hintList + G.hints + s.val) =
        (hintRhsValue G outside beta hPrefix v (j.val + 1) s).val) ∧
      HintRhsFrame G state.mem out.mem ∧ HintGaussHeader G 0 out.mem ∧
      out.mem (G.context + 15) = outsideBase ∧ out.regs 12 = j.val + 1 ∧
      out.regs 13 = r ∧ out.regs 14 = G.context) := by
  have h0 := hGeometry.residual_before
  have h1 := hGeometry.lift_before
  have h2 := hGeometry.column_before
  have h3 := hGeometry.residualVec_before
  have h4 := hGeometry.kernelVec_before
  have h5 := hGeometry.span
  obtain ⟨hQueryAt, hRestAt⟩ := At.seqStmt hAt
  change At P base (hintRhsQueryStmt.compile base) at hQueryAt
  change At P (base + 38) ((Stmt.seq hintRhsAxpyStmt (.code hintRhsAdvanceCode)).compile (base + 38)) at hRestAt
  obtain ⟨hAxpyAt, hAdvanceAt⟩ := At.seqStmt hRestAt
  change At P (base + 38) (hintRhsAxpyStmt.compile (base + 38)) at hAxpyAt
  change At P (base + 62) hintRhsAdvanceCode at hAdvanceAt
  obtain ⟨_, kQ, sQ, hRunQ, hPcQ, hCostQ, hColumnQ, hFrameQ, hHeaderQ, hPointerQ, hCounterQ, hCountQ, hContextQ, hArgsQ⟩ :=
    hintRhsQueryStmt_sem G r j outsideBase (outside j) beta hPrefix P E state base hGeometry hReserve
      hHeader hFits hContext hCounter hCount hPointer hOutsideSpan hOutside hOffset hQuerySpan hCoeff hQueryAt hPc
  have hRhsQ : ∀ s : Fin G.rows, sQ.mem (G.hintList + G.hints + s.val) =
      (hintRhsValue G outside beta hPrefix v j.val s).val := by
    intro s
    rw [hFrameQ _ (Or.inl (by have := s.isLt; omega))]
    exact hRhs s
  obtain ⟨_, kA, sA, hRunA, hPcA, hCostA, hRhsA, hFrameA, hHeaderA, hCounterA, hCountA, hContextA, hOneA⟩ :=
    hintRhsAxpyStmt_sem G (hintRhsValue G outside beta hPrefix v j.val)
      (fun s => beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (outside j)) P E sQ (base + 38)
      hGeometry hSource hRhsQ hColumnQ hHeaderQ hFits hContextQ hArgsQ.count_value hArgsQ.one_value hAxpyAt hPcQ
  have hCounterA' : sA.regs 12 = j.val := hCounterA.trans hCounterQ
  have hCountA' : sA.regs 13 = r := hCountA.trans hCountQ
  have hNext : j.val + 1 < 2 ^ E.W := by
    have := j.isLt
    have := hFits.values 9 (by decide)
    change G.hintList < 2 ^ E.W at this
    omega
  have hAdvance := hintRhsAdvance_spec E sA j.val r G.context hNext hCounterA' hCountA' hContextA hOneA
  generalize hOut : runBlock hintRhsAdvanceCode E sA = out at hAdvance
  obtain ⟨hPcOut, hMemOut, hCounterOut, hCountOut, hContextOut⟩ := hAdvance
  have hRunAdvance : (step P E)^[1] sA = out := by
    have hh := iterate_runBlock_of_at P E hintRhsAdvanceCode sA (by rwa [hPcA])
      (by simp [hintRhsAdvanceCode, NoBranch, Instr.NoBranchI])
    rw [hOut] at hh
    exact hh
  have hFrameQA : HintRhsFrame G state.mem sA.mem :=
    (HintRhsFrame.of_column hFrameQ).trans (HintRhsFrame.of_rhs hFrameA)
  have hFrameOut : HintRhsFrame G state.mem out.mem := by rw [hMemOut]; exact hFrameQA
  refine ⟨hPc, 1 + (kA + kQ), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunQ hRunA) hRunAdvance,
    ?_, by omega, ?_, hFrameOut, ?_, ?_, hCounterOut, hCountOut, hContextOut⟩
  · rw [hPcOut, hPcA]
  · intro s
    rw [hMemOut, hRhsA, hintRhsValue_step]
    rfl
  · rw [hMemOut]
    exact hHeaderA
  · exact (hFrameOut.pointer hGeometry hReserve (by omega)).trans hPointer

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

structure HintRhsInv (G : HintGaussArea) {r : ℕ} (outside : Fin r → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (v : HintVec G.rows) (outsideBase j : ℕ) (state : RAMState) : Prop where
  rhs : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + s.val) =
    (hintRhsValue G outside beta hPrefix v j s).val
  header : HintGaussHeader G 0 state.mem
  pointer : state.mem (G.context + 15) = outsideBase
  counter : state.regs 12 = j
  count_value : state.regs 13 = r
  context_value : state.regs 14 = G.context

theorem HintRhsInv.pc {G : HintGaussArea} {r : ℕ} {outside : Fin r → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {v : HintVec G.rows} {outsideBase j : ℕ} {state : RAMState}
    (h : HintRhsInv G outside beta hPrefix v outsideBase j state) (pc : ℕ) :
    HintRhsInv G outside beta hPrefix v outsideBase j {state with pc := pc} :=
  ⟨h.rhs, h.header, h.pointer, h.counter, h.count_value, h.context_value⟩

theorem HintRhsInv.test {G : HintGaussArea} {r : ℕ} {outside : Fin r → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {v : HintVec G.rows} {outsideBase j : ℕ} {state : RAMState}
    (h : HintRhsInv G outside beta hPrefix v outsideBase j state) (E : RAMEnv) :
    HintRhsInv G outside beta hPrefix v outsideBase j (runBlock (Cond.lt 2 12 13).code E state) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Cond.code, runBlock, execInstr] using h.rhs
  · simpa [Cond.code, runBlock, execInstr] using h.header
  · simpa [Cond.code, runBlock, execInstr] using h.pointer
  · simpa [Cond.code, runBlock, execInstr] using h.counter
  · simpa [Cond.code, runBlock, execInstr] using h.count_value
  · simpa [Cond.code, runBlock, execInstr] using h.context_value

def hintRhsLoop : Stmt := .loop (.lt 2 12 13) hintRhsBody
theorem hintRhsLoop_len : hintRhsLoop.len = 66 := rfl

theorem hintRhsLoop_sem (G : HintGaussArea) (r : ℕ) (outsideBase : ℕ)
    (outside : Fin r → Fin G.buckets) (beta : Fin G.steps → Fin G.buckets → ZMod 2)
    (hPrefix : G.rows ≤ G.steps) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hSource : G.hintList + G.hints + 2 * G.rows ≤ G.context)
    (hInv : HintRhsInv G outside beta hPrefix v outsideBase 0 state)
    (hFits : HintGaussHeaderFits E G 0)
    (hOutsideSpan : outsideBase + 1 + r ≤ G.hintList)
    (hOutside : ∀ j : Fin r, state.mem (outsideBase + 1 + j.val) = (outside j).val)
    (hSteps : 0 < G.steps) (hCoeffSpan : (G.row + 1) * G.steps * G.buckets ≤ 2 ^ E.W)
    (hCoeff : ∀ j : Fin r, ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + (outside j).val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (outside j)).val)
    (hAt : At P base (hintRhsLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 66) state (fun k out => k ≤ (20 * G.rows + 50) * r + 2 ∧
      HintRhsInv G outside beta hPrefix v outsideBase r out ∧ HintRhsFrame G state.mem out.mem) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ j, j + left = r ∧
    HintRhsInv G outside beta hPrefix v outsideBase j st ∧ HintRhsFrame G state.mem st.mem
  have h0 := hGeometry.residual_before
  have h1 := hGeometry.lift_before
  have h2 := hGeometry.column_before
  have hBodyAt : At P (base + 2) (hintRhsBody.compile (base + 2)) := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨j, hJ, hRhs, hFrame⟩ := hI
    exact ⟨j, hJ, hRhs.pc pc, hFrame⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.lt 2 12 13).code E st) := by
    intro left st hI
    obtain ⟨j, hJ, hRhs, hFrame⟩ := hI
    exact ⟨j, hJ, hRhs.test E, hFrame⟩
  have hGo : ∀ left st, I (left + 1) st → (Cond.lt 2 12 13).eval st := by
    intro left st hI
    obtain ⟨j, hJ, hRhs, _⟩ := hI
    change st.regs 12 < st.regs 13
    rw [hRhs.counter, hRhs.count_value]
    omega
  have hStop : ∀ st, I 0 st → ¬ (Cond.lt 2 12 13).eval st := by
    intro st hI
    obtain ⟨j, hJ, hRhs, _⟩ := hI
    change ¬ st.regs 12 < st.regs 13
    rw [hRhs.counter, hRhs.count_value]
    omega
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.lt 2 12 13).code.length + 1 →
      Sem P E (base + (Cond.lt 2 12 13).code.length + 1)
        (base + (Cond.lt 2 12 13).code.length + 1 + hintRhsBody.len) st
        (fun k out => k ≤ 20 * G.rows + 47 ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨j, hJ, hRhs, hFrame⟩ := hI
    have hj : j < r := by omega
    let t : Fin r := ⟨j, hj⟩
    have hOutsideNow : st.mem (outsideBase + 1 + t.val) = (outside t).val := by
      rw [hFrame _ (Or.inl (by have := t.isLt; omega)) (Or.inl (by have := t.isLt; omega))]
      exact hOutside t
    have hOffset : G.row * G.steps * G.buckets + (outside t).val < 2 ^ E.W := by
      have hh := (hintGauss_query_index_lt G.row G.steps G.buckets 0 (outside t).val hSteps (outside t).isLt).trans_le hCoeffSpan
      simpa only [Nat.zero_mul, Nat.add_zero] using hh
    have hQueries : ∀ s < G.rows, G.row * G.steps * G.buckets + (outside t).val + s * G.buckets < 2 ^ E.W := by
      intro s hs
      exact (hintGauss_query_index_lt G.row G.steps G.buckets s (outside t).val (hs.trans_le hPrefix) (outside t).isLt).trans_le hCoeffSpan
    have hNative := hintRhsBody_sem G r t outsideBase outside beta hPrefix v P E st (base + 2)
      hGeometry hReserve hSource hRhs.header hFits hRhs.context_value hRhs.counter hRhs.count_value
      hRhs.pointer hOutsideSpan hOutsideNow hRhs.rhs hOffset hQueries (hCoeff t) hBodyAt hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hValue, hFrameOut, hHeader, hPointer, hCounter, hCount, hContext⟩ := hOut
    exact ⟨hCost.le, j + 1, by omega, ⟨hValue, hHeader, hPointer, hCounter, hCount, hContext⟩, hFrame.trans hFrameOut⟩
  have hInitial : I r state := ⟨0, by omega, hInv, HintRhsFrame.refl G state.mem⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 12 13) hintRhsBody hAt hGeometry.word_bound I (20 * G.rows + 47)
    hIpc hItest hGo hStop hBody r state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, j, hJ, hFinal, hFrame⟩ := hOut
  have hj : j = r := by omega
  rw [hj] at hFinal
  change k ≤ (1 + (20 * G.rows + 47) + 2) * r + 2 at hCost
  exact ⟨by simpa only [show 1 + (20 * G.rows + 47) + 2 = 20 * G.rows + 50 from by omega] using hCost,
    hFinal, hFrame⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRhsLoop_sem
end S_HintRhsLoop20261120
section S_HintFamilyInput20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRhsBuilder : Stmt := .seq (.code hintRhsEntry) (.seq hintRhsCloneStmt hintRhsLoop)
theorem hintRhsBuilder_len : hintRhsBuilder.len = 94 := rfl

/-- Build the affine right-hand side from the actual observation backup and the
    actual outside-coordinate array. Nothing supplies the resulting vector. -/
theorem hintRhsBuilder_sem (G : HintGaussArea) (r outsideBase : ℕ)
    (outside : Fin r → Fin G.buckets) (hOutsideInj : Function.Injective outside)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hSource : G.hintList + G.hints + 2 * G.rows ≤ G.context)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context) (hPointer : state.mem (G.context + 15) = outsideBase)
    (hCount : state.mem outsideBase = r) (hOutsideSpan : outsideBase + 1 + r ≤ G.hintList)
    (hOutside : ∀ j : Fin r, state.mem (outsideBase + 1 + j.val) = (outside j).val)
    (hVector : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + G.rows + s.val) = (v s).val)
    (hSteps : 0 < G.steps) (hCoeffSpan : (G.row + 1) * G.steps * G.buckets ≤ 2 ^ E.W)
    (hCoeff : ∀ j : Fin r, ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + (outside j).val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ (outside j)).val)
    (hAt : At P base (hintRhsBuilder.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 94) state (fun k out => k ≤ 9 * G.rows + 23 + (20 * G.rows + 50) * r ∧
      (∀ s : Fin G.rows, out.mem (G.hintList + G.hints + s.val) =
        (hintOutsideRhs G beta hPrefix (Finset.univ.image (fun j => (outside j).val)) v s).val) ∧
      HintRhsFrame G state.mem out.mem ∧ HintGaussHeader G 0 out.mem ∧
      out.mem (G.context + 15) = outsideBase ∧ out.regs 12 = r ∧ out.regs 13 = r ∧ out.regs 14 = G.context) := by
  have h0 := hGeometry.residual_before
  have h1 := hGeometry.lift_before
  have h2 := hGeometry.column_before
  obtain ⟨hEntryAt, hRestAt⟩ := At.seqStmt hAt
  change At P base hintRhsEntry at hEntryAt
  change At P (base + 5) ((Stmt.seq hintRhsCloneStmt hintRhsLoop).compile (base + 5)) at hRestAt
  obtain ⟨hCloneAt, hLoopAt⟩ := At.seqStmt hRestAt
  change At P (base + 5) (hintRhsCloneStmt.compile (base + 5)) at hCloneAt
  change At P (base + 28) (hintRhsLoop.compile (base + 28)) at hLoopAt
  have hNo : NoBranch hintRhsEntry := by simp [hintRhsEntry, hintLoadField, NoBranch, Instr.NoBranchI]
  have hEntry := hintRhsEntry_spec E G r outsideBase state hGeometry hReserve hFits hContext hPointer hCount hOutsideSpan
  generalize hMid : runBlock hintRhsEntry E state = mid at hEntry
  obtain ⟨hPcMid, hMemMid, hCounterMid, hCountMid, hContextMid⟩ := hEntry
  have hRunMid : (step P E)^[5] state = mid := by
    have hh := iterate_runBlock_of_at P E hintRhsEntry state (by rwa [hPc]) hNo
    rw [hMid] at hh
    exact hh
  have hVectorMid : ∀ s : Fin G.rows, mid.mem (G.hintList + G.hints + G.rows + s.val) = (v s).val := by
    rw [hMemMid]
    exact hVector
  have hHeaderMid : HintGaussHeader G 0 mid.mem := by rw [hMemMid]; exact hHeader
  obtain ⟨_, kC, sC, hRunC, hPcC, hCostC, hVectorC, hFrameC, hHeaderC, hCounterC, hCountC, hContextC⟩ :=
    hintRhsCloneStmt_sem G v P E mid (base + 5) hGeometry hSource hVectorMid hHeaderMid hFits hContextMid hCloneAt
      (by rw [hPcMid, hPc])
  have hFrameC' : HintRhsFrame G state.mem sC.mem := by
    have hh := HintRhsFrame.of_rhs hFrameC
    rw [hMemMid] at hh
    exact hh
  have hInvC : HintRhsInv G outside beta hPrefix v outsideBase 0 sC := by
    refine ⟨?_, hHeaderC, ?_, hCounterC.trans hCounterMid, hCountC.trans hCountMid, hContextC⟩
    · simpa only [hintRhsValue_zero] using hVectorC
    · exact (hFrameC'.pointer hGeometry hReserve (by omega)).trans hPointer
  have hOutsideC : ∀ j : Fin r, sC.mem (outsideBase + 1 + j.val) = (outside j).val := by
    intro j
    rw [hFrameC' _ (Or.inl (by have := j.isLt; omega)) (Or.inl (by have := j.isLt; omega))]
    exact hOutside j
  obtain ⟨_, kL, out, hRunL, hPcL, hCostL, hInvL, hFrameL⟩ :=
    hintRhsLoop_sem G r outsideBase outside beta hPrefix v P E sC (base + 28) hGeometry hReserve
      hSource hInvC hFits hOutsideSpan hOutsideC hSteps hCoeffSpan hCoeff hLoopAt (by simpa only [Nat.add_assoc] using hPcC)
  refine ⟨hPc, kL + (kC + 5), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunMid hRunC) hRunL,
    ?_, by omega, ?_, hFrameC'.trans hFrameL, hInvL.header, hInvL.pointer, hInvL.counter, hInvL.count_value, hInvL.context_value⟩
  · simpa only [Nat.add_assoc] using hPcL
  · simpa only [hintRhsValue_full G outside hOutsideInj beta hPrefix v] using hInvL.rhs

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintFamilyInputCallStmt : Stmt := .seq hintRhsBuilder hintGaussSolverStmt
theorem hintFamilyInputCallStmt_len : hintFamilyInputCallStmt.len = 552 := rfl

/-- Unlike the lower-level affine call, this call takes only the original
    transcript backup and actual coordinate arrays as its data inputs. -/
theorem hintFamilyInputCall_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (r outsideBase : ℕ) (outside : Fin r → Fin G.buckets) (hOutsideInj : Function.Injective outside)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps) (v : HintVec G.rows) (Nj : ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hSource : G.hintList + G.hints + 2 * G.rows ≤ G.context)
    (hInj : Function.Injective coords) (hHintValid : ∀ j, (coords j).val < Nj)
    (hOutsideValid : ∀ j, (outside j).val < Nj)
    (hSeparate : Disjoint (Finset.univ.image (fun j => (outside j).val))
      (Finset.univ.image (fun j => (coords j).val)))
    (hHint : ∀ j : Fin G.hints, state.mem (G.hintList + j.val) = (coords j).val)
    (hHeader : HintGaussHeader G 0 state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context) (hPointer : state.mem (G.context + 15) = outsideBase)
    (hCount : state.mem outsideBase = r) (hOutsideSpan : outsideBase + 1 + r ≤ G.hintList)
    (hOutside : ∀ j : Fin r, state.mem (outsideBase + 1 + j.val) = (outside j).val)
    (hVector : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + G.rows + s.val) = (v s).val)
    (hSteps : 0 < G.steps) (hCoeffSpan : (G.row + 1) * G.steps * G.buckets ≤ 2 ^ E.W)
    (hCoeff : ∀ c : Fin G.buckets, ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + c.val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ c).val)
    (hAt : At P base (hintFamilyInputCallStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 552) state (fun k out =>
      k ≤ 9 * G.rows + 23 + (20 * G.rows + 50) * r + 512 * (G.rows + G.hints + 1) ^ 3 ∧
      (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧
      (out.regs 1 = 1 ↔ ∃! C : Finset ℕ, hintFamilyClass G coords beta Nj r
        (Finset.univ.image (fun j => (outside j).val)) v C) ∧
      (out.regs 1 = 1 → ∃ z : HintVec G.hints,
        (∀ t : Fin G.hints, out.mem (G.kernelVec + t.val) = (z t).val) ∧
        hintFamilyClass G coords beta Nj r (Finset.univ.image (fun j => (outside j).val)) v
          (hintBitsSet (fun j => (coords j).val) z ∪ Finset.univ.image (fun j => (outside j).val)) ∧
        ∀ C : Finset ℕ, hintFamilyClass G coords beta Nj r (Finset.univ.image (fun j => (outside j).val)) v C →
          C = hintBitsSet (fun j => (coords j).val) z ∪ Finset.univ.image (fun j => (outside j).val)) ∧
      HintGaussHeader G G.hints out.mem ∧
      (∀ addr, (addr < G.hintList + G.hints ∨ G.hintList + G.hints + G.rows ≤ addr) →
        (addr < G.context ∨ G.pivotRow + G.rows ≤ addr) → out.mem addr = state.mem addr) ∧ out.regs 14 = G.context) := by
  have h0 := hGeometry.header_before
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  have h3 := hGeometry.column_before
  have h4 := hGeometry.residualVec_before
  have h5 := hGeometry.kernelVec_before
  have h6 := hGeometry.span
  obtain ⟨hBuilderAt, hSolverAt⟩ := At.seqStmt hAt
  change At P base (hintRhsBuilder.compile base) at hBuilderAt
  change At P (base + 94) (hintGaussSolverStmt.compile (base + 94)) at hSolverAt
  obtain ⟨_, kB, sB, hRunB, hPcB, hCostB, hRhsB, hFrameB, hHeaderB, _, _, _, hContextB⟩ :=
    hintRhsBuilder_sem G r outsideBase outside hOutsideInj beta hPrefix v P E state base hGeometry hReserve hSource
      hHeader hFits hContext hPointer hCount hOutsideSpan hOutside hVector hSteps hCoeffSpan (fun j => hCoeff (outside j)) hBuilderAt hPc
  have hHintB : ∀ j : Fin G.hints, sB.mem (G.hintList + j.val) = (coords j).val := by
    intro j
    rw [hFrameB _ (Or.inl (by have := j.isLt; omega)) (Or.inl (by have := j.isLt; omega))]
    exact hHint j
  have hOutsideSet : Finset.univ.image (fun j => (outside j).val) ⊆ Finset.range Nj := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hOutsideValid j)
  have hNatInj : Function.Injective (fun j => (outside j).val) := by
    intro i j hEq
    exact hOutsideInj (Fin.ext hEq)
  have hCard : (Finset.univ.image (fun j => (outside j).val)).card = r := by
    rw [Finset.card_image_of_injective _ hNatInj, Finset.card_univ, Fintype.card_fin]
  obtain ⟨_, kS, out, hRunS, hPcS, hCostS, hBit, hUnique, hWitness, hHeaderOut, hFrameS, hContextOut⟩ :=
    hintFamilyCandidateCall_sem G coords beta hPrefix Nj r (Finset.univ.image (fun j => (outside j).val)) v
      P E sB (base + 94) hGeometry hReserve (by omega) hInj hHintValid hOutsideSet hCard hSeparate hHintB hRhsB
      hSteps hCoeffSpan (fun j => hCoeff (coords j)) hHeaderB hFits hContextB hSolverAt hPcB
  refine ⟨hPc, kS + kB, out, hintIterate_then (step P E) hRunB hRunS, ?_, by omega,
    hBit, hUnique, hWitness, hHeaderOut, ?_, hContextOut⟩
  · simpa only [Nat.add_assoc] using hPcS
  · intro addr hRhs hOutsideGauss
    rw [hFrameS addr hOutsideGauss]
    apply hFrameB addr hRhs
    rcases hOutsideGauss with hBefore | hAfter
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintFamilyInputCall_sem
end S_HintFamilyInput20261120
section S_HintTupleFilterInner20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintTruth (P : Prop) : ℕ := by classical exact if P then 1 else 0

theorem hintTruth_congr {P Q : Prop} (h : P ↔ Q) : hintTruth P = hintTruth Q := congrArg hintTruth (propext h)

def HintTuplePrefix (g : ℕ → ℕ) (i j : ℕ) : Prop := ∀ t < j, i < t → g i < g t

theorem hintTuplePrefix_succ (g : ℕ → ℕ) (i j : ℕ) :
    HintTuplePrefix g i (j + 1) ↔ HintTuplePrefix g i j ∧ (i < j → g i < g j) := by
  constructor
  · intro h
    exact ⟨fun t ht => h t (by omega), h j (by omega)⟩
  · rintro ⟨h, hLast⟩ t ht hit
    by_cases hEq : t = j
    · subst t; exact hLast hit
    · exact h t (by omega) hit

structure HintTupleScanArgs (arrayBase count firstIndex firstValue : ℕ) (state : RAMState) : Prop where
  array : state.regs 4 = arrayBase
  count_value : state.regs 13 = count
  first_index : state.regs 12 = firstIndex
  first_value : state.regs 11 = firstValue
  one_value : state.regs 15 = 1

def hintTupleScanBody : List Instr :=
  [.add 3 4 0, .load 8 3, .lt 9 12 0, .lt 10 11 8, .lt 9 9 15,
    .bor 9 9 10, .mul 1 1 9, .add 0 0 15]

theorem hintTupleScanBody_spec (E : RAMEnv) (state : RAMState) (arrayBase count i j value first : ℕ)
    (accepted : Prop) (hWord : 1 < 2 ^ E.W) (hValue : value < 2 ^ E.W)
    (hAddr : arrayBase + j < 2 ^ E.W) (hNext : j + 1 < 2 ^ E.W)
    (hArgs : HintTupleScanArgs arrayBase count i first state)
    (hCounter : state.regs 0 = j) (hAccept : state.regs 1 = hintTruth accepted)
    (hRead : state.mem (arrayBase + j) = value) :
    let out := runBlock hintTupleScanBody E state
    out.pc = state.pc + 8 ∧ out.mem = state.mem ∧ out.regs 0 = j + 1 ∧
      out.regs 1 = hintTruth (accepted ∧ (i < j → first < value)) ∧
      HintTupleScanArgs arrayBase count i first out ∧
      out.regs 7 = state.regs 7 ∧ out.regs 14 = state.regs 14 := by
  classical
  obtain ⟨h4, h13, h12, h11, h15⟩ := hArgs
  dsimp only
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hintTupleScanBody, runBlock, execInstr]
  · simp [hintTupleScanBody, runBlock, execInstr, hCounter, h15, Nat.mod_eq_of_lt hNext]
  · by_cases hA : accepted <;> by_cases hIJ : i < j <;> by_cases hLT : first < value <;>
      simp [hintTupleScanBody, runBlock, execInstr, hintTruth, h4, h12, h11, h15,
        hCounter, hAccept, hRead, hA, hIJ, hLT, Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hValue, Nat.mod_eq_of_lt hWord]
  · exact ⟨by simpa [hintTupleScanBody, runBlock, execInstr] using h4,
      by simpa [hintTupleScanBody, runBlock, execInstr] using h13,
      by simpa [hintTupleScanBody, runBlock, execInstr] using h12,
      by simpa [hintTupleScanBody, runBlock, execInstr] using h11,
      by simpa [hintTupleScanBody, runBlock, execInstr] using h15⟩
  · simp [hintTupleScanBody, runBlock, execInstr]
  · simp [hintTupleScanBody, runBlock, execInstr]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

theorem HintTupleScanArgs.pc {arrayBase count firstIndex firstValue : ℕ} {state : RAMState}
    (h : HintTupleScanArgs arrayBase count firstIndex firstValue state) (pc : ℕ) :
    HintTupleScanArgs arrayBase count firstIndex firstValue {state with pc := pc} :=
  ⟨h.array, h.count_value, h.first_index, h.first_value, h.one_value⟩

theorem HintTupleScanArgs.test {arrayBase count firstIndex firstValue : ℕ} {state : RAMState}
    (h : HintTupleScanArgs arrayBase count firstIndex firstValue state) (E : RAMEnv) :
    HintTupleScanArgs arrayBase count firstIndex firstValue (runBlock (Cond.lt 2 0 13).code E state) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Cond.code, runBlock, execInstr] using h.array
  · simpa [Cond.code, runBlock, execInstr] using h.count_value
  · simpa [Cond.code, runBlock, execInstr] using h.first_index
  · simpa [Cond.code, runBlock, execInstr] using h.first_value
  · simpa [Cond.code, runBlock, execInstr] using h.one_value

def HintTupleScanInv (arrayBase count firstIndex : ℕ) (g original : ℕ → ℕ) (accepted : Prop)
    (j : ℕ) (state : RAMState) : Prop :=
  HintTupleScanArgs arrayBase count firstIndex (g firstIndex) state ∧
    state.regs 0 = j ∧ state.regs 1 = hintTruth (accepted ∧ HintTuplePrefix g firstIndex j) ∧ state.mem = original

def hintTupleScanLoop : Stmt := .loop (.lt 2 0 13) (.code hintTupleScanBody)
theorem hintTupleScanLoop_len : hintTupleScanLoop.len = 11 := rfl

theorem hintTupleScanLoop_sem (arrayBase count i : ℕ) (g : ℕ → ℕ) (accepted : Prop)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hSpan : arrayBase + count < 2 ^ E.W)
    (hBound : ∀ j < count, g j < 2 ^ E.W)
    (hArgs : HintTupleScanArgs arrayBase count i (g i) state)
    (hCounter : state.regs 0 = 0) (hAccept : state.regs 1 = hintTruth accepted)
    (hDigits : ∀ j < count, state.mem (arrayBase + j) = g j)
    (hAt : At P base (hintTupleScanLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 11) state (fun k out => k ≤ 11 * count + 2 ∧
      HintTupleScanArgs arrayBase count i (g i) out ∧ out.regs 0 = count ∧
      out.regs 1 = hintTruth (accepted ∧ HintTuplePrefix g i count) ∧ out.mem = state.mem ∧
      out.regs 7 = state.regs 7 ∧ out.regs 14 = state.regs 14) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ j, j + left = count ∧
    HintTupleScanInv arrayBase count i g state.mem accepted j st ∧
    st.regs 7 = state.regs 7 ∧ st.regs 14 = state.regs 14
  have hBodyAt : At P (base + 2) hintTupleScanBody := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨j, hJ, ⟨hA, h0, h1, hMem⟩, h7, h14⟩ := hI
    exact ⟨j, hJ, ⟨hA.pc pc, h0, h1, hMem⟩, h7, h14⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.lt 2 0 13).code E st) := by
    intro left st hI
    obtain ⟨j, hJ, ⟨hA, h0, h1, hMem⟩, h7, h14⟩ := hI
    refine ⟨j, hJ, ⟨hA.test E, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simpa [Cond.code, runBlock, execInstr] using h0
    · simpa [Cond.code, runBlock, execInstr] using h1
    · simpa [Cond.code, runBlock, execInstr] using hMem
    · simpa [Cond.code, runBlock, execInstr] using h7
    · simpa [Cond.code, runBlock, execInstr] using h14
  have hGo : ∀ left st, I (left + 1) st → (Cond.lt 2 0 13).eval st := by
    intro left st hI
    obtain ⟨j, hJ, ⟨hA, h0, _, _⟩, _, _⟩ := hI
    change st.regs 0 < st.regs 13
    rw [h0, hA.count_value]
    omega
  have hStop : ∀ st, I 0 st → ¬ (Cond.lt 2 0 13).eval st := by
    intro st hI
    obtain ⟨j, hJ, ⟨hA, h0, _, _⟩, _, _⟩ := hI
    change ¬ st.regs 0 < st.regs 13
    rw [h0, hA.count_value]
    omega
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.lt 2 0 13).code.length + 1 →
      Sem P E (base + (Cond.lt 2 0 13).code.length + 1)
        (base + (Cond.lt 2 0 13).code.length + 1 + (Stmt.code hintTupleScanBody).len) st
        (fun k out => k ≤ 8 ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨j, hJ, ⟨hA, h0, h1, hMem⟩, h7, h14⟩ := hI
    have hj : j < count := by omega
    have hRead : st.mem (arrayBase + j) = g j := by rw [hMem]; exact hDigits j hj
    have hSpec := hintTupleScanBody_spec E st arrayBase count i j (g j) (g i)
      (accepted ∧ HintTuplePrefix g i j) hWord (hBound j hj) (by omega) (by omega) hA h0 h1 hRead
    generalize hMid : runBlock hintTupleScanBody E st = mid at hSpec
    obtain ⟨_, hMemMid, h0Mid, h1Mid, hArgsMid, h7Mid, h14Mid⟩ := hSpec
    have hFlag : mid.regs 1 = hintTruth (accepted ∧ HintTuplePrefix g i (j + 1)) :=
      h1Mid.trans (hintTruth_congr (by rw [hintTuplePrefix_succ]; tauto))
    have hNative := Sem.block P E (base + 2) hintTupleScanBody st hBodyAt
      (by simp [hintTupleScanBody, NoBranch, Instr.NoBranchI]) hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hK, hOut⟩ := hOut
    rw [hMid] at hOut
    subst out
    exact ⟨by simpa [hintTupleScanBody] using hK.le, j + 1, by omega,
      ⟨hArgsMid, h0Mid, hFlag, hMemMid.trans hMem⟩, h7Mid.trans h7, h14Mid.trans h14⟩
  have hFlag0 : state.regs 1 = hintTruth (accepted ∧ HintTuplePrefix g i 0) := by
    rw [hAccept]
    apply hintTruth_congr
    simp [HintTuplePrefix]
  have hInitial : I count state := ⟨0, by omega, ⟨hArgs, hCounter, hFlag0, rfl⟩, rfl, rfl⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 0 13) (.code hintTupleScanBody) hAt hWord I 8
    hIpc hItest hGo hStop hBody count state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, j, hJ, ⟨hA, h0, h1, hMem⟩, h7, h14⟩ := hOut
  have hj : j = count := by omega
  rw [hj] at h0 h1
  exact ⟨hCost, hA, h0, h1, hMem, h7, h14⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintTupleScanLoop_sem
end S_HintTupleFilterInner20261120
section S_HintTupleFilter20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintTupleFilterArgs (arrayBase count bitmapBase : ℕ) (state : RAMState) : Prop where
  array : state.regs 4 = arrayBase
  count_value : state.regs 13 = count
  bitmap : state.regs 7 = bitmapBase
  one_value : state.regs 15 = 1

def hintTupleFilterSetup : List Instr :=
  [.add 3 4 12, .load 11 3, .add 3 7 11, .load 8 3, .lt 8 8 15, .mul 1 1 8, .imm 0 0]

theorem hintTupleFilterSetup_spec (E : RAMEnv) (state : RAMState) (arrayBase count bitmapBase i value : ℕ)
    (accepted : Prop) (J : Finset ℕ) (hWord : 1 < 2 ^ E.W) (hValue : value < 2 ^ E.W)
    (hAddr : arrayBase + i < 2 ^ E.W) (hBitmapAddr : bitmapBase + value < 2 ^ E.W)
    (hArgs : HintTupleFilterArgs arrayBase count bitmapBase state)
    (hCounter : state.regs 12 = i) (hAccept : state.regs 1 = hintTruth accepted)
    (hRead : state.mem (arrayBase + i) = value)
    (hBitmap : state.mem (bitmapBase + value) = hintTruth (value ∈ J)) :
    let out := runBlock hintTupleFilterSetup E state
    out.pc = state.pc + 7 ∧ out.mem = state.mem ∧
      HintTupleScanArgs arrayBase count i value out ∧ out.regs 0 = 0 ∧
      out.regs 1 = hintTruth (accepted ∧ value ∉ J) ∧ out.regs 7 = bitmapBase ∧ out.regs 14 = state.regs 14 := by
  classical
  obtain ⟨h4, h13, h7, h15⟩ := hArgs
  dsimp only
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hintTupleFilterSetup, runBlock, execInstr]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hintTupleFilterSetup, runBlock, execInstr, h4, h13, h7, h15, hCounter, hRead,
        Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hValue]
  · simp [hintTupleFilterSetup, runBlock, execInstr]
  · by_cases hA : accepted <;> by_cases hJ : value ∈ J <;>
      simp [hintTupleFilterSetup, runBlock, execInstr, hintTruth, h4, h13, h7, h15, hCounter, hAccept,
        hRead, hBitmap, hA, hJ, Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hValue,
        Nat.mod_eq_of_lt hBitmapAddr, Nat.mod_eq_of_lt hWord]
  · simp [hintTupleFilterSetup, runBlock, execInstr, h7]
  · simp [hintTupleFilterSetup, runBlock, execInstr]

def hintTupleFilterBody : Stmt :=
  .seq (.code hintTupleFilterSetup) (.seq hintTupleScanLoop (.code hintRhsAdvanceCode))
theorem hintTupleFilterBody_len : hintTupleFilterBody.len = 19 := rfl

theorem hintTupleFilterBody_sem (arrayBase count bitmapBase i Nj : ℕ) (g : ℕ → ℕ)
    (accepted : Prop) (J : Finset ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hNj : Nj < 2 ^ E.W)
    (hSpan : arrayBase + count < 2 ^ E.W) (hBitmapSpan : bitmapBase + Nj ≤ 2 ^ E.W)
    (hBound : ∀ j < count, g j < Nj) (hi : i < count)
    (hArgs : HintTupleFilterArgs arrayBase count bitmapBase state)
    (hCounter : state.regs 12 = i) (hAccept : state.regs 1 = hintTruth accepted)
    (hDigits : ∀ j < count, state.mem (arrayBase + j) = g j)
    (hBitmap : ∀ v < Nj, state.mem (bitmapBase + v) = hintTruth (v ∈ J))
    (hAt : At P base (hintTupleFilterBody.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 19) state (fun k out => k ≤ 11 * count + 10 ∧
      HintTupleFilterArgs arrayBase count bitmapBase out ∧ out.regs 12 = i + 1 ∧
      out.regs 1 = hintTruth (accepted ∧ (g i ∉ J ∧ HintTuplePrefix g i count)) ∧
      out.mem = state.mem ∧ out.regs 14 = state.regs 14) := by
  obtain ⟨hSetupAt, hRestAt⟩ := At.seqStmt hAt
  change At P base hintTupleFilterSetup at hSetupAt
  change At P (base + 7) ((Stmt.seq hintTupleScanLoop (.code hintRhsAdvanceCode)).compile (base + 7)) at hRestAt
  obtain ⟨hScanAt, hAdvanceAt⟩ := At.seqStmt hRestAt
  change At P (base + 7) (hintTupleScanLoop.compile (base + 7)) at hScanAt
  change At P (base + 18) hintRhsAdvanceCode at hAdvanceAt
  have hSetup := hintTupleFilterSetup_spec E state arrayBase count bitmapBase i (g i) accepted J hWord
    ((hBound i hi).trans hNj) (by omega) (by have := hBound i hi; omega) hArgs hCounter hAccept
    (hDigits i hi) (hBitmap (g i) (hBound i hi))
  generalize hMid : runBlock hintTupleFilterSetup E state = mid at hSetup
  obtain ⟨hPcMid, hMemMid, hScanArgs, hZero, hFlagMid, hBitmapBase, hContextMid⟩ := hSetup
  have hRunMid : (step P E)^[7] state = mid := by
    have hh := iterate_runBlock_of_at P E hintTupleFilterSetup state (by rwa [hPc])
      (by simp [hintTupleFilterSetup, NoBranch, Instr.NoBranchI])
    rw [hMid] at hh
    exact hh
  have hDigitsMid : ∀ j < count, mid.mem (arrayBase + j) = g j := by rw [hMemMid]; exact hDigits
  obtain ⟨_, kS, sS, hRunS, hPcS, hCostS, hArgsS, _, hFlagS, hMemS, hBitmapS, hContextS⟩ :=
    hintTupleScanLoop_sem arrayBase count i g (accepted ∧ g i ∉ J) P E mid (base + 7)
      hWord hSpan (fun j hj => (hBound j hj).trans hNj) hScanArgs hZero hFlagMid hDigitsMid hScanAt (by rw [hPcMid, hPc])
  have hAdvance := hintRhsAdvance_spec E sS i count (state.regs 14) (by omega)
    hArgsS.first_index hArgsS.count_value (hContextS.trans hContextMid) hArgsS.one_value
  generalize hOut : runBlock hintRhsAdvanceCode E sS = out at hAdvance
  obtain ⟨hPcOut, hMemOut, hCounterOut, _, hContextOut⟩ := hAdvance
  have hRunOut : (step P E)^[1] sS = out := by
    have hh := iterate_runBlock_of_at P E hintRhsAdvanceCode sS (by rwa [hPcS])
      (by simp [hintRhsAdvanceCode, NoBranch, Instr.NoBranchI])
    rw [hOut] at hh
    exact hh
  have hFlagOut : out.regs 1 = sS.regs 1 := by
    rw [← hOut]
    simp [hintRhsAdvanceCode, runBlock, execInstr]
  have hArgsOut : HintTupleFilterArgs arrayBase count bitmapBase out := by
    have h4 := hArgsS.array
    have h13 := hArgsS.count_value
    have h15 := hArgsS.one_value
    have h7 : sS.regs 7 = bitmapBase := hBitmapS.trans hBitmapBase
    rw [← hOut]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hintRhsAdvanceCode, runBlock, execInstr] using h4
    · simpa [hintRhsAdvanceCode, runBlock, execInstr] using h13
    · simpa [hintRhsAdvanceCode, runBlock, execInstr] using h7
    · simpa [hintRhsAdvanceCode, runBlock, execInstr] using h15
  refine ⟨hPc, 1 + (kS + 7), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunMid hRunS) hRunOut,
    ?_, by omega, hArgsOut, hCounterOut, ?_, hMemOut.trans (hMemS.trans hMemMid), hContextOut⟩
  · rw [hPcOut, hPcS]
  · exact hFlagOut.trans (hFlagS.trans (hintTruth_congr (by tauto)))

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def HintTupleGood (count : ℕ) (J : Finset ℕ) (g : ℕ → ℕ) (i : ℕ) : Prop :=
  ∀ t < i, g t ∉ J ∧ HintTuplePrefix g t count

theorem hintTupleGood_succ (count : ℕ) (J : Finset ℕ) (g : ℕ → ℕ) (i : ℕ) :
    HintTupleGood count J g (i + 1) ↔ HintTupleGood count J g i ∧ (g i ∉ J ∧ HintTuplePrefix g i count) := by
  constructor
  · intro h
    exact ⟨fun t ht => h t (by omega), h i (by omega)⟩
  · rintro ⟨h, hLast⟩ t ht
    by_cases hEq : t = i
    · subst t; exact hLast
    · exact h t (by omega)

theorem hintTupleGood_full (count : ℕ) (J : Finset ℕ) (g : ℕ → ℕ) :
    HintTupleGood count J g count ↔
      StrictMono (fun i : Fin count => g i.val) ∧ ∀ i : Fin count, g i.val ∉ J := by
  constructor
  · intro h
    exact ⟨fun i j hij => (h i.val i.isLt).2 j.val j.isLt hij, fun i => (h i.val i.isLt).1⟩
  · rintro ⟨hMono, hAvoid⟩ t ht
    refine ⟨hAvoid ⟨t, ht⟩, ?_⟩
    intro u hu htu
    exact hMono (show (⟨t, ht⟩ : Fin count) < ⟨u, hu⟩ from htu)

structure HintTupleFilterInv (arrayBase count bitmapBase : ℕ) (g original : ℕ → ℕ) (J : Finset ℕ)
    (i : ℕ) (state : RAMState) : Prop where
  args : HintTupleFilterArgs arrayBase count bitmapBase state
  counter : state.regs 12 = i
  flag : state.regs 1 = hintTruth (HintTupleGood count J g i)
  memory : state.mem = original

theorem HintTupleFilterInv.pc {arrayBase count bitmapBase i : ℕ} {g original : ℕ → ℕ}
    {J : Finset ℕ} {state : RAMState} (h : HintTupleFilterInv arrayBase count bitmapBase g original J i state) (pc : ℕ) :
    HintTupleFilterInv arrayBase count bitmapBase g original J i {state with pc := pc} :=
  ⟨⟨h.args.array, h.args.count_value, h.args.bitmap, h.args.one_value⟩, h.counter, h.flag, h.memory⟩

theorem HintTupleFilterInv.test {arrayBase count bitmapBase i : ℕ} {g original : ℕ → ℕ}
    {J : Finset ℕ} {state : RAMState} (h : HintTupleFilterInv arrayBase count bitmapBase g original J i state) (E : RAMEnv) :
    HintTupleFilterInv arrayBase count bitmapBase g original J i (runBlock (Cond.lt 2 12 13).code E state) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simpa [Cond.code, runBlock, execInstr] using h.args.array
  · simpa [Cond.code, runBlock, execInstr] using h.args.count_value
  · simpa [Cond.code, runBlock, execInstr] using h.args.bitmap
  · simpa [Cond.code, runBlock, execInstr] using h.args.one_value
  · simpa [Cond.code, runBlock, execInstr] using h.counter
  · simpa [Cond.code, runBlock, execInstr] using h.flag
  · simpa [Cond.code, runBlock, execInstr] using h.memory

def hintTupleFilterLoop : Stmt := .loop (.lt 2 12 13) hintTupleFilterBody
theorem hintTupleFilterLoop_len : hintTupleFilterLoop.len = 22 := rfl

theorem hintTupleFilterLoop_sem (arrayBase count bitmapBase Nj : ℕ) (g : ℕ → ℕ) (J : Finset ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hNj : Nj < 2 ^ E.W)
    (hSpan : arrayBase + count < 2 ^ E.W) (hBitmapSpan : bitmapBase + Nj ≤ 2 ^ E.W)
    (hBound : ∀ j < count, g j < Nj)
    (hInv : HintTupleFilterInv arrayBase count bitmapBase g state.mem J 0 state)
    (hDigits : ∀ j < count, state.mem (arrayBase + j) = g j)
    (hBitmap : ∀ v < Nj, state.mem (bitmapBase + v) = hintTruth (v ∈ J))
    (hAt : At P base (hintTupleFilterLoop.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 22) state (fun k out => k ≤ (11 * count + 13) * count + 2 ∧
      HintTupleFilterInv arrayBase count bitmapBase g state.mem J count out ∧ out.regs 14 = state.regs 14) := by
  let I : ℕ → RAMState → Prop := fun left st => ∃ i, i + left = count ∧
    HintTupleFilterInv arrayBase count bitmapBase g state.mem J i st ∧ st.regs 14 = state.regs 14
  have hBodyAt : At P (base + 2) (hintTupleFilterBody.compile (base + 2)) := (at_loop hAt).2.2.1
  have hIpc : ∀ left st pc, I left st → I left {st with pc := pc} := by
    intro left st pc hI
    obtain ⟨i, hi, hFilter, hCtx⟩ := hI
    exact ⟨i, hi, hFilter.pc pc, hCtx⟩
  have hItest : ∀ left st, I left st → I left (runBlock (Cond.lt 2 12 13).code E st) := by
    intro left st hI
    obtain ⟨i, hi, hFilter, hCtx⟩ := hI
    refine ⟨i, hi, hFilter.test E, ?_⟩
    simpa [Cond.code, runBlock, execInstr] using hCtx
  have hGo : ∀ left st, I (left + 1) st → (Cond.lt 2 12 13).eval st := by
    intro left st hI
    obtain ⟨i, hi, hFilter, _⟩ := hI
    change st.regs 12 < st.regs 13
    rw [hFilter.counter, hFilter.args.count_value]
    omega
  have hStop : ∀ st, I 0 st → ¬ (Cond.lt 2 12 13).eval st := by
    intro st hI
    obtain ⟨i, hi, hFilter, _⟩ := hI
    change ¬ st.regs 12 < st.regs 13
    rw [hFilter.counter, hFilter.args.count_value]
    omega
  have hBody : ∀ left st, I (left + 1) st → st.pc = base + (Cond.lt 2 12 13).code.length + 1 →
      Sem P E (base + (Cond.lt 2 12 13).code.length + 1)
        (base + (Cond.lt 2 12 13).code.length + 1 + hintTupleFilterBody.len) st
        (fun k out => k ≤ 11 * count + 10 ∧ I left out) := by
    intro left st hI hStart
    obtain ⟨i, hI, hFilter, hCtx⟩ := hI
    have hi : i < count := by omega
    have hDigitsNow : ∀ j < count, st.mem (arrayBase + j) = g j := by rw [hFilter.memory]; exact hDigits
    have hBitmapNow : ∀ v < Nj, st.mem (bitmapBase + v) = hintTruth (v ∈ J) := by rw [hFilter.memory]; exact hBitmap
    have hNative := hintTupleFilterBody_sem arrayBase count bitmapBase i Nj g (HintTupleGood count J g i) J P E st (base + 2)
      hWord hNj hSpan hBitmapSpan hBound hi hFilter.args hFilter.counter hFilter.flag hDigitsNow hBitmapNow hBodyAt hStart
    apply Sem.mono hNative
    intro k out hOut
    obtain ⟨hCost, hArgs, hCounter, hFlag, hMemory, hContext⟩ := hOut
    exact ⟨hCost, i + 1, by omega,
      ⟨hArgs, hCounter, hFlag.trans (hintTruth_congr (hintTupleGood_succ count J g i).symm), hMemory.trans hFilter.memory⟩,
      hContext.trans hCtx⟩
  have hInitial : I count state := ⟨0, by omega, hInv, rfl⟩
  have hNative := hintLoopFuel_sem P E base (.lt 2 12 13) hintTupleFilterBody hAt hWord I (11 * count + 10)
    hIpc hItest hGo hStop hBody count state hInitial hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hCost, i, hi, hFinal, hContext⟩ := hOut
  have hIndex : i = count := by omega
  rw [hIndex] at hFinal
  change k ≤ (1 + (11 * count + 10) + 2) * count + 2 at hCost
  exact ⟨by simpa only [show 1 + (11 * count + 10) + 2 = 11 * count + 13 from by omega] using hCost, hFinal, hContext⟩

def hintTupleFilterInit : List Instr := [.imm 1 1, .imm 12 0, .imm 15 1]
def hintTupleFilterStmt : Stmt := .seq (.code hintTupleFilterInit) hintTupleFilterLoop
theorem hintTupleFilterStmt_len : hintTupleFilterStmt.len = 25 := rfl

/-- A native read-only test for an ascending tuple disjoint from the hints.
    Its quadratic cost is only in the outside count, never in 2^|J|. -/
theorem hintTupleFilterStmt_sem (arrayBase count bitmapBase Nj : ℕ) (g : ℕ → ℕ) (J : Finset ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hWord : 1 < 2 ^ E.W) (hNj : Nj < 2 ^ E.W)
    (hSpan : arrayBase + count < 2 ^ E.W) (hBitmapSpan : bitmapBase + Nj ≤ 2 ^ E.W)
    (hBound : ∀ j < count, g j < Nj)
    (hArray : state.regs 4 = arrayBase) (hCount : state.regs 13 = count) (hBitmapBase : state.regs 7 = bitmapBase)
    (hDigits : ∀ j < count, state.mem (arrayBase + j) = g j)
    (hBitmap : ∀ v < Nj, state.mem (bitmapBase + v) = hintTruth (v ∈ J))
    (hAt : At P base (hintTupleFilterStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 25) state (fun k out => k ≤ 11 * count * count + 13 * count + 5 ∧
      HintTupleFilterArgs arrayBase count bitmapBase out ∧ out.regs 12 = count ∧
      (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧
      (out.regs 1 = 1 ↔ StrictMono (fun i : Fin count => g i.val) ∧ ∀ i : Fin count, g i.val ∉ J) ∧
      out.mem = state.mem ∧ out.regs 14 = state.regs 14) := by
  classical
  obtain ⟨hInitAt, hLoopAt⟩ := At.seqStmt hAt
  change At P base hintTupleFilterInit at hInitAt
  change At P (base + 3) (hintTupleFilterLoop.compile (base + 3)) at hLoopAt
  obtain ⟨_, kI, sI, hRunI, hPcI, hCostI, hStateI⟩ := Sem.block P E base hintTupleFilterInit state hInitAt
    (by simp [hintTupleFilterInit, NoBranch, Instr.NoBranchI]) hPc
  have hMemoryI : sI.mem = state.mem := by rw [hStateI]; rfl
  have hContextI : sI.regs 14 = state.regs 14 := by rw [hStateI]; simp [hintTupleFilterInit, runBlock, execInstr]
  have hInvI : HintTupleFilterInv arrayBase count bitmapBase g sI.mem J 0 sI := by
    refine ⟨?_, ?_, ?_, rfl⟩
    · rw [hStateI]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hintTupleFilterInit, runBlock, execInstr, hArray, hCount, hBitmapBase, Nat.mod_eq_of_lt hWord]
    · rw [hStateI]
      simp [hintTupleFilterInit, runBlock, execInstr]
    · rw [hStateI]
      simp [hintTupleFilterInit, runBlock, execInstr, hintTruth, HintTupleGood, Nat.mod_eq_of_lt hWord]
  have hDigitsI : ∀ j < count, sI.mem (arrayBase + j) = g j := by rw [hMemoryI]; exact hDigits
  have hBitmapI : ∀ v < Nj, sI.mem (bitmapBase + v) = hintTruth (v ∈ J) := by rw [hMemoryI]; exact hBitmap
  obtain ⟨_, kL, out, hRunL, hPcL, hCostL, hInvL, hContextL⟩ :=
    hintTupleFilterLoop_sem arrayBase count bitmapBase Nj g J P E sI (base + 3) hWord hNj hSpan hBitmapSpan
      hBound hInvI hDigitsI hBitmapI hLoopAt hPcI
  refine ⟨hPc, kL + kI, out, hintIterate_then (step P E) hRunI hRunL, ?_, ?_, hInvL.args, hInvL.counter,
    ?_, ?_, hInvL.memory.trans hMemoryI, hContextL.trans hContextI⟩
  · simpa only [Nat.add_assoc] using hPcL
  · change kI = 3 at hCostI
    nlinarith only [hCostL, hCostI]
  · rw [hInvL.flag]
    simp only [hintTruth]
    split_ifs <;> simp
  · rw [hInvL.flag]
    simpa [hintTruth] using hintTupleGood_full count J g

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintTupleFilterStmt_sem
end S_HintTupleFilter20261120
section S_HintScanEntry20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintScanParent : List Instr := [.imm 3 16, .sub 11 14 3]

theorem hintScanParent_spec (E : RAMEnv) (state : RAMState) (parent : ℕ)
    (hEnd : parent + 16 < 2 ^ E.W) (hContext : state.regs 14 = parent + 16) :
    let out := runBlock hintScanParent E state
    out.pc = state.pc + 2 ∧ out.mem = state.mem ∧ out.regs 11 = parent ∧ out.regs 14 = parent + 16 := by
  have h16 : 16 < 2 ^ E.W := by omega
  have hParent : parent < 2 ^ E.W := by omega
  have hSub : parent + 16 + 2 ^ E.W - 16 = parent + 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ?_⟩ <;>
    simp [hintScanParent, runBlock, execInstr, hContext, Nat.mod_eq_of_lt h16, hSub,
      Nat.add_mod, Nat.mod_self, Nat.mod_eq_of_lt hParent]

def hintScanInput : List Instr := [.load 4 11, .imm 3 15, .add 3 14 3, .store 3 4, .load 13 4]

theorem hintScanInput_spec (E : RAMEnv) (state : RAMState) (parent context outsideBase count : ℕ)
    (hSpan : context + 15 < 2 ^ E.W) (hOutside : outsideBase < context) (hCount : count < 2 ^ E.W)
    (hContext : state.regs 14 = context) (hParent : state.regs 11 = parent)
    (hReadPointer : state.mem parent = outsideBase) (hReadCount : state.mem outsideBase = count) :
    let out := runBlock hintScanInput E state
    out.pc = state.pc + 5 ∧ out.mem = Function.update state.mem (context + 15) outsideBase ∧
      out.regs 4 = outsideBase ∧ out.regs 13 = count ∧ out.regs 11 = parent ∧ out.regs 14 = context := by
  have h15 : 15 < 2 ^ E.W := by omega
  have hBase : outsideBase < 2 ^ E.W := by omega
  have hNe : outsideBase ≠ context + 15 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [hintScanInput, runBlock, execInstr, hContext, hParent, hReadPointer, hReadCount,
      hNe, Nat.mod_eq_of_lt h15, Nat.mod_eq_of_lt hBase, Nat.mod_eq_of_lt hSpan, Nat.mod_eq_of_lt hCount]

def hintScanFields : List Instr := [.imm 15 1, .add 4 4 15, .imm 3 1, .add 3 11 3, .load 7 3]

theorem hintScanFields_spec (E : RAMEnv) (state : RAMState) (parent context outsideBase count bitmapBase : ℕ)
    (hWord : 1 < 2 ^ E.W) (hSpan : parent + 1 < 2 ^ E.W) (hArray : outsideBase + 1 < 2 ^ E.W)
    (hBitmap : bitmapBase < 2 ^ E.W)
    (hContext : state.regs 14 = context) (hParent : state.regs 11 = parent)
    (hPointer : state.regs 4 = outsideBase) (hCount : state.regs 13 = count)
    (hRead : state.mem (parent + 1) = bitmapBase) :
    let out := runBlock hintScanFields E state
    out.pc = state.pc + 5 ∧ out.mem = state.mem ∧
      HintTupleFilterArgs (outsideBase + 1) count bitmapBase out ∧ out.regs 14 = context := by
  refine ⟨?_, rfl, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [hintScanFields, runBlock, execInstr, hContext, hParent, hPointer, hCount, hRead,
      Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hSpan, Nat.mod_eq_of_lt hArray, Nat.mod_eq_of_lt hBitmap]

def hintScanReset : List Instr := [.imm 3 8, .add 3 14 3, .imm 8 0, .store 3 8]

theorem hintScanReset_spec (E : RAMEnv) (state : RAMState) (context arrayBase count bitmapBase : ℕ)
    (hSpan : context + 8 < 2 ^ E.W) (hContext : state.regs 14 = context)
    (hArgs : HintTupleFilterArgs arrayBase count bitmapBase state) :
    let out := runBlock hintScanReset E state
    out.pc = state.pc + 4 ∧ out.mem = Function.update state.mem (context + 8) 0 ∧
      HintTupleFilterArgs arrayBase count bitmapBase out ∧ out.regs 14 = context := by
  have h8 : 8 < 2 ^ E.W := by omega
  obtain ⟨h4, h13, h7, h15⟩ := hArgs
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp [hintScanReset, runBlock, execInstr, hContext, h4, h13, h7, h15,
      Nat.mod_eq_of_lt h8, Nat.mod_eq_of_lt hSpan]

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def hintScanEntryCode : List Instr := hintScanParent ++ hintScanInput ++ hintScanFields ++ hintScanReset
theorem hintScanEntryCode_length : hintScanEntryCode.length = 16 := rfl

theorem hintScanEntry_spec (E : RAMEnv) (G : HintGaussArea) (state : RAMState)
    (parent outsideBase count bitmapBase oldIndex : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hParent : parent + 16 = G.context) (hSource : G.hintList + G.hints + 2 * G.rows ≤ parent)
    (hOutsideSpan : outsideBase + 1 + count ≤ G.hintList) (hBitmapBefore : bitmapBase ≤ outsideBase)
    (hContext : state.regs 14 = G.context) (hHeader : HintGaussHeader G oldIndex state.mem)
    (hReadPointer : state.mem parent = outsideBase) (hReadBitmap : state.mem (parent + 1) = bitmapBase)
    (hReadCount : state.mem outsideBase = count) :
    let out := runBlock hintScanEntryCode E state
    out.pc = state.pc + 16 ∧ HintTupleFilterArgs (outsideBase + 1) count bitmapBase out ∧
      HintGaussHeader G 0 out.mem ∧ out.mem (G.context + 15) = outsideBase ∧ out.regs 14 = G.context ∧
      (∀ addr, addr ≠ G.context + 8 → addr ≠ G.context + 15 → out.mem addr = state.mem addr) := by
  have h0 := hGeometry.residual_before
  have h1 := hGeometry.lift_before
  have h2 := hGeometry.column_before
  have h3 := hGeometry.residualVec_before
  have h4 := hGeometry.kernelVec_before
  have h5 := hGeometry.span
  have hCtxSpan : G.context + 15 < 2 ^ E.W := by omega
  have hEnd : parent + 16 < 2 ^ E.W := by omega
  have hWord : 1 < 2 ^ E.W := hGeometry.word_bound
  have hParentSpec := hintScanParent_spec E state parent hEnd (hContext.trans hParent.symm)
  generalize hP : runBlock hintScanParent E state = sP at hParentSpec
  obtain ⟨hPcP, hMemP, hPtrP, hCtxP⟩ := hParentSpec
  have hReadPointerP : sP.mem parent = outsideBase := by rw [hMemP]; exact hReadPointer
  have hReadCountP : sP.mem outsideBase = count := by rw [hMemP]; exact hReadCount
  have hInputSpec := hintScanInput_spec E sP parent G.context outsideBase count hCtxSpan (by omega) (by omega)
    (hCtxP.trans hParent) hPtrP hReadPointerP hReadCountP
  generalize hI : runBlock hintScanInput E sP = sI at hInputSpec
  obtain ⟨hPcI, hMemI, hArrayI, hCountI, hParentI, hCtxI⟩ := hInputSpec
  have hReadBitmapI : sI.mem (parent + 1) = bitmapBase := by
    rw [hMemI, Function.update_of_ne (by omega : parent + 1 ≠ G.context + 15), hMemP]
    exact hReadBitmap
  have hFieldSpec := hintScanFields_spec E sI parent G.context outsideBase count bitmapBase hWord (by omega) (by omega)
    (by omega) hCtxI hParentI hArrayI hCountI hReadBitmapI
  generalize hF : runBlock hintScanFields E sI = sF at hFieldSpec
  obtain ⟨hPcF, hMemF, hArgsF, hCtxF⟩ := hFieldSpec
  have hResetSpec := hintScanReset_spec E sF G.context (outsideBase + 1) count bitmapBase (by omega) hCtxF hArgsF
  generalize hR : runBlock hintScanReset E sF = out at hResetSpec
  obtain ⟨hPcR, hMemR, hArgsR, hCtxR⟩ := hResetSpec
  have hRun : runBlock hintScanEntryCode E state = out := by
    rw [hintScanEntryCode, runBlock_append, runBlock_append, runBlock_append, hP, hI, hF, hR]
  have hMemory : out.mem = Function.update (Function.update state.mem (G.context + 15) outsideBase) (G.context + 8) 0 := by
    rw [hMemR, hMemF, hMemI, hMemP]
  have hHeaderOut : HintGaussHeader G 0 out.mem := by
    intro i hi
    by_cases hEq : i = 8
    · subst i
      simp [hMemory, hintGaussHeaderValue]
    · have hNe8 : G.context + i ≠ G.context + 8 := by omega
      have hNe15 : G.context + i ≠ G.context + 15 := by omega
      rw [hMemory, Function.update_of_ne hNe8, Function.update_of_ne hNe15, hHeader i hi]
      interval_cases i <;> first | rfl | omega
  have hPointerOut : out.mem (G.context + 15) = outsideBase := by
    simp [hMemory, show G.context + 15 ≠ G.context + 8 from by omega]
  have hFrame : ∀ addr, addr ≠ G.context + 8 → addr ≠ G.context + 15 → out.mem addr = state.mem addr := by
    intro addr hNe8 hNe15
    rw [hMemory, Function.update_of_ne hNe8, Function.update_of_ne hNe15]
  have hPcOut : out.pc = state.pc + 16 := by rw [hPcR, hPcF, hPcI, hPcP]
  simpa only [hRun] using And.intro hPcOut (And.intro hArgsR (And.intro hHeaderOut (And.intro hPointerOut (And.intro hCtxR hFrame))))

theorem hintScanEntry_sem (P : Program) (E : RAMEnv) (G : HintGaussArea) (state : RAMState)
    (base parent outsideBase count bitmapBase oldIndex : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hParent : parent + 16 = G.context) (hSource : G.hintList + G.hints + 2 * G.rows ≤ parent)
    (hOutsideSpan : outsideBase + 1 + count ≤ G.hintList) (hBitmapBefore : bitmapBase ≤ outsideBase)
    (hContext : state.regs 14 = G.context) (hHeader : HintGaussHeader G oldIndex state.mem)
    (hReadPointer : state.mem parent = outsideBase) (hReadBitmap : state.mem (parent + 1) = bitmapBase)
    (hReadCount : state.mem outsideBase = count) (hAt : At P base hintScanEntryCode) (hPc : state.pc = base) :
    Sem P E base (base + 16) state (fun k out => k = 16 ∧
      HintTupleFilterArgs (outsideBase + 1) count bitmapBase out ∧ HintGaussHeader G 0 out.mem ∧
      out.mem (G.context + 15) = outsideBase ∧ out.regs 14 = G.context ∧
      (∀ addr, addr ≠ G.context + 8 → addr ≠ G.context + 15 → out.mem addr = state.mem addr)) := by
  have hSpec := hintScanEntry_spec E G state parent outsideBase count bitmapBase oldIndex hGeometry hReserve hParent
    hSource hOutsideSpan hBitmapBefore hContext hHeader hReadPointer hReadBitmap hReadCount
  generalize hMid : runBlock hintScanEntryCode E state = mid at hSpec
  obtain ⟨_, hArgs, hHeaderOut, hPointer, hCtx, hFrame⟩ := hSpec
  have hNative := Sem.block P E base hintScanEntryCode state hAt
    (by simp [hintScanEntryCode, hintScanParent, hintScanInput, hintScanFields, hintScanReset, NoBranch, Instr.NoBranchI]) hPc
  apply Sem.mono hNative
  intro k out hOut
  obtain ⟨hK, hOut⟩ := hOut
  rw [hMid] at hOut
  subst out
  exact ⟨hK, hArgs, hHeaderOut, hPointer, hCtx, hFrame⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintScanEntry_sem
end S_HintScanEntry20261120
section S_HintOutsideTuples20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- The tuples accepted by the outside-set enumerator: ascending and avoiding
    the actual hint coordinates. No hint subset is enumerated. -/
def HintOutsideTuple (Nj : ℕ) (J : Finset ℕ) (r : ℕ) :=
  {g : Fin r → Fin Nj // StrictMono (fun i => (g i).val) ∧ ∀ i, (g i).val ∉ J}

def HintOutsideSet (Nj : ℕ) (J : Finset ℕ) (r : ℕ) :=
  {A : Finset ℕ // A ⊆ Finset.range Nj \ J ∧ A.card = r}

def hintTupleSet {Nj r : ℕ} (g : Fin r → Fin Nj) : Finset ℕ :=
  Finset.univ.image (fun i => (g i).val)

theorem hintTupleSet_card {Nj r : ℕ} (g : Fin r → Fin Nj)
    (hMono : StrictMono (fun i => (g i).val)) : (hintTupleSet g).card = r := by
  rw [hintTupleSet, Finset.card_image_of_injective _ hMono.injective, Finset.card_univ, Fintype.card_fin]

theorem hintTupleSet_subset {Nj r : ℕ} {J : Finset ℕ} (g : Fin r → Fin Nj)
    (hAvoid : ∀ i, (g i).val ∉ J) : hintTupleSet g ⊆ Finset.range Nj \ J := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (g i).isLt, hAvoid i⟩

theorem hintOutsideTuple_injective {Nj r : ℕ} {J : Finset ℕ}
    {g f : HintOutsideTuple Nj J r} (hEq : hintTupleSet g.val = hintTupleSet f.val) : g = f := by
  have hCard := hintTupleSet_card g.val g.property.1
  have hFirst := Finset.orderEmbOfFin_unique hCard
    (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) g.property.1
  have hSecond : (fun i => (f.val i).val) = (hintTupleSet g.val).orderEmbOfFin hCard := by
    apply Finset.orderEmbOfFin_unique hCard
    · intro i
      rw [hEq]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · exact f.property.1
  apply Subtype.ext
  funext i
  exact Fin.ext (congrFun (hFirst.trans hSecond.symm) i)

noncomputable def hintOutsideTupleCodec (Nj : ℕ) (J : Finset ℕ) (r : ℕ) :
    HintOutsideTuple Nj J r ≃ HintOutsideSet Nj J r := by
  let encode : HintOutsideTuple Nj J r → HintOutsideSet Nj J r := fun g =>
    ⟨hintTupleSet g.val, hintTupleSet_subset g.val g.property.2, hintTupleSet_card g.val g.property.1⟩
  apply Equiv.ofBijective encode
  constructor
  · intro g f hEq
    exact hintOutsideTuple_injective (congrArg Subtype.val hEq)
  · intro A
    let g : Fin r → Fin Nj := fun i => ⟨A.val.orderEmbOfFin A.property.2 i,
      Finset.mem_range.mp (Finset.mem_sdiff.mp (A.property.1 (A.val.orderEmbOfFin_mem A.property.2 i))).1⟩
    have hMono : StrictMono (fun i => (g i).val) := (A.val.orderEmbOfFin A.property.2).strictMono
    have hAvoid : ∀ i, (g i).val ∉ J := by
      intro i
      exact (Finset.mem_sdiff.mp (A.property.1 (A.val.orderEmbOfFin_mem A.property.2 i))).2
    refine ⟨⟨g, hMono, hAvoid⟩, ?_⟩
    apply Subtype.ext
    change Finset.univ.image (A.val.orderEmbOfFin A.property.2) = A.val
    exact A.val.image_orderEmbOfFin_univ A.property.2

theorem hintOutsideTupleCodec_val {Nj r : ℕ} {J : Finset ℕ} (g : HintOutsideTuple Nj J r) :
    (hintOutsideTupleCodec Nj J r g).val = hintTupleSet g.val := rfl

/-- The ambient enumeration has Nj^r tuples, independently of the hint count. -/
theorem hintOutsideTuple_count_le (Nj : ℕ) (J : Finset ℕ) (r : ℕ) :
    Nat.card (HintOutsideTuple Nj J r) ≤ Nj ^ r := by
  have hh : Nat.card (HintOutsideTuple Nj J r) ≤ Nat.card (Fin r → Fin Nj) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using hh

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintOutsideTupleCodec
#print axioms LinearSetReconciliation327.Main.hintOutsideTuple_count_le
end S_HintOutsideTuples20261120
section S_HintScanJudge20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintTupleAccept {Nj r : ℕ} (J : Finset ℕ) (outside : Fin r → Fin Nj) : Prop :=
  StrictMono (fun j => (outside j).val) ∧ ∀ j, (outside j).val ∉ J

def hintScanSuccess (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj r : ℕ) (outside : Fin r → Fin Nj)
    (v : HintVec G.rows) : Prop :=
  hintTupleAccept (Finset.univ.image (fun j => (coords j).val)) outside ∧
    ∃! C : Finset ℕ, hintFamilyClass G coords beta Nj r (hintTupleSet outside) v C

def HintScanWitness (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (Nj r : ℕ) (A : Finset ℕ)
    (v : HintVec G.rows) (out : RAMState) : Prop :=
  out.regs 1 = 1 → ∃ z : HintVec G.hints,
    (∀ t : Fin G.hints, out.mem (G.kernelVec + t.val) = (z t).val) ∧
    hintFamilyClass G coords beta Nj r A v (hintBitsSet (fun j => (coords j).val) z ∪ A) ∧
    ∀ C : Finset ℕ, hintFamilyClass G coords beta Nj r A v C →
      C = hintBitsSet (fun j => (coords j).val) z ∪ A

def hintScanJudgeStmt : Stmt := .seq (.code hintScanEntryCode)
  (.seq hintTupleFilterStmt (.ite (.neqz 1) hintFamilyInputCallStmt (.code [])))
theorem hintScanJudgeStmt_len : hintScanJudgeStmt.len = 596 := rfl

theorem hintScanJudgeStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (r parent outsideBase bitmapBase oldIndex Nj : ℕ) (outside : Fin r → Fin Nj)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps) (v : HintVec G.rows)
    (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hGeometry : HintGaussGeometry E G) (hReserve : G.context + 16 ≤ G.residual)
    (hParent : parent + 16 = G.context) (hSource : G.hintList + G.hints + 2 * G.rows ≤ parent)
    (hInj : Function.Injective coords) (hHintValid : ∀ j, (coords j).val < Nj) (hNj : Nj ≤ G.buckets)
    (hOutsideSpan : outsideBase + 1 + r ≤ G.hintList) (hBitmapSpan : bitmapBase + Nj ≤ outsideBase)
    (hHint : ∀ j : Fin G.hints, state.mem (G.hintList + j.val) = (coords j).val)
    (hHeader : HintGaussHeader G oldIndex state.mem) (hFits : HintGaussHeaderFits E G 0)
    (hContext : state.regs 14 = G.context)
    (hReadPointer : state.mem parent = outsideBase) (hReadBitmap : state.mem (parent + 1) = bitmapBase)
    (hReadCount : state.mem outsideBase = r)
    (hOutside : ∀ j : Fin r, state.mem (outsideBase + 1 + j.val) = (outside j).val)
    (hBitmap : ∀ q < Nj, state.mem (bitmapBase + q) = hintTruth (q ∈ Finset.univ.image (fun j => (coords j).val)))
    (hVector : ∀ s : Fin G.rows, state.mem (G.hintList + G.hints + G.rows + s.val) = (v s).val)
    (hSteps : 0 < G.steps) (hCoeffSpan : (G.row + 1) * G.steps * G.buckets ≤ 2 ^ E.W)
    (hCoeff : ∀ c : Fin G.buckets, ∀ s : Fin G.rows,
      E.coeff G.node (G.row * G.steps * G.buckets + c.val + s.val * G.buckets) =
        (beta ⟨s.val, s.isLt.trans_le hPrefix⟩ c).val)
    (hAt : At P base (hintScanJudgeStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 596) state (fun k out =>
      k ≤ 11 * r * r + 13 * r + 23 + (9 * G.rows + 23 + (20 * G.rows + 50) * r + 512 * (G.rows + G.hints + 1) ^ 3) ∧
      (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧
      (out.regs 1 = 1 ↔ hintScanSuccess G coords beta Nj r outside v) ∧
      HintScanWitness G coords beta Nj r (hintTupleSet outside) v out ∧
      (∃ index, HintGaussHeader G index out.mem) ∧
      (∀ addr, (addr < G.hintList + G.hints ∨ G.hintList + G.hints + G.rows ≤ addr) →
        (addr < G.context ∨ G.pivotRow + G.rows ≤ addr) → out.mem addr = state.mem addr) ∧ out.regs 14 = G.context) := by
  classical
  let J := Finset.univ.image (fun j => (coords j).val)
  let B := 9 * G.rows + 23 + (20 * G.rows + 50) * r + 512 * (G.rows + G.hints + 1) ^ 3
  have h0 := hGeometry.header_before
  have h1 := hGeometry.residual_before
  have h2 := hGeometry.lift_before
  have h3 := hGeometry.column_before
  have h4 := hGeometry.residualVec_before
  have h5 := hGeometry.kernelVec_before
  have h6 := hGeometry.span
  have hNjWord : Nj < 2 ^ E.W := hNj.trans_lt (hFits.values 12 (by decide))
  obtain ⟨hEntryAt, hRestAt⟩ := At.seqStmt hAt
  change At P base hintScanEntryCode at hEntryAt
  change At P (base + 16) ((Stmt.seq hintTupleFilterStmt (.ite (.neqz 1) hintFamilyInputCallStmt (.code []))).compile (base + 16)) at hRestAt
  obtain ⟨hFilterAt, hBranchAt⟩ := At.seqStmt hRestAt
  change At P (base + 16) (hintTupleFilterStmt.compile (base + 16)) at hFilterAt
  change At P (base + 41) ((Stmt.ite (.neqz 1) hintFamilyInputCallStmt (.code [])).compile (base + 41)) at hBranchAt
  obtain ⟨_, kE, sE, hRunE, hPcE, hCostE, hArgsE, hHeaderE, hPointerE, hContextE, hFrameE⟩ :=
    hintScanEntry_sem P E G state base parent outsideBase r bitmapBase oldIndex hGeometry hReserve hParent hSource
      hOutsideSpan (by omega) hContext hHeader hReadPointer hReadBitmap hReadCount hEntryAt hPc
  let digits : ℕ → ℕ := fun j => if hj : j < r then (outside ⟨j, hj⟩).val else 0
  have hDigitsE : ∀ j < r, sE.mem (outsideBase + 1 + j) = digits j := by
    intro j hj
    rw [hFrameE _ (by omega) (by omega)]
    simpa only [digits, dif_pos hj] using hOutside ⟨j, hj⟩
  have hBitmapE : ∀ q < Nj, sE.mem (bitmapBase + q) = hintTruth (q ∈ J) := by
    intro q hq
    rw [hFrameE _ (by omega) (by omega)]
    exact hBitmap q hq
  have hBound : ∀ j < r, digits j < Nj := by intro j hj; simpa only [digits, dif_pos hj] using (outside ⟨j, hj⟩).isLt
  obtain ⟨_, kF, sF, hRunF, hPcF, hCostF, _, _, hBitF, hValidF, hMemoryF, hContextF⟩ :=
    hintTupleFilterStmt_sem (outsideBase + 1) r bitmapBase Nj digits J P E sE (base + 16) hGeometry.word_bound hNjWord
      (by omega) (by omega) hBound hArgsE.array hArgsE.count_value hArgsE.bitmap hDigitsE hBitmapE hFilterAt hPcE
  have hValid : sF.regs 1 = 1 ↔ hintTupleAccept J outside := by
    simpa [digits, hintTupleAccept] using hValidF
  have hLow : ∀ addr, addr < G.context → sF.mem addr = state.mem addr := by
    intro addr ha
    rw [hMemoryF, hFrameE addr (by omega) (by omega)]
  have hHeaderF : HintGaussHeader G 0 sF.mem := by rw [hMemoryF]; exact hHeaderE
  have hPointerF : sF.mem (G.context + 15) = outsideBase := by rw [hMemoryF]; exact hPointerE
  have hContextF' : sF.regs 14 = G.context := hContextF.trans hContextE
  let Q : ℕ → RAMState → Prop := fun k out => k ≤ B + 2 ∧
    (out.regs 1 = 0 ∨ out.regs 1 = 1) ∧ (out.regs 1 = 1 ↔ hintScanSuccess G coords beta Nj r outside v) ∧
    HintScanWitness G coords beta Nj r (hintTupleSet outside) v out ∧
    (∃ index, HintGaussHeader G index out.mem) ∧
    (∀ addr, (addr < G.hintList + G.hints ∨ G.hintList + G.hints + G.rows ≤ addr) →
      (addr < G.context ∨ G.pivotRow + G.rows ≤ addr) → out.mem addr = sF.mem addr) ∧ out.regs 14 = G.context
  have hBranch : Sem P E (base + 41) (base + 596) sF Q := by
    apply Sem.ite P E (base + 41) (.neqz 1) hintFamilyInputCallStmt (.code []) sF Q hBranchAt hGeometry.word_bound hPcF
    · intro hGo
      change Sem P E (base + 42) (base + 594) {sF with pc := base + 42}
        (fun k out => Q (1 + k + 1) {out with pc := base + 596})
      have hGood : hintTupleAccept J outside := hValid.mp (hBitF.resolve_left hGo)
      let outsideK : Fin r → Fin G.buckets := fun j => ⟨(outside j).val, (outside j).isLt.trans_le hNj⟩
      have hOutsideInj : Function.Injective outsideK := by
        intro i j hEq
        have hVal : (outsideK i).val = (outsideK j).val := congrArg (fun x : Fin G.buckets => x.val) hEq
        exact hGood.1.injective hVal
      have hSeparate : Disjoint (Finset.univ.image (fun j => (outsideK j).val)) J := by
        apply Finset.disjoint_left.mpr
        intro q hq hqJ
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
        exact hGood.2 j hqJ
      have hHintF : ∀ j : Fin G.hints, sF.mem (G.hintList + j.val) = (coords j).val := by
        intro j; rw [hLow _ (by have := j.isLt; omega)]; exact hHint j
      have hOutsideF : ∀ j : Fin r, sF.mem (outsideBase + 1 + j.val) = (outsideK j).val := by
        intro j; rw [hLow _ (by have := j.isLt; omega)]; exact hOutside j
      have hVectorF : ∀ s : Fin G.rows, sF.mem (G.hintList + G.hints + G.rows + s.val) = (v s).val := by
        intro s; rw [hLow _ (by have := s.isLt; omega)]; exact hVector s
      have hCall := hintFamilyInputCall_sem G coords r outsideBase outsideK hOutsideInj beta hPrefix v Nj
        P E {sF with pc := base + 42} (base + 42) hGeometry hReserve (by omega) hInj hHintValid
        (fun j => (outside j).isLt) hSeparate hHintF hHeaderF hFits hContextF' hPointerF
        (by rw [hLow _ (by omega)]; exact hReadCount) hOutsideSpan hOutsideF hVectorF hSteps hCoeffSpan hCoeff
        (at_ite hBranchAt).2.2.1 rfl
      apply Sem.mono hCall
      intro k out hOut
      obtain ⟨hCost, hBit, hUnique, hWitness, hHeaderOut, hFrame, hCtx⟩ := hOut
      change Q (1 + k + 1) {out with pc := base + 596}
      dsimp only [Q]
      refine ⟨by dsimp only [B]; omega, hBit, ?_, hWitness, ⟨G.hints, hHeaderOut⟩, hFrame, hCtx⟩
      exact ⟨fun hs => ⟨hGood, hUnique.mp hs⟩, fun hs => hUnique.mpr hs.2⟩
    · intro hStop
      change Sem P E (base + 595) (base + 595) {sF with pc := base + 595}
        (fun k out => Q (1 + k + 1) {out with pc := base + 596})
      have hZero : sF.regs 1 = 0 := by change ¬ sF.regs 1 ≠ 0 at hStop; exact not_not.mp hStop
      have hBad : ¬ hintTupleAccept J outside := by intro hGood; have := hValid.mpr hGood; omega
      have hNative := Sem.block P E (base + 595) [] {sF with pc := base + 595}
        (at_ite hBranchAt).2.2.2.2.1 (by trivial) rfl
      apply Sem.mono hNative
      intro k out hOut
      obtain ⟨hCost, rfl⟩ := hOut
      change Q (1 + k + 1) {sF with pc := base + 596}
      dsimp only [Q]
      refine ⟨by change k = 0 at hCost; omega, Or.inl hZero, ?_, ?_, ⟨0, hHeaderF⟩, ?_, hContextF'⟩
      · exact ⟨fun hs => by simp_all, fun hs => False.elim (hBad hs.1)⟩
      · intro hs
        simp_all
      · intro addr _ _
        rfl
  obtain ⟨_, kB, out, hRunB, hPcB, hCostB, hBitB, hUniqueB, hWitnessB, hHeaderB, hFrameB, hContextB⟩ := hBranch
  refine ⟨hPc, kB + (kF + kE), out,
    hintIterate_then (step P E) (hintIterate_then (step P E) hRunE hRunF) hRunB, hPcB, ?_, hBitB, hUniqueB,
    hWitnessB, hHeaderB, ?_, hContextB⟩
  · dsimp only [B] at hCostB
    omega
  · intro addr hRhs hGauss
    rw [hFrameB addr hRhs hGauss, hMemoryF]
    apply hFrameE addr
    · rcases hGauss with hBefore | hAfter <;> omega
    · rcases hGauss with hBefore | hAfter <;> omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintScanJudgeStmt_sem
end S_HintScanJudge20261120


