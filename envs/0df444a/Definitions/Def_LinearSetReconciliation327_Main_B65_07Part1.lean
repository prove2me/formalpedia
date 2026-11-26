-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_07Part1
-- name    : LinearSetReconciliation327_Main_B65_07Part1
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T05:01:48.017246+00:00
-- url     : https://prove2.me/theorems/5401c7e6-d4dc-42df-8987-d1919e1f8035
-- title:
--   Theorem 6.5 supporting machine proof B65_07Part1
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_HintCRCode20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintLoopBudget20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintUpdateExport20261120
import Definitions.Def_LinearSetReconciliation327_Main_B65_06
import Definitions.Def_LinearSetReconciliation327_Main_B65_06RowResult
set_option autoImplicit false

section S_HintRowSizing20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRowSizingMin : List Instr :=
  [.sub 8 4 1, .imm 15 1, .lt 9 8 5, .bxor 10 9 15, .mul 8 8 9, .mul 10 5 10, .add 8 8 10]
def hintRowSizingTable : List Instr := [.add 5 5 15, .mul 7 5 1, .add 7 6 7]

theorem hintRowSizingMin_spec (E : RAMEnv) (state : RAMState) (Nj BY h : ℕ)
    (hWord : 1 < 2 ^ E.W) (hLe : h ≤ Nj) (hNj : Nj < 2 ^ E.W) (hBY : BY < 2 ^ E.W)
    (h4 : state.regs 4 = Nj) (h5 : state.regs 5 = BY) (h1 : state.regs 1 = h) :
    let out := runBlock hintRowSizingMin E state
    out.pc = state.pc + 7 ∧ out.mem = state.mem ∧ out.regs 8 = min BY (Nj - h) ∧
      out.regs 15 = 1 ∧ (∀ r : Fin 16, r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 15 → out.regs r = state.regs r) := by
  have hShift : Nj + 2 ^ E.W - h = (Nj - h) + 2 ^ E.W := by omega
  have hDiff : Nj - h < 2 ^ E.W := by omega
  have hSub : (Nj + 2 ^ E.W - h) % 2 ^ E.W = Nj - h := by
    rw [hShift, Nat.add_mod_right, Nat.mod_eq_of_lt hDiff]
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · simp [hintRowSizingMin, runBlock, execInstr]
  · by_cases hh : Nj - h < BY
    · simp [hintRowSizingMin, runBlock, execInstr, h4, h5, h1, hSub, hh,
        min_eq_right hh.le, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hDiff]
    · simp [hintRowSizingMin, runBlock, execInstr, h4, h5, h1, hSub, hh,
        min_eq_left (Nat.le_of_not_gt hh), Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hBY]
  · simp [hintRowSizingMin, runBlock, execInstr, Nat.mod_eq_of_lt hWord]
  · intro r h8 h9 h10 h15
    simp [hintRowSizingMin, runBlock, execInstr, h8, h9, h10, h15]

theorem hintRowSizingTable_spec (E : RAMEnv) (state : RAMState) (table BY h : ℕ)
    (hStride : BY + 1 < 2 ^ E.W) (hTable : table + (BY + 1) * h < 2 ^ E.W)
    (h1 : state.regs 1 = h) (h5 : state.regs 5 = BY) (h6 : state.regs 6 = table)
    (h15 : state.regs 15 = 1) :
    let out := runBlock hintRowSizingTable E state
    out.pc = state.pc + 3 ∧ out.mem = state.mem ∧ out.regs 7 = table + (BY + 1) * h ∧
      (∀ r : Fin 16, r ≠ 5 → r ≠ 7 → out.regs r = state.regs r) := by
  have hMul : (BY + 1) * h < 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [hintRowSizingTable, runBlock, execInstr]
  · simp [hintRowSizingTable, runBlock, execInstr, h1, h5, h6, h15,
      Nat.mod_eq_of_lt hStride, Nat.mod_eq_of_lt hMul, Nat.mod_eq_of_lt hTable]
  · intro r h5' h7
    simp [hintRowSizingTable, runBlock, execInstr, h5', h7]


def hintRowSizingFetch : List Instr :=
  hintParentLoad 4 2 ++ hintParentLoad 5 12 ++ hintParentLoad 6 13
def hintRowSizingWrite : List Instr :=
  [.imm 3 4, .add 3 11 3, .store 3 8, .imm 3 5, .add 3 11 3, .store 3 7,
    .imm 3 1, .add 3 14 3, .store 3 1]
def hintRowSizingCode : List Instr :=
  hintScanParent ++ hintRowSizingFetch ++ hintRowSizingMin ++ hintRowSizingTable ++ hintRowSizingWrite

theorem hintRowSizingCode_length : hintRowSizingCode.length = 30 := rfl

def hintRowSizedMem (mem : ℕ → ℕ) (parent Nj BY table h : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update mem (parent + 4) (min BY (Nj - h)))
    (parent + 5) (table + (BY + 1) * h)) (parent + 17) h

theorem hintRowSizingWrite_spec (E : RAMEnv) (state : RAMState) (parent h limit lookup : ℕ)
    (hSpan : parent + 29 < 2 ^ E.W)
    (h11 : state.regs 11 = parent) (h14 : state.regs 14 = parent + 16)
    (h1 : state.regs 1 = h) (h8 : state.regs 8 = limit) (h7 : state.regs 7 = lookup) :
    let out := runBlock hintRowSizingWrite E state
    out.pc = state.pc + 9 ∧
      out.mem = Function.update (Function.update (Function.update state.mem (parent + 4) limit)
        (parent + 5) lookup) (parent + 17) h ∧
      out.regs 14 = parent + 16 := by
  have h1Fit : 1 < 2 ^ E.W := by omega
  have h4Fit : 4 < 2 ^ E.W := by omega
  have h5Fit : 5 < 2 ^ E.W := by omega
  have hAddr4 : parent + 4 < 2 ^ E.W := by omega
  have hAddr5 : parent + 5 < 2 ^ E.W := by omega
  have hAddr17 : parent + 16 + 1 < 2 ^ E.W := by omega
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [hintRowSizingWrite, runBlock, execInstr, h11, h14, h1, h8, h7,
      Nat.mod_eq_of_lt h1Fit, Nat.mod_eq_of_lt h4Fit, Nat.mod_eq_of_lt h5Fit,
      Nat.mod_eq_of_lt hAddr4, Nat.mod_eq_of_lt hAddr5, Nat.mod_eq_of_lt hAddr17]

theorem hintRowSizingCode_spec (E : RAMEnv) (state : RAMState) (parent Nj BY table h : ℕ)
    (hSpan : parent + 29 < 2 ^ E.W) (hCtx : state.regs 14 = parent + 16)
    (hCount : h ≤ Nj) (hNj : Nj < 2 ^ E.W) (hStride : BY + 1 < 2 ^ E.W)
    (hTable : table + (BY + 1) * h < 2 ^ E.W) (hLen : state.regs 1 = h)
    (hReadNj : state.mem (parent + 2) = Nj) (hReadBY : state.mem (parent + 12) = BY)
    (hReadTable : state.mem (parent + 13) = table) :
    let out := runBlock hintRowSizingCode E state
    out.pc = state.pc + 30 ∧ out.mem = hintRowSizedMem state.mem parent Nj BY table h ∧
      out.regs 14 = parent + 16 := by
  have hWord : 1 < 2 ^ E.W := by omega
  have hBY : BY < 2 ^ E.W := by omega
  have hTableFit : table < 2 ^ E.W := by omega
  have hParent := hintScanParent_spec E state parent (by omega) hCtx
  have hLenP : (runBlock hintScanParent E state).regs 1 = h := by
    simp [hintScanParent, runBlock, execInstr, hLen]
  generalize hP : runBlock hintScanParent E state = sP at hParent hLenP
  obtain ⟨hPcP, hMemP, h11P, h14P⟩ := hParent
  have hFetch : let out := runBlock hintRowSizingFetch E sP
      out.pc = sP.pc + 9 ∧ out.mem = sP.mem ∧
        out.regs 4 = Nj ∧ out.regs 5 = BY ∧ out.regs 6 = table ∧ out.regs 1 = h ∧
        out.regs 11 = parent ∧ out.regs 14 = parent + 16 := by
    have h2 : 2 < 2 ^ E.W := by omega
    have h12 : 12 < 2 ^ E.W := by omega
    have h13 : 13 < 2 ^ E.W := by omega
    have hA2 : parent + 2 < 2 ^ E.W := by omega
    have hA12 : parent + 12 < 2 ^ E.W := by omega
    have hA13 : parent + 13 < 2 ^ E.W := by omega
    refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hintRowSizingFetch, hintParentLoad, runBlock, execInstr, h11P, h14P, hLenP, hMemP,
        hReadNj, hReadBY, hReadTable, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h12, Nat.mod_eq_of_lt h13,
        Nat.mod_eq_of_lt hA2, Nat.mod_eq_of_lt hA12, Nat.mod_eq_of_lt hA13,
        Nat.mod_eq_of_lt hNj, Nat.mod_eq_of_lt hBY, Nat.mod_eq_of_lt hTableFit]
  generalize hF : runBlock hintRowSizingFetch E sP = sF at hFetch
  obtain ⟨hPcF, hMemF, h4F, h5F, h6F, h1F, h11F, h14F⟩ := hFetch
  have hMin := hintRowSizingMin_spec E sF Nj BY h hWord hCount hNj hBY h4F h5F h1F
  generalize hM : runBlock hintRowSizingMin E sF = sM at hMin
  obtain ⟨hPcM, hMemM, h8M, h15M, hRegsM⟩ := hMin
  have hSameM (r : Fin 16) (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10) (h15 : r ≠ 15)
      (value : ℕ) (hEq : sF.regs r = value) : sM.regs r = value := (hRegsM r h8 h9 h10 h15).trans hEq
  have hLoc := hintRowSizingTable_spec E sM table BY h hStride hTable
    (hSameM 1 (by decide) (by decide) (by decide) (by decide) _ h1F)
    (hSameM 5 (by decide) (by decide) (by decide) (by decide) _ h5F)
    (hSameM 6 (by decide) (by decide) (by decide) (by decide) _ h6F) h15M
  generalize hT : runBlock hintRowSizingTable E sM = sT at hLoc
  obtain ⟨hPcT, hMemT, h7T, hRegsT⟩ := hLoc
  have h1T := (hRegsT 1 (by decide) (by decide)).trans
    (hSameM 1 (by decide) (by decide) (by decide) (by decide) _ h1F)
  have h11T := (hRegsT 11 (by decide) (by decide)).trans
    (hSameM 11 (by decide) (by decide) (by decide) (by decide) _ h11F)
  have h14T := (hRegsT 14 (by decide) (by decide)).trans
    (hSameM 14 (by decide) (by decide) (by decide) (by decide) _ h14F)
  have h8T := (hRegsT 8 (by decide) (by decide)).trans h8M
  have hWrite := hintRowSizingWrite_spec E sT parent h (min BY (Nj - h)) (table + (BY + 1) * h)
    hSpan h11T h14T h1T h8T h7T
  generalize hW : runBlock hintRowSizingWrite E sT = out at hWrite
  obtain ⟨hPcW, hMemW, hCtxW⟩ := hWrite
  have hRun : runBlock hintRowSizingCode E state = out := by
    rw [hintRowSizingCode, runBlock_append, runBlock_append, runBlock_append, runBlock_append, hP, hF, hM, hT, hW]
  rw [hRun]
  exact ⟨by omega, by rw [hMemW, hMemT, hMemM, hMemF, hMemP, hintRowSizedMem], hCtxW⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowSizingCode_spec
end S_HintRowSizing20261120
section S_HintRowPrepare20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintRowSizedMem_frame (mem : ℕ → ℕ) (parent Nj BY table h addr : ℕ)
    (h4 : addr ≠ parent + 4) (h5 : addr ≠ parent + 5) (h17 : addr ≠ parent + 17) :
    hintRowSizedMem mem parent Nj BY table h addr = mem addr := by
  simp only [hintRowSizedMem, Function.update_of_ne h4, Function.update_of_ne h5, Function.update_of_ne h17]

structure HintRowPrepareMetadata (G : HintGaussArea)
    (parent Nj m outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount : ℕ)
    (memory : ℕ → ℕ) : Prop where
  gather : HintGatherMetadata parent G.hintList hintSource m G.row G.node Nj memory
  outside_pointer : memory parent = outsideBase
  bitmap_pointer : memory (parent + 1) = bitmapBase
  outside_count : memory outsideBase = oldCount
  transcript_pointer : memory (parent + 9) = transcriptSource
  hint_limit : memory (parent + 6) = BX
  outside_limit : memory (parent + 12) = BY
  threshold_table : memory (parent + 13) = table
  header : ∃ index, ∀ i < 14, i ≠ 1 → memory (G.context + i) = hintGaussHeaderValue G index i

structure HintRowPrepared (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets) (v : HintVec G.rows)
    (parent Nj outsideBase bitmapBase BX BY table oldCount : ℕ) (state : RAMState) : Prop where
  input : HintRowInput G coords Nj oldCount parent outsideBase bitmapBase v state.mem
  header : ∃ index, HintGaussHeader G index state.mem
  context : state.regs 14 = G.context
  max_count : state.mem (parent + 4) = min BY (Nj - G.hints)
  wait_table : state.mem (parent + 5) = table + (BY + 1) * G.hints
  hint_limit : state.mem (parent + 6) = BX

def hintRowPrepareStmt : Stmt := .seq hintRowGatherStmt
  (.seq (.code hintRowSizingCode) hintTranscriptStmt)

theorem hintRowPrepareStmt_len : hintRowPrepareStmt.len = 95 := rfl

/-- Prepare the actual inputs for the row workers from the real node hint bitmap
and column-major transcript. The initial hint count and row scratch may be arbitrary. -/
theorem hintRowPrepareStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets) (v : HintVec G.rows)
    (N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount : ℕ)
    (π : Equiv.Perm (Fin N)) (J : Finset ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hParent : parent + 16 = G.context) (hContext : state.regs 14 = G.context)
    (hFits : HintGaussHeaderFits E G 0)
    (hMeta : HintRowPrepareMetadata G parent Nj m outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount state.mem)
    (hm : 0 < m) (hRow : G.row < m) (hNj : Nj = rowLen N m G.row)
    (hHintLen : (hintRowMembers N m G.row π J).length = G.hints)
    (hCoords : ∀ i : Fin G.hints, (coords i).val =
      (hintRowMembers N m G.row π J)[i.val]'(hHintLen.symm ▸ i.isLt))
    (hRowsFit : m < 2 ^ E.W) (hNjFit : Nj < 2 ^ E.W)
    (hBYFit : BY + 1 < 2 ^ E.W) (hTableFit : table + (BY + 1) * G.hints < 2 ^ E.W)
    (hOutside : outsideBase < G.hintList)
    (hGatherEnd : G.hintList + Nj ≤ parent)
    (hDestEnd : G.hintList + G.hints + 2 * G.rows ≤ parent)
    (hHintSeparate : parent ≤ hintSource) (hHintFit : hintSource < 2 ^ E.W)
    (hHintSpan : hintSource + N ≤ 2 ^ E.W)
    (hTranscriptSeparate : G.hintList + G.hints + 2 * G.rows ≤ transcriptSource)
    (hTranscriptOutsideGather : G.hintList + Nj ≤ transcriptSource)
    (hTranscriptAfterHeader : parent + 18 ≤ transcriptSource)
    (hTranscriptFit : transcriptSource < 2 ^ E.W)
    (hTranscriptSpan : ∀ t : Fin G.rows, transcriptSource + t.val * m < 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv G.node p.val = (π.symm p).val)
    (hBits : ∀ c : Fin N, state.mem (hintSource + c.val) = hintTruth (c.val ∈ J))
    (hTranscript : ∀ t : Fin G.rows, state.mem (transcriptSource + t.val * m) = (v t).val)
    (hAt : At P base (hintRowPrepareStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 95) state (fun k out => k ≤ 12 * Nj + 9 * G.rows + 78 ∧
      HintRowPrepared G coords v parent Nj outsideBase bitmapBase BX BY table oldCount out ∧
      CRMemFrame G.hintList (parent + 18) state.mem out.mem) := by
  have hSpan := hFits.span
  have hHL : G.hints ≤ Nj := by
    rw [← hHintLen, hNj]
    exact hintGatherList_length_le _ _
  have hMetaGather : HintGatherMetadata parent G.hintList hintSource m G.row G.node
      (rowLen N m G.row) state.mem := hNj ▸ hMeta.gather
  obtain ⟨hGatherAt, hRestAt⟩ := At.seqStmt hAt
  change At P base (hintRowGatherStmt.compile base) at hGatherAt
  change At P (base + 35) ((Stmt.seq (.code hintRowSizingCode) hintTranscriptStmt).compile (base + 35)) at hRestAt
  obtain ⟨hSizeAt, hTranscriptAt⟩ := At.seqStmt hRestAt
  change At P (base + 35) hintRowSizingCode at hSizeAt
  change At P (base + 65) (hintTranscriptStmt.compile (base + 65)) at hTranscriptAt
  obtain ⟨_, kG, sG, hRunG, hPcG, hCostG, hLenG, hListG, hFrameG, hCtxG⟩ :=
    hintRowGatherStmt_sem P E state N m G.row G.node parent G.hintList hintSource base π J hm hRow
      (by omega) (hContext.trans hParent.symm) hMetaGather (hFits.values 9 (by decide)) hHintFit hRowsFit
      (hFits.values 10 (by decide)) (by omega) (by omega) hHintSpan hPerm hBits hGatherAt hPc
  have hAfterG (addr : ℕ) (ha : parent ≤ addr) : sG.mem addr = state.mem addr :=
    hFrameG addr (Or.inr (by omega))
  have hSize := hintRowSizingCode_spec E sG parent Nj BY table G.hints (by omega) hCtxG hHL hNjFit hBYFit hTableFit
    (hLenG.trans hHintLen)
    ((hAfterG _ (by omega)).trans hMeta.gather.count_value)
    ((hAfterG _ (by omega)).trans hMeta.outside_limit)
    ((hAfterG _ (by omega)).trans hMeta.threshold_table)
  generalize hS : runBlock hintRowSizingCode E sG = sS at hSize
  obtain ⟨hPcS, hMemS, hCtxS⟩ := hSize
  have hRunS : (step P E)^[30] sG = sS := by
    have hh := iterate_runBlock_of_at P E hintRowSizingCode sG (by rwa [hPcG])
      (by simp [hintRowSizingCode, hintScanParent, hintRowSizingFetch, hintParentLoad,
        hintRowSizingMin, hintRowSizingTable, hintRowSizingWrite, NoBranch, Instr.NoBranchI])
    simpa only [hintRowSizingCode_length, hS] using hh
  have hUnchangedS (addr : ℕ) (h4 : addr ≠ parent + 4) (h5 : addr ≠ parent + 5) (h17 : addr ≠ parent + 17) :
      sS.mem addr = sG.mem addr := by
    rw [hMemS]
    exact hintRowSizedMem_frame _ _ _ _ _ _ _ h4 h5 h17
  have hHeaderS : ∃ index, HintGaussHeader G index sS.mem := by
    obtain ⟨index, hHead⟩ := hMeta.header
    refine ⟨index, ?_⟩
    intro i hi
    by_cases hEq : i = 1
    · subst i
      rw [show G.context + 1 = parent + 17 by omega, hMemS]
      simp [hintRowSizedMem, hintGaussHeaderValue]
    · rw [hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
      exact hHead i hi hEq
  obtain ⟨_, kT, out, hRunT, hPcT, hCostT, hObs, hHeaderOut, hCtxOut, hFrameT⟩ :=
    hintTranscriptStmt_sem G v parent transcriptSource m P E sS (base + 65)
      hParent (hCtxS.trans hParent) hHeaderS hFits hTranscriptFit hRowsFit
      (by rw [hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]; exact hMeta.transcript_pointer)
      (by rw [hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]; exact hMeta.gather.rows_value)
      hDestEnd hTranscriptSeparate hTranscriptSpan
      (by
        intro t
        rw [hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
        exact hTranscript t) hTranscriptAt (by omega)
  have hAfterT (addr : ℕ) (ha : parent ≤ addr) : out.mem addr = sS.mem addr :=
    hFrameT addr (Or.inr (by omega))
  refine ⟨hPc, kT + (30 + kG), out, hintIterate_then (step P E) (hintIterate_then (step P E) hRunG hRunS) hRunT,
    by omega, by omega, ⟨⟨?_, ?_, ?_, ?_, ?_, hObs⟩, hHeaderOut, hCtxOut, ?_, ?_, ?_⟩, ?_⟩
  · rw [hAfterT _ le_rfl, hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ le_rfl]
    exact hMeta.outside_pointer
  · rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
    exact hMeta.bitmap_pointer
  · rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
    exact hMeta.gather.count_value
  · rw [hFrameT _ (Or.inl (by omega)), hUnchangedS _ (by omega) (by omega) (by omega),
      hFrameG _ (Or.inl hOutside)]
    exact hMeta.outside_count
  · intro i
    have hi := i.isLt
    rw [hFrameT _ (Or.inl (by omega)), hUnchangedS _ (by omega) (by omega) (by omega)]
    exact (hListG i.val (hHintLen.symm ▸ hi)).trans (hCoords i).symm
  · rw [hAfterT _ (by omega), hMemS]
    simp [hintRowSizedMem, Function.update_of_ne (by omega : parent + 4 ≠ parent + 17),
      Function.update_of_ne (by omega : parent + 4 ≠ parent + 5)]
  · rw [hAfterT _ (by omega), hMemS]
    simp [hintRowSizedMem, Function.update_of_ne (by omega : parent + 5 ≠ parent + 17)]
  · rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
    exact hMeta.hint_limit
  · intro addr hAway
    rcases hAway with hBefore | hAfter
    · rw [hFrameT _ (Or.inl (by omega)), hUnchangedS _ (by omega) (by omega) (by omega), hFrameG _ (Or.inl hBefore)]
    · rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowPrepareStmt_sem
end S_HintRowPrepare20261120
section S_HintPreparedWorkers20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

theorem hintRowPrepared_image (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets)
    (N m : ℕ) (π : Equiv.Perm (Fin N)) (J : Finset ℕ) (hm : 0 < m) (hRow : G.row < m)
    (hLen : (hintRowMembers N m G.row π J).length = G.hints)
    (hCoords : ∀ i : Fin G.hints, (coords i).val =
      (hintRowMembers N m G.row π J)[i.val]'(hLen.symm ▸ i.isLt)) :
    Finset.univ.image (fun t => (coords t).val) = rowImage N m π G.row J := by
  classical
  ext q
  constructor
  · intro h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    rw [hCoords i]
    exact (hintRowMembers_mem N m G.row π J hm hRow _).mp (List.getElem_mem _)
  · intro h
    have hMem := (hintRowMembers_mem N m G.row π J hm hRow q).mpr h
    obtain ⟨i, hi, hq⟩ := List.mem_iff_getElem.mp hMem
    have hBound : i < G.hints := hLen ▸ hi
    exact Finset.mem_image.mpr ⟨⟨i, hBound⟩, Finset.mem_univ _, (hCoords ⟨i, hBound⟩).trans hq⟩

theorem hintPrepared_frames {E : RAMEnv} {G : HintGaussArea} {coords : Fin G.hints → Fin G.buckets}
    {beta : Fin G.steps → Fin G.buckets → ZMod 2} {hPrefix : G.rows ≤ G.steps}
    {Nj maxR parent outsideBase bitmapBase : ℕ}
    (hPublic : HintScanPublic E G coords beta hPrefix Nj maxR parent outsideBase bitmapBase) :
    bitmapBase ≤ G.hintList ∧ parent + 18 ≤ G.pivotRow + G.rows ∧
      (∀ addr, addr < bitmapBase ∨ G.pivotRow + G.rows ≤ addr →
        (addr < bitmapBase ∨ bitmapBase + Nj ≤ addr) ∧
        (addr < outsideBase ∨ outsideBase + 1 + maxR ≤ addr) ∧
        addr ≠ parent + 3 ∧ addr ≠ parent + 7 ∧ addr ≠ parent + 8 ∧
        (addr < G.hintList + G.hints ∨ G.hintList + G.hints + G.rows ≤ addr) ∧
        (addr < G.context ∨ G.pivotRow + G.rows ≤ addr)) := by
  have hBitmap := hPublic.bitmap_span
  have hOutside := hPublic.outside_span
  have hSource := hPublic.source
  have hParent := hPublic.parent_eq
  have hReserve := hPublic.reserve
  have h0 := hPublic.geometry.residual_before
  have h1 := hPublic.geometry.lift_before
  have h2 := hPublic.geometry.column_before
  have h3 := hPublic.geometry.residualVec_before
  have h4 := hPublic.geometry.kernelVec_before
  refine ⟨by omega, by omega, ?_⟩
  intro addr ha
  rcases ha with ha | ha
  · refine ⟨Or.inl ha, Or.inl (by omega), by omega, by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩
  · refine ⟨Or.inr (by omega), Or.inr (by omega), by omega, by omega, by omega, Or.inr (by omega), Or.inr ha⟩

def hintPreparedPredictStmt : Stmt := .seq hintRowPrepareStmt hintRowPredictStmt
def hintPreparedFinalStmt : Stmt := .seq hintRowPrepareStmt hintRowFinalStmt
theorem hintPreparedPredictStmt_len : hintPreparedPredictStmt.len = 1584 := rfl
theorem hintPreparedFinalStmt_len : hintPreparedFinalStmt.len = 1653 := rfl

theorem hintPreparedPredictStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets) (v : HintVec G.rows)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps) (c : ℕ)
    (N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount : ℕ)
    (π : Equiv.Perm (Fin N)) (J : Finset ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hContext : state.regs 14 = G.context)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj (min BY (Nj - G.hints)) parent outsideBase bitmapBase)
    (j : Fin m) (hRowValue : G.row = j.val) (hBX : BX < 2 ^ E.W)
    (hMeta : HintRowPrepareMetadata G parent Nj m outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount state.mem)
    (hm : 0 < m) (hRow : G.row < m) (hNj : Nj = rowLen N m G.row)
    (hHintLen : (hintRowMembers N m G.row π J).length = G.hints)
    (hCoords : ∀ i : Fin G.hints, (coords i).val =
      (hintRowMembers N m G.row π J)[i.val]'(hHintLen.symm ▸ i.isLt))
    (hRowsFit : m < 2 ^ E.W) (hNjFit : Nj < 2 ^ E.W)
    (hBYFit : BY + 1 < 2 ^ E.W) (hTableFit : table + (BY + 1) * G.hints < 2 ^ E.W)
    (hGatherEnd : G.hintList + Nj ≤ parent)
    (hHintSeparate : parent ≤ hintSource) (hHintFit : hintSource < 2 ^ E.W)
    (hHintSpan : hintSource + N ≤ 2 ^ E.W)
    (hTranscriptSeparate : G.hintList + G.hints + 2 * G.rows ≤ transcriptSource)
    (hTranscriptOutsideGather : G.hintList + Nj ≤ transcriptSource)
    (hTranscriptAfterHeader : parent + 18 ≤ transcriptSource)
    (hTranscriptFit : transcriptSource < 2 ^ E.W)
    (hTranscriptSpan : ∀ t : Fin G.rows, transcriptSource + t.val * m < 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv G.node p.val = (π.symm p).val)
    (hBits : ∀ c : Fin N, state.mem (hintSource + c.val) = hintTruth (c.val ∈ J))
    (hTranscript : ∀ t : Fin G.rows, state.mem (transcriptSource + t.val * m) = (v t).val)
    (hWaitTable : table + (BY + 1) * G.hints + min BY (Nj - G.hints) < 2 ^ E.W)
    (hLookup : ∀ r ≤ min BY (Nj - G.hints),
      E.det (table + (BY + 1) * G.hints + r) = min G.steps (sigma G.hints Nj r + c))
    (hCoeff : ∀ hNext : G.rows < G.steps, ∀ q : Fin G.buckets,
      E.coeff G.node ((G.row * G.steps + G.rows) * G.buckets + q.val) = (beta ⟨G.rows, hNext⟩ q).val)
    (hAt : At P base (hintPreparedPredictStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1584) state (fun k out =>
      k ≤ (hintRowOuterBudget G Nj (min BY (Nj - G.hints)) + 2) *
        (min BY (Nj - G.hints) + 1) + 12 * Nj + 9 * G.rows + 107 ∧
      hintRowOutput out = workerPredict N m G.steps G.buckets BX BY c j beta
        (rowImage N m π j.val J) (List.ofFn v) ∧
      out.regs 14 = G.context ∧ CRMemFrame bitmapBase (G.pivotRow + G.rows) state.mem out.mem) := by
  let maxR := min BY (Nj - G.hints)
  let tableAddr := table + (BY + 1) * G.hints
  have hh := hPublic.outside_span
  obtain ⟨hBitmapStart, hHeaderEnd, hZones⟩ := hintPrepared_frames hPublic
  have hImage := hintRowPrepared_image G coords N m π J hm hRow hHintLen hCoords
  have hNj' : rowLen N m j.val = Nj := by rw [← hRowValue, hNj]
  obtain ⟨hAtPrep, hAtWork⟩ := At.seqStmt hAt
  change At P base (hintRowPrepareStmt.compile base) at hAtPrep
  change At P (base + 95) (hintRowPredictStmt.compile (base + 95)) at hAtWork
  obtain ⟨_, kP, mid, hRunP, hPcP, hCostP, hp, hFrameP⟩ :=
    hintRowPrepareStmt_sem G coords v N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount π J
      P E state base hPublic.parent_eq hContext hPublic.fits hMeta hm hRow hNj hHintLen hCoords hRowsFit hNjFit
      hBYFit hTableFit (by omega) hGatherEnd hPublic.source hHintSeparate hHintFit hHintSpan
      hTranscriptSeparate hTranscriptOutsideGather hTranscriptAfterHeader hTranscriptFit hTranscriptSpan hPerm hBits hTranscript
      hAtPrep hPc
  obtain ⟨_, kW, out, hRunW, hPcW, hCostW, hOut, _, _, hCtxOut, hFrameW⟩ :=
    hintRowPredictStmt_sem G coords beta hPrefix N m Nj parent outsideBase bitmapBase maxR tableAddr BX BY c oldCount j v
      P E mid (base + 95) hPublic hp.input hp.header hp.context hNj' rfl hBX hp.hint_limit
      hp.max_count hp.wait_table hWaitTable hLookup hCoeff hAtWork hPcP
  have hOutput : hintRowOutput out = workerPredict N m G.steps G.buckets BX BY c j beta
      (rowImage N m π j.val J) (List.ofFn v) := by
    have hAlign : Finset.univ.image (fun t => (coords t).val) = rowImage N m π j.val J := hImage.trans (by rw [← hRowValue])
    simpa only [hAlign] using hOut
  refine ⟨hPc, kW + kP, out, hintIterate_then (step P E) hRunP hRunW, by omega,
    by dsimp only [maxR] at hCostW; omega, hOutput, hCtxOut, ?_⟩
  intro addr hAway
  obtain ⟨hB, hO, h3, _, _, hR, hG⟩ := hZones addr hAway
  rw [hFrameW addr hB hO h3 hR hG]
  apply hFrameP
  rcases hAway with hBefore | hAfter
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

theorem hintPreparedFinalStmt_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets) (v : HintVec G.rows)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount : ℕ)
    (π : Equiv.Perm (Fin N)) (J : Finset ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hContext : state.regs 14 = G.context)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj (min BY (Nj - G.hints)) parent outsideBase bitmapBase)
    (j : Fin m) (hRowValue : G.row = j.val) (hBX : BX < 2 ^ E.W)
    (hMeta : HintRowPrepareMetadata G parent Nj m outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount state.mem)
    (hm : 0 < m) (hRow : G.row < m) (hNj : Nj = rowLen N m G.row)
    (hHintLen : (hintRowMembers N m G.row π J).length = G.hints)
    (hCoords : ∀ i : Fin G.hints, (coords i).val =
      (hintRowMembers N m G.row π J)[i.val]'(hHintLen.symm ▸ i.isLt))
    (hRowsFit : m < 2 ^ E.W) (hNjFit : Nj < 2 ^ E.W)
    (hBYFit : BY + 1 < 2 ^ E.W) (hTableFit : table + (BY + 1) * G.hints < 2 ^ E.W)
    (hGatherEnd : G.hintList + Nj ≤ parent)
    (hHintSeparate : parent ≤ hintSource) (hHintFit : hintSource < 2 ^ E.W)
    (hHintSpan : hintSource + N ≤ 2 ^ E.W)
    (hTranscriptSeparate : G.hintList + G.hints + 2 * G.rows ≤ transcriptSource)
    (hTranscriptOutsideGather : G.hintList + Nj ≤ transcriptSource)
    (hTranscriptAfterHeader : parent + 18 ≤ transcriptSource)
    (hTranscriptFit : transcriptSource < 2 ^ E.W)
    (hTranscriptSpan : ∀ t : Fin G.rows, transcriptSource + t.val * m < 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv G.node p.val = (π.symm p).val)
    (hBits : ∀ c : Fin N, state.mem (hintSource + c.val) = hintTruth (c.val ∈ J))
    (hTranscript : ∀ t : Fin G.rows, state.mem (transcriptSource + t.val * m) = (v t).val)
    (hAt : At P base (hintPreparedFinalStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1653) state (fun k out =>
      k ≤ (hintFinalBudget G Nj (min BY (Nj - G.hints)) + 2) *
        (min BY (Nj - G.hints) + 1) + hintFinalBudget G Nj (min BY (Nj - G.hints)) +
        26 * Nj + 9 * G.rows + 18 * G.hints + 8 * min BY (Nj - G.hints) + 186 ∧
      (∀ q < Nj, out.mem (bitmapBase + q) = hintTruth (q ∈
        workerFinal N m G.steps G.buckets BX BY j beta (rowImage N m π j.val J) (List.ofFn v))) ∧
      out.regs 14 = G.context ∧ CRMemFrame bitmapBase (G.pivotRow + G.rows) state.mem out.mem) := by
  let maxR := min BY (Nj - G.hints)
  have hh := hPublic.outside_span
  obtain ⟨hBitmapStart, hHeaderEnd, hZones⟩ := hintPrepared_frames hPublic
  have hImage := hintRowPrepared_image G coords N m π J hm hRow hHintLen hCoords
  have hNj' : rowLen N m j.val = Nj := by rw [← hRowValue, hNj]
  obtain ⟨hAtPrep, hAtWork⟩ := At.seqStmt hAt
  change At P base (hintRowPrepareStmt.compile base) at hAtPrep
  change At P (base + 95) (hintRowFinalStmt.compile (base + 95)) at hAtWork
  obtain ⟨_, kP, mid, hRunP, hPcP, hCostP, hp, hFrameP⟩ :=
    hintRowPrepareStmt_sem G coords v N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount π J
      P E state base hPublic.parent_eq hContext hPublic.fits hMeta hm hRow hNj hHintLen hCoords hRowsFit hNjFit
      hBYFit hTableFit (by omega) hGatherEnd hPublic.source hHintSeparate hHintFit hHintSpan
      hTranscriptSeparate hTranscriptOutsideGather hTranscriptAfterHeader hTranscriptFit hTranscriptSpan hPerm hBits hTranscript
      hAtPrep hPc
  obtain ⟨_, kW, out, hRunW, hPcW, hCostW, hOut, _, _, hCtxOut, hFrameW⟩ :=
    hintRowFinalStmt_sem G coords beta hPrefix N m Nj parent outsideBase bitmapBase maxR BX BY oldCount j v
      P E mid (base + 95) hPublic hp.input hp.header hp.context hNj' rfl hBX hp.hint_limit
      hp.max_count hAtWork hPcP
  refine ⟨hPc, kW + kP, out, hintIterate_then (step P E) hRunP hRunW, by omega,
    by dsimp only [maxR] at hCostW; omega, ?_, hCtxOut, ?_⟩
  · intro q hq
    have hAlign : Finset.univ.image (fun t => (coords t).val) = rowImage N m π j.val J := hImage.trans (by rw [← hRowValue])
    simpa only [hAlign] using hOut q hq
  · intro addr hAway
    obtain ⟨hB, hO, h3, h7, h8, hR, hG⟩ := hZones addr hAway
    have hEq := hFrameW addr hB hO h3 h7 h8 hR hG
    rw [hEq]
    apply hFrameP
    rcases hAway with hBefore | hAfter
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPreparedPredictStmt_sem
#print axioms LinearSetReconciliation327.Main.hintPreparedFinalStmt_sem
end S_HintPreparedWorkers20261120
section S_HintPreparedStable20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintParams

theorem hintRowPrepareStmt_stable_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets) (v : HintVec G.rows)
    (N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount : ℕ)
    (π : Equiv.Perm (Fin N)) (J : Finset ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hParent : parent + 16 = G.context) (hContext : state.regs 14 = G.context)
    (hFits : HintGaussHeaderFits E G 0)
    (hMeta : HintRowPrepareMetadata G parent Nj m outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount state.mem)
    (hm : 0 < m) (hRow : G.row < m) (hNj : Nj = rowLen N m G.row)
    (hHintLen : (hintRowMembers N m G.row π J).length = G.hints)
    (hCoords : ∀ i : Fin G.hints, (coords i).val =
      (hintRowMembers N m G.row π J)[i.val]'(hHintLen.symm ▸ i.isLt))
    (hRowsFit : m < 2 ^ E.W) (hNjFit : Nj < 2 ^ E.W)
    (hBYFit : BY + 1 < 2 ^ E.W) (hTableFit : table + (BY + 1) * G.hints < 2 ^ E.W)
    (hOutside : outsideBase < G.hintList)
    (hGatherEnd : G.hintList + Nj ≤ parent)
    (hDestEnd : G.hintList + G.hints + 2 * G.rows ≤ parent)
    (hHintSeparate : parent ≤ hintSource) (hHintFit : hintSource < 2 ^ E.W)
    (hHintSpan : hintSource + N ≤ 2 ^ E.W)
    (hTranscriptSeparate : G.hintList + G.hints + 2 * G.rows ≤ transcriptSource)
    (hTranscriptOutsideGather : G.hintList + Nj ≤ transcriptSource)
    (hTranscriptAfterHeader : parent + 18 ≤ transcriptSource)
    (hTranscriptFit : transcriptSource < 2 ^ E.W)
    (hTranscriptSpan : ∀ t : Fin G.rows, transcriptSource + t.val * m < 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv G.node p.val = (π.symm p).val)
    (hBits : ∀ c : Fin N, state.mem (hintSource + c.val) = hintTruth (c.val ∈ J))
    (hTranscript : ∀ t : Fin G.rows, state.mem (transcriptSource + t.val * m) = (v t).val)
    (hAt : At P base (hintRowPrepareStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 95) state (fun k out => k ≤ 12 * Nj + 9 * G.rows + 78 ∧
      HintRowPrepared G coords v parent Nj outsideBase bitmapBase BX BY table oldCount out ∧
      CRMemFrame G.hintList (parent + 18) state.mem out.mem ∧
      (∀ i < 16, i ≠ 4 → i ≠ 5 → out.mem (parent + i) = state.mem (parent + i))) := by
  have hSpan := hFits.span
  have hHL : G.hints ≤ Nj := by
    rw [← hHintLen, hNj]
    exact hintGatherList_length_le _ _
  have hMetaGather : HintGatherMetadata parent G.hintList hintSource m G.row G.node
      (rowLen N m G.row) state.mem := hNj ▸ hMeta.gather
  obtain ⟨hGatherAt, hRestAt⟩ := At.seqStmt hAt
  change At P base (hintRowGatherStmt.compile base) at hGatherAt
  change At P (base + 35) ((Stmt.seq (.code hintRowSizingCode) hintTranscriptStmt).compile (base + 35)) at hRestAt
  obtain ⟨hSizeAt, hTranscriptAt⟩ := At.seqStmt hRestAt
  change At P (base + 35) hintRowSizingCode at hSizeAt
  change At P (base + 65) (hintTranscriptStmt.compile (base + 65)) at hTranscriptAt
  obtain ⟨_, kG, sG, hRunG, hPcG, hCostG, hLenG, hListG, hFrameG, hCtxG⟩ :=
    hintRowGatherStmt_sem P E state N m G.row G.node parent G.hintList hintSource base π J hm hRow
      (by omega) (hContext.trans hParent.symm) hMetaGather (hFits.values 9 (by decide)) hHintFit hRowsFit
      (hFits.values 10 (by decide)) (by omega) (by omega) hHintSpan hPerm hBits hGatherAt hPc
  have hAfterG (addr : ℕ) (ha : parent ≤ addr) : sG.mem addr = state.mem addr :=
    hFrameG addr (Or.inr (by omega))
  have hSize := hintRowSizingCode_spec E sG parent Nj BY table G.hints (by omega) hCtxG hHL hNjFit hBYFit hTableFit
    (hLenG.trans hHintLen)
    ((hAfterG _ (by omega)).trans hMeta.gather.count_value)
    ((hAfterG _ (by omega)).trans hMeta.outside_limit)
    ((hAfterG _ (by omega)).trans hMeta.threshold_table)
  generalize hS : runBlock hintRowSizingCode E sG = sS at hSize
  obtain ⟨hPcS, hMemS, hCtxS⟩ := hSize
  have hRunS : (step P E)^[30] sG = sS := by
    have hh := iterate_runBlock_of_at P E hintRowSizingCode sG (by rwa [hPcG])
      (by simp [hintRowSizingCode, hintScanParent, hintRowSizingFetch, hintParentLoad,
        hintRowSizingMin, hintRowSizingTable, hintRowSizingWrite, NoBranch, Instr.NoBranchI])
    simpa only [hintRowSizingCode_length, hS] using hh
  have hUnchangedS (addr : ℕ) (h4 : addr ≠ parent + 4) (h5 : addr ≠ parent + 5) (h17 : addr ≠ parent + 17) :
      sS.mem addr = sG.mem addr := by
    rw [hMemS]
    exact hintRowSizedMem_frame _ _ _ _ _ _ _ h4 h5 h17
  have hHeaderS : ∃ index, HintGaussHeader G index sS.mem := by
    obtain ⟨index, hHead⟩ := hMeta.header
    refine ⟨index, ?_⟩
    intro i hi
    by_cases hEq : i = 1
    · subst i
      rw [show G.context + 1 = parent + 17 by omega, hMemS]
      simp [hintRowSizedMem, hintGaussHeaderValue]
    · rw [hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
      exact hHead i hi hEq
  obtain ⟨_, kT, out, hRunT, hPcT, hCostT, hObs, hHeaderOut, hCtxOut, hFrameT⟩ :=
    hintTranscriptStmt_sem G v parent transcriptSource m P E sS (base + 65)
      hParent (hCtxS.trans hParent) hHeaderS hFits hTranscriptFit hRowsFit
      (by rw [hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]; exact hMeta.transcript_pointer)
      (by rw [hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]; exact hMeta.gather.rows_value)
      hDestEnd hTranscriptSeparate hTranscriptSpan
      (by
        intro t
        rw [hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
        exact hTranscript t) hTranscriptAt (by omega)
  have hAfterT (addr : ℕ) (ha : parent ≤ addr) : out.mem addr = sS.mem addr :=
    hFrameT addr (Or.inr (by omega))
  refine ⟨hPc, kT + (30 + kG), out, hintIterate_then (step P E) (hintIterate_then (step P E) hRunG hRunS) hRunT,
    by omega, by omega, ⟨⟨?_, ?_, ?_, ?_, ?_, hObs⟩, hHeaderOut, hCtxOut, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hAfterT _ le_rfl, hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ le_rfl]
    exact hMeta.outside_pointer
  · rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
    exact hMeta.bitmap_pointer
  · rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
    exact hMeta.gather.count_value
  · rw [hFrameT _ (Or.inl (by omega)), hUnchangedS _ (by omega) (by omega) (by omega),
      hFrameG _ (Or.inl hOutside)]
    exact hMeta.outside_count
  · intro i
    have hi := i.isLt
    rw [hFrameT _ (Or.inl (by omega)), hUnchangedS _ (by omega) (by omega) (by omega)]
    exact (hListG i.val (hHintLen.symm ▸ hi)).trans (hCoords i).symm
  · rw [hAfterT _ (by omega), hMemS]
    simp [hintRowSizedMem, Function.update_of_ne (by omega : parent + 4 ≠ parent + 17),
      Function.update_of_ne (by omega : parent + 4 ≠ parent + 5)]
  · rw [hAfterT _ (by omega), hMemS]
    simp [hintRowSizedMem, Function.update_of_ne (by omega : parent + 5 ≠ parent + 17)]
  · rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]
    exact hMeta.hint_limit
  · intro addr hAway
    rcases hAway with hBefore | hAfter
    · rw [hFrameT _ (Or.inl (by omega)), hUnchangedS _ (by omega) (by omega) (by omega), hFrameG _ (Or.inl hBefore)]
    · rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]

  · intro i hi h4 h5
    rw [hAfterT _ (by omega), hUnchangedS _ (by omega) (by omega) (by omega), hAfterG _ (by omega)]

theorem hintPreparedPredictStmt_stable_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets) (v : HintVec G.rows)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps) (c : ℕ)
    (N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount : ℕ)
    (π : Equiv.Perm (Fin N)) (J : Finset ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hContext : state.regs 14 = G.context)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj (min BY (Nj - G.hints)) parent outsideBase bitmapBase)
    (j : Fin m) (hRowValue : G.row = j.val) (hBX : BX < 2 ^ E.W)
    (hMeta : HintRowPrepareMetadata G parent Nj m outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount state.mem)
    (hm : 0 < m) (hRow : G.row < m) (hNj : Nj = rowLen N m G.row)
    (hHintLen : (hintRowMembers N m G.row π J).length = G.hints)
    (hCoords : ∀ i : Fin G.hints, (coords i).val =
      (hintRowMembers N m G.row π J)[i.val]'(hHintLen.symm ▸ i.isLt))
    (hRowsFit : m < 2 ^ E.W) (hNjFit : Nj < 2 ^ E.W)
    (hBYFit : BY + 1 < 2 ^ E.W) (hTableFit : table + (BY + 1) * G.hints < 2 ^ E.W)
    (hGatherEnd : G.hintList + Nj ≤ parent)
    (hHintSeparate : parent ≤ hintSource) (hHintFit : hintSource < 2 ^ E.W)
    (hHintSpan : hintSource + N ≤ 2 ^ E.W)
    (hTranscriptSeparate : G.hintList + G.hints + 2 * G.rows ≤ transcriptSource)
    (hTranscriptOutsideGather : G.hintList + Nj ≤ transcriptSource)
    (hTranscriptAfterHeader : parent + 18 ≤ transcriptSource)
    (hTranscriptFit : transcriptSource < 2 ^ E.W)
    (hTranscriptSpan : ∀ t : Fin G.rows, transcriptSource + t.val * m < 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv G.node p.val = (π.symm p).val)
    (hBits : ∀ c : Fin N, state.mem (hintSource + c.val) = hintTruth (c.val ∈ J))
    (hTranscript : ∀ t : Fin G.rows, state.mem (transcriptSource + t.val * m) = (v t).val)
    (hWaitTable : table + (BY + 1) * G.hints + min BY (Nj - G.hints) < 2 ^ E.W)
    (hLookup : ∀ r ≤ min BY (Nj - G.hints),
      E.det (table + (BY + 1) * G.hints + r) = min G.steps (sigma G.hints Nj r + c))
    (hCoeff : ∀ hNext : G.rows < G.steps, ∀ q : Fin G.buckets,
      E.coeff G.node ((G.row * G.steps + G.rows) * G.buckets + q.val) = (beta ⟨G.rows, hNext⟩ q).val)
    (hAt : At P base (hintPreparedPredictStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1584) state (fun k out =>
      k ≤ (hintRowOuterBudget G Nj (min BY (Nj - G.hints)) + 2) *
        (min BY (Nj - G.hints) + 1) + 12 * Nj + 9 * G.rows + 107 ∧
      hintRowOutput out = workerPredict N m G.steps G.buckets BX BY c j beta
        (rowImage N m π j.val J) (List.ofFn v) ∧
      out.regs 14 = G.context ∧
      CRMemFrame bitmapBase (G.pivotRow + G.rows) state.mem out.mem ∧
      (∃ count, HintRowInput G coords Nj count parent outsideBase bitmapBase v out.mem) ∧
      (∃ index, HintGaussHeader G index out.mem) ∧
      (∀ i, 9 ≤ i → i < 16 → out.mem (parent + i) = state.mem (parent + i))) := by
  let maxR := min BY (Nj - G.hints)
  let tableAddr := table + (BY + 1) * G.hints
  have hh := hPublic.outside_span
  obtain ⟨hBitmapStart, hHeaderEnd, hZones⟩ := hintPrepared_frames hPublic
  have hImage := hintRowPrepared_image G coords N m π J hm hRow hHintLen hCoords
  have hNj' : rowLen N m j.val = Nj := by rw [← hRowValue, hNj]
  obtain ⟨hAtPrep, hAtWork⟩ := At.seqStmt hAt
  change At P base (hintRowPrepareStmt.compile base) at hAtPrep
  change At P (base + 95) (hintRowPredictStmt.compile (base + 95)) at hAtWork
  obtain ⟨_, kP, mid, hRunP, hPcP, hCostP, hp, hFrameP, hStableP⟩ :=
    hintRowPrepareStmt_stable_sem G coords v N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount π J
      P E state base hPublic.parent_eq hContext hPublic.fits hMeta hm hRow hNj hHintLen hCoords hRowsFit hNjFit
      hBYFit hTableFit (by omega) hGatherEnd hPublic.source hHintSeparate hHintFit hHintSpan
      hTranscriptSeparate hTranscriptOutsideGather hTranscriptAfterHeader hTranscriptFit hTranscriptSpan hPerm hBits hTranscript
      hAtPrep hPc
  obtain ⟨_, kW, out, hRunW, hPcW, hCostW, hOut, hInputOut, hHeaderOut, hCtxOut, hFrameW⟩ :=
    hintRowPredictStmt_sem G coords beta hPrefix N m Nj parent outsideBase bitmapBase maxR tableAddr BX BY c oldCount j v
      P E mid (base + 95) hPublic hp.input hp.header hp.context hNj' rfl hBX hp.hint_limit
      hp.max_count hp.wait_table hWaitTable hLookup hCoeff hAtWork hPcP
  have hOutput : hintRowOutput out = workerPredict N m G.steps G.buckets BX BY c j beta
      (rowImage N m π j.val J) (List.ofFn v) := by
    have hAlign : Finset.univ.image (fun t => (coords t).val) = rowImage N m π j.val J := hImage.trans (by rw [← hRowValue])
    simpa only [hAlign] using hOut
  refine ⟨hPc, kW + kP, out, hintIterate_then (step P E) hRunP hRunW, by omega,
    by dsimp only [maxR] at hCostW; omega, hOutput, hCtxOut, ?_, hInputOut, hHeaderOut, ?_⟩
  · intro addr hAway
    obtain ⟨hB, hO, h3, _, _, hR, hG⟩ := hZones addr hAway
    rw [hFrameW addr hB hO h3 hR hG]
    apply hFrameP
    rcases hAway with hBefore | hAfter
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · intro i hi hi'
    rw [hFrameW.parent hPublic i (by omega) hi', hStableP i hi' (by omega) (by omega)]

theorem hintPreparedFinalStmt_stable_sem (G : HintGaussArea) (coords : Fin G.hints → Fin G.buckets) (v : HintVec G.rows)
    (beta : Fin G.steps → Fin G.buckets → ZMod 2) (hPrefix : G.rows ≤ G.steps)
    (N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount : ℕ)
    (π : Equiv.Perm (Fin N)) (J : Finset ℕ) (P : Program) (E : RAMEnv) (state : RAMState) (base : ℕ)
    (hContext : state.regs 14 = G.context)
    (hPublic : HintScanPublic E G coords beta hPrefix Nj (min BY (Nj - G.hints)) parent outsideBase bitmapBase)
    (j : Fin m) (hRowValue : G.row = j.val) (hBX : BX < 2 ^ E.W)
    (hMeta : HintRowPrepareMetadata G parent Nj m outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount state.mem)
    (hm : 0 < m) (hRow : G.row < m) (hNj : Nj = rowLen N m G.row)
    (hHintLen : (hintRowMembers N m G.row π J).length = G.hints)
    (hCoords : ∀ i : Fin G.hints, (coords i).val =
      (hintRowMembers N m G.row π J)[i.val]'(hHintLen.symm ▸ i.isLt))
    (hRowsFit : m < 2 ^ E.W) (hNjFit : Nj < 2 ^ E.W)
    (hBYFit : BY + 1 < 2 ^ E.W) (hTableFit : table + (BY + 1) * G.hints < 2 ^ E.W)
    (hGatherEnd : G.hintList + Nj ≤ parent)
    (hHintSeparate : parent ≤ hintSource) (hHintFit : hintSource < 2 ^ E.W)
    (hHintSpan : hintSource + N ≤ 2 ^ E.W)
    (hTranscriptSeparate : G.hintList + G.hints + 2 * G.rows ≤ transcriptSource)
    (hTranscriptOutsideGather : G.hintList + Nj ≤ transcriptSource)
    (hTranscriptAfterHeader : parent + 18 ≤ transcriptSource)
    (hTranscriptFit : transcriptSource < 2 ^ E.W)
    (hTranscriptSpan : ∀ t : Fin G.rows, transcriptSource + t.val * m < 2 ^ E.W)
    (hPerm : ∀ p : Fin N, E.permInv G.node p.val = (π.symm p).val)
    (hBits : ∀ c : Fin N, state.mem (hintSource + c.val) = hintTruth (c.val ∈ J))
    (hTranscript : ∀ t : Fin G.rows, state.mem (transcriptSource + t.val * m) = (v t).val)
    (hAt : At P base (hintPreparedFinalStmt.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 1653) state (fun k out =>
      k ≤ (hintFinalBudget G Nj (min BY (Nj - G.hints)) + 2) *
        (min BY (Nj - G.hints) + 1) + hintFinalBudget G Nj (min BY (Nj - G.hints)) +
        26 * Nj + 9 * G.rows + 18 * G.hints + 8 * min BY (Nj - G.hints) + 186 ∧
      (∀ q < Nj, out.mem (bitmapBase + q) = hintTruth (q ∈
        workerFinal N m G.steps G.buckets BX BY j beta (rowImage N m π j.val J) (List.ofFn v))) ∧
      out.regs 14 = G.context ∧
      CRMemFrame bitmapBase (G.pivotRow + G.rows) state.mem out.mem ∧
      (∃ count, HintRowInput G coords Nj count parent outsideBase bitmapBase v out.mem) ∧
      (∃ index, HintGaussHeader G index out.mem) ∧
      (∀ i, 9 ≤ i → i < 16 → out.mem (parent + i) = state.mem (parent + i))) := by
  let maxR := min BY (Nj - G.hints)
  have hh := hPublic.outside_span
  obtain ⟨hBitmapStart, hHeaderEnd, hZones⟩ := hintPrepared_frames hPublic
  have hImage := hintRowPrepared_image G coords N m π J hm hRow hHintLen hCoords
  have hNj' : rowLen N m j.val = Nj := by rw [← hRowValue, hNj]
  obtain ⟨hAtPrep, hAtWork⟩ := At.seqStmt hAt
  change At P base (hintRowPrepareStmt.compile base) at hAtPrep
  change At P (base + 95) (hintRowFinalStmt.compile (base + 95)) at hAtWork
  obtain ⟨_, kP, mid, hRunP, hPcP, hCostP, hp, hFrameP, hStableP⟩ :=
    hintRowPrepareStmt_stable_sem G coords v N m Nj parent outsideBase bitmapBase hintSource transcriptSource BX BY table oldCount π J
      P E state base hPublic.parent_eq hContext hPublic.fits hMeta hm hRow hNj hHintLen hCoords hRowsFit hNjFit
      hBYFit hTableFit (by omega) hGatherEnd hPublic.source hHintSeparate hHintFit hHintSpan
      hTranscriptSeparate hTranscriptOutsideGather hTranscriptAfterHeader hTranscriptFit hTranscriptSpan hPerm hBits hTranscript
      hAtPrep hPc
  obtain ⟨_, kW, out, hRunW, hPcW, hCostW, hOut, hInputOut, hHeaderOut, hCtxOut, hFrameW⟩ :=
    hintRowFinalStmt_sem G coords beta hPrefix N m Nj parent outsideBase bitmapBase maxR BX BY oldCount j v
      P E mid (base + 95) hPublic hp.input hp.header hp.context hNj' rfl hBX hp.hint_limit
      hp.max_count hAtWork hPcP
  refine ⟨hPc, kW + kP, out, hintIterate_then (step P E) hRunP hRunW, by omega,
    by dsimp only [maxR] at hCostW; omega, ?_, hCtxOut, ?_, hInputOut, hHeaderOut, ?_⟩
  · intro q hq
    have hAlign : Finset.univ.image (fun t => (coords t).val) = rowImage N m π j.val J := hImage.trans (by rw [← hRowValue])
    simpa only [hAlign] using hOut q hq
  · intro addr hAway
    obtain ⟨hB, hO, h3, h7, h8, hR, hG⟩ := hZones addr hAway
    have hEq := hFrameW addr hB hO h3 h7 h8 hR hG
    rw [hEq]
    apply hFrameP
    rcases hAway with hBefore | hAfter
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · intro i hi hi'
    rw [hFrameW.parent hPublic i (by omega) hi' (by omega) (by omega), hStableP i hi' (by omega) (by omega)]


end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPreparedPredictStmt_stable_sem
#print axioms LinearSetReconciliation327.Main.hintPreparedFinalStmt_stable_sem
end S_HintPreparedStable20261120
section S_HintActionSwitch20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintDispatchDec : List Instr := [.sub 1 1 15]

def hintActionSwitch : List Stmt → Stmt
  | [] => .code []
  | action :: rest =>
      .ite (.neqz 1) (.seq (.code hintDispatchDec) (hintActionSwitch rest)) action

structure HintDispatchSame (s t : RAMState) : Prop where
  memory : t.mem = s.mem
  regs : ∀ r : Fin 16, r ≠ 1 → t.regs r = s.regs r

theorem HintDispatchSame.trans {s t u : RAMState} (h : HintDispatchSame s t) (h' : HintDispatchSame t u) :
    HintDispatchSame s u :=
  ⟨h'.memory.trans h.memory, fun r hr => (h'.regs r hr).trans (h.regs r hr)⟩

theorem hintDispatchDec_spec (E : RAMEnv) (s : RAMState) (tag : ℕ)
    (hTag : s.regs 1 = tag + 1) (hTagFit : tag < 2 ^ E.W) (hOne : s.regs 15 = 1) :
    let out := runBlock hintDispatchDec E s
    out.pc = s.pc + 1 ∧ out.regs 1 = tag ∧ HintDispatchSame s out := by
  have hSub : (tag + 1) + 2 ^ E.W - 1 = tag + 2 ^ E.W := by omega
  refine ⟨?_, ?_, ⟨rfl, ?_⟩⟩
  · simp [hintDispatchDec, runBlock, execInstr]
  · simp [hintDispatchDec, runBlock, execInstr, hTag, hOne, hSub, Nat.mod_eq_of_lt hTagFit]
  · intro r hr
    simp [hintDispatchDec, runBlock, execInstr, hr]

/-- A fixed switch on the event tag in register 1. Each selected action sees
register 1 equal to zero and the original memory and all other registers. -/
theorem hintActionSwitch_sem (actions : List Stmt) (action : Stmt) (tag : ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base budget : ℕ) (Q : RAMState → Prop)
    (hWord : 1 < 2 ^ E.W) (hTag : state.regs 1 = tag) (hTagFit : tag < 2 ^ E.W)
    (hOne : state.regs 15 = 1) (hSelect : actions[tag]? = some action)
    (hAt : At P base ((hintActionSwitch actions).compile base)) (hPc : state.pc = base)
    (hAction : ∀ entry (s : RAMState), HintDispatchSame state s → s.regs 1 = 0 → s.pc = entry →
      At P entry (action.compile entry) →
      Sem P E entry (entry + action.len) s (fun k out => k ≤ budget ∧ Q out))
    (hQpc : ∀ out pc, Q out → Q {out with pc := pc}) :
    Sem P E base (base + (hintActionSwitch actions).len) state (fun k out => k ≤ budget + 3 * tag + 2 ∧ Q out) := by
  induction actions generalizing tag base state with
  | nil => simp at hSelect
  | cons first rest ih =>
    let tail := Stmt.seq (.code hintDispatchDec) (hintActionSwitch rest)
    change At P base ((Stmt.ite (.neqz 1) tail first).compile base) at hAt
    change Sem P E base (base + (Stmt.ite (.neqz 1) tail first).len) state _
    have hEnd : base + (Stmt.ite (.neqz 1) tail first).len =
        base + (Cond.neqz 1).code.length + tail.len + first.len + 3 := by
      simp only [Stmt.len]
      omega
    rw [hEnd]
    apply Sem.ite P E base (.neqz 1) tail first state _ hAt hWord hPc
    · intro hGo
      have hPositive : tag ≠ 0 := by intro hZero; apply hGo; change state.regs 1 = 0; omega
      obtain ⟨t, ht⟩ : ∃ t, tag = t + 1 := ⟨tag - 1, by omega⟩
      have hSelectT : rest[t]? = some action := by
        simpa only [ht, List.getElem?_cons_succ] using hSelect
      let entered : RAMState := {state with pc := base + 1}
      have hTailAt : At P (base + 1) (tail.compile (base + 1)) := (at_ite hAt).2.2.1
      change Sem P E (base + 1) (base + 1 + tail.len) entered _
      obtain ⟨hDecAt, hRestAt⟩ := At.seqStmt hTailAt
      change At P (base + 1) hintDispatchDec at hDecAt
      change At P (base + 1 + 1) ((hintActionSwitch rest).compile (base + 1 + 1)) at hRestAt
      have hDec := hintDispatchDec_spec E entered t (by exact hTag.trans ht) (by omega) hOne
      generalize hD : runBlock hintDispatchDec E entered = mid at hDec
      obtain ⟨hPcD, hTagD, hSameD⟩ := hDec
      have hSame : HintDispatchSame state mid := ⟨hSameD.memory, hSameD.regs⟩
      have hRunD : (step P E)^[1] entered = mid := by
        have h := iterate_runBlock_of_at P E hintDispatchDec entered hDecAt
          (by simp [hintDispatchDec, NoBranch, Instr.NoBranchI])
        rw [hD] at h
        exact h
      have hSuffix := ih t mid (base + 1 + 1) hTagD (by omega)
        ((hSame.regs 15 (by decide)).trans hOne) hSelectT hRestAt hPcD
        (fun entry st hSame' => hAction entry st (hSame.trans hSame'))
      obtain ⟨_, k, out, hRun, hPcOut, hCost, hPost⟩ := hSuffix
      refine ⟨rfl, k + 1, out, hintIterate_then (step P E) hRunD hRun, ?_, ?_, hQpc _ _ hPost⟩
      · change out.pc = base + 1 + (1 + (hintActionSwitch rest).len)
        omega
      · change 1 + (k + 1) + 1 ≤ budget + 3 * tag + 2
        omega
    · intro hStop
      have hZero : tag = 0 := by
        by_contra hNe
        exact hStop (by change state.regs 1 ≠ 0; rwa [hTag])
      have hFirst : first = action := by simpa [hZero] using hSelect
      subst first
      let start := base + tail.len + 2
      let entered : RAMState := {state with pc := start}
      have hRight : At P start (action.compile start) := by
        have h := (at_ite hAt).2.2.2.2.1
        simpa only [Cond.code, List.length_nil, Nat.add_zero, Nat.add_assoc,
          show 1 + (tail.len + 1) = tail.len + 2 by omega, start] using h
      simp only [Cond.code, List.length_nil, Nat.add_zero, Nat.zero_add]
      rw [show base + 1 + tail.len + 1 + action.len = start + action.len by dsimp [start]; omega]
      change Sem P E start (start + action.len) entered _
      have hNative := hAction _ entered ⟨rfl, fun _ _ => rfl⟩ (hTag.trans hZero) rfl hRight
      apply Sem.mono hNative
      intro k out hOut
      exact ⟨by change 1 + k + 1 ≤ budget + 3 * tag + 2; omega, hQpc _ _ hOut.2⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintActionSwitch_sem
end S_HintActionSwitch20261120
section S_HintDispatchIO20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintDispatchTable (E : RAMEnv) (table : ℕ) (events : List (ℕ × ℕ)) : Prop where
  span : table + 2 * events.length ≤ 2 ^ E.W
  tag : ∀ j : Fin events.length, E.det (table + 2 * j.val) = events[j.val].1
  descriptor : ∀ j : Fin events.length, E.det (table + 2 * j.val + 1) = events[j.val].2
  fits : ∀ j : Fin events.length, events[j.val].1 < 2 ^ E.W ∧ events[j.val].2 < 2 ^ E.W

structure HintDispatchData (control table count index : ℕ) (s : RAMState) : Prop where
  context : s.regs 14 = control
  table_pointer : s.mem control = table
  size : s.mem (control + 1) = count
  cursor : s.mem (control + 2) = index

def hintDispatchFetch : List Instr :=
  [.imm 5 2, .add 3 14 5, .load 0 3, .load 4 14, .mul 7 0 5, .add 7 4 7,
    .qDet 1 7, .imm 15 1, .add 7 7 15, .qDet 6 7]
def hintDispatchInit : List Instr :=
  [.imm 3 2, .add 3 14 3, .imm 0 0, .store 3 0, .imm 15 1, .add 4 14 15, .load 6 4, .lt 13 0 6]
def hintDispatchAdvance : List Instr :=
  [.imm 3 2, .add 3 14 3, .load 0 3, .imm 15 1, .add 0 0 15, .store 3 0,
    .add 4 14 15, .load 6 4, .lt 13 0 6]

theorem hintDispatchFetch_spec (E : RAMEnv) (s : RAMState)
    (control table : ℕ) (events : List (ℕ × ℕ)) (j : Fin events.length)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W)
    (hData : HintDispatchData control table events.length j.val s) (hTable : HintDispatchTable E table events) :
    let out := runBlock hintDispatchFetch E s
    out.pc = s.pc + 10 ∧ out.regs 1 = events[j.val].1 ∧ out.regs 6 = events[j.val].2 ∧ out.regs 15 = 1 ∧
      out.mem = s.mem ∧ HintDispatchData control table events.length j.val out := by
  have hSpan := hTable.span
  have hJ := j.isLt
  have hTag := hTable.tag j
  have hDesc := hTable.descriptor j
  have hTagFit := (hTable.fits j).1
  have hDescFit := (hTable.fits j).2
  have hOne : 1 < 2 ^ E.W := by omega
  have hTbl : table < 2 ^ E.W := by omega
  have hIndex : j.val < 2 ^ E.W := by omega
  have hMul : j.val * 2 < 2 ^ E.W := by omega
  have hAddr : table + j.val * 2 < 2 ^ E.W := by omega
  have hAddr2 : table + j.val * 2 + 1 < 2 ^ E.W := by omega
  rw [Nat.mul_comm 2 j.val] at hTag hDesc
  refine ⟨?_, ?_, ?_, ?_, rfl, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    simp [hintDispatchFetch, runBlock, execInstr, hData.context, hData.table_pointer, hData.cursor,
      hTag, hDesc, Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hTbl,
      Nat.mod_eq_of_lt hControl, Nat.mod_eq_of_lt hIndex, Nat.mod_eq_of_lt hMul,
      Nat.mod_eq_of_lt hAddr, Nat.mod_eq_of_lt hAddr2, Nat.mod_eq_of_lt hTagFit,
      Nat.mod_eq_of_lt hDescFit, hData.size]

theorem hintDispatchInit_spec (E : RAMEnv) (s : RAMState) (control table count old : ℕ)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : count < 2 ^ E.W)
    (hData : HintDispatchData control table count old s) :
    let out := runBlock hintDispatchInit E s
    out.pc = s.pc + 8 ∧ out.mem = Function.update s.mem (control + 2) 0 ∧
      out.regs 13 = hintTruth (0 < count) ∧ HintDispatchData control table count 0 out := by
  classical
  have hOne : 1 < 2 ^ E.W := by omega
  have hA1 : control + 1 < 2 ^ E.W := by omega
  have hNe0 : control ≠ control + 2 := by omega
  have hNe1 : control + 1 ≠ control + 2 := by omega
  by_cases hc : 0 < count <;>
    refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
      simp [hintDispatchInit, runBlock, execInstr, hData.context, hData.table_pointer, hData.size,
        hintTruth, hc, Function.update_of_ne hNe0, Function.update_of_ne hNe1,
        Nat.mod_eq_of_lt hControl, Nat.mod_eq_of_lt hA1, Nat.mod_eq_of_lt hCount,
        Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hOne]

theorem hintDispatchAdvance_spec (E : RAMEnv) (s : RAMState) (control table count j : ℕ)
    (hWord : 2 < 2 ^ E.W) (hControl : control + 2 < 2 ^ E.W) (hCount : count < 2 ^ E.W) (hj : j < count)
    (hData : HintDispatchData control table count j s) :
    let out := runBlock hintDispatchAdvance E s
    out.pc = s.pc + 9 ∧ out.mem = Function.update s.mem (control + 2) (j + 1) ∧
      out.regs 13 = hintTruth (j + 1 < count) ∧ HintDispatchData control table count (j + 1) out := by
  classical
  have hOne : 1 < 2 ^ E.W := by omega
  have hA1 : control + 1 < 2 ^ E.W := by omega
  have hNe0 : control ≠ control + 2 := by omega
  have hNe1 : control + 1 ≠ control + 2 := by omega
  have hJ : j < 2 ^ E.W := by omega
  have hNext : j + 1 < 2 ^ E.W := by omega
  by_cases hc : j + 1 < count <;>
    refine ⟨?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
      simp [hintDispatchAdvance, runBlock, execInstr, hData.context, hData.table_pointer, hData.size,
        hData.cursor, hintTruth, hc, Function.update_of_ne hNe0, Function.update_of_ne hNe1,
        Nat.mod_eq_of_lt hControl, Nat.mod_eq_of_lt hA1, Nat.mod_eq_of_lt hCount,
        Nat.mod_eq_of_lt hWord, Nat.mod_eq_of_lt hOne, Nat.mod_eq_of_lt hJ, Nat.mod_eq_of_lt hNext]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDispatchFetch_spec
#print axioms LinearSetReconciliation327.Main.hintDispatchAdvance_spec
end S_HintDispatchIO20261120


