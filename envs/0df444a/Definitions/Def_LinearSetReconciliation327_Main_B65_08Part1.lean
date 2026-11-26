-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_08Part1
-- name    : LinearSetReconciliation327_Main_B65_08Part1
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T06:57:41.019066+00:00
-- url     : https://prove2.me/theorems/2cbb350c-156e-42f3-aabe-152d52c622d4
-- title:
--   Theorem 6.5 supporting machine proof B65_08Part1
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_08EmitCore
import Definitions.Def_LinearSetReconciliation327_Main_HintCRListCorrect20261120
import Definitions.Def_LinearSetReconciliation327_Main_B65_06
import Definitions.Def_LinearSetReconciliation327_Main_B65_06RowResult
import Definitions.Def_LinearSetReconciliation327_Main_B65_07
set_option autoImplicit false

section S_HintCRNode20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintCRNodeArea where
  offset : ℕ
  registers : ℕ
  memory : ℕ
  table : ℕ
  log : ℕ
  descriptor : ℕ
  destination : ℕ
  control : ℕ

structure HintCRNodePre (S : CRSourceBundle) (E : RAMEnv) (N t : ℕ) (A : HintCRNodeArea) : Prop where
  universe_pos : 1 ≤ N
  sparse_bound : t ≤ N
  spill : CRSimLayout E (S.data N t).W A.registers A.memory A.table A.log
    (crSourceSteps S N t) (S.data N t).det
  call_header : CRCallHeader E A.descriptor (S.data N t).W (S.data N t).R A.offset A.registers
    A.memory A.table A.log (crSourceSteps S N t)
  normalization : HintNormalizeTable E A.descriptor A.destination N A.control
  output_before : A.destination + N < A.registers
  input_span : A.offset + (S.data N t).R < 2 ^ E.W
  input_before : (A.offset + (S.data N t).R) / E.W < A.memory

noncomputable def hintCRNodeBudget (S : CRSourceBundle) (N t : ℕ) : ℕ :=
  17 * (S.data N t).R + 16 * crSourceSteps S N t + 20 * N + 148

def HintCRNodeFrame (S : CRSourceBundle) (A : HintCRNodeArea) (N t : ℕ)
    (initial final : ℕ → ℕ) : Prop :=
  ∀ addr, (addr < A.destination ∨ A.destination + N < addr) →
    (addr < A.registers ∨ A.log + crSourceSteps S N t + 1 ≤ addr) → final addr = initial addr

theorem hintCRNodeCompose_sem (S : CRSourceBundle) (P : Program) (E : RAMEnv) (state : RAMState)
    (A : HintCRNodeArea) (N t entry endPc : ℕ) (Raw : RAMState → Prop)
    (Goal : (ℕ → ℕ) → Prop) (pre : HintCRNodePre S E N t A)
    (hPc : state.pc = entry)
    (hCore : Sem P E entry (entry + (crSourceInputCode S entry).length) state (fun k out =>
      k ≤ 17 * (S.data N t).R + 16 * crSourceSteps S N t + 124 ∧
      HintCRListSpan (S.data N t).W A.memory out ∧ out.regs 1 ≤ 2 ^ (S.data N t).W ∧
      out.regs 6 = A.descriptor ∧ CRMemFrame A.registers (A.log + crSourceSteps S N t + 1) state.mem out.mem ∧ Raw out))
    (hNormalize : At P (entry + (crSourceInputCode S entry).length)
      (hintNormalizeStmt.compile (entry + (crSourceInputCode S entry).length)))
    (hEnd : endPc = entry + (crSourceInputCode S entry).length + 40)
    (hGoal : ∀ raw out : RAMState, Raw raw →
      (∀ q < N, out.mem (A.destination + q) =
        hintStampValue E (raw.regs 0) (min (raw.regs 1) N) raw.mem q) → Goal out.mem) :
    Sem P E entry endPc state (fun k out => k ≤ hintCRNodeBudget S N t ∧
      out.regs 14 = A.control ∧ HintCRNodeFrame S A N t state.mem out.mem ∧ Goal out.mem) := by
  obtain ⟨_, kc, raw, hRun, hCorePc, hCost, hShape, hMax, hMeta, hFrame, hRaw⟩ := hCore
  have hFile := pre.spill.file_before
  have hLog := pre.spill.mem_before_log
  have hTop := pre.spill.log_word
  have hBefore := pre.output_before
  have hPow : 2 ^ ((S.data N t).W + 1) = 2 ^ (S.data N t).W + 2 ^ (S.data N t).W := by
    rw [pow_succ]
    omega
  rw [hPow] at hLog
  have hMin : min (raw.regs 1) N ≤ raw.regs 1 := min_le_left _ _
  have hBound : raw.regs 0 < 2 ^ E.W ∧ raw.regs 0 + min (raw.regs 1) N ≤ 2 ^ E.W ∧
      (raw.regs 0 + min (raw.regs 1) N ≤ A.destination ∨ A.destination + N < raw.regs 0) := by
    rcases hShape with ⟨hZero, hEmpty⟩ | ⟨hMemory, hMemoryEnd⟩
    · rw [hZero, hEmpty]
      simp
    · exact ⟨by omega, by omega, Or.inr (by omega)⟩
  obtain ⟨_, kn, out, hRunN, hPcN, hCostN, hCtx, hBitmap, hFrameN⟩ :=
    hintNormalizeStmt_sem P E raw A.descriptor A.destination N A.control
      (entry + (crSourceInputCode S entry).length) pre.normalization hMeta hBound.1 hBound.2.1
      hBound.2.2 hNormalize hCorePc
  refine ⟨hPc, kn + kc, out, hintIterate_then (step P E) hRun hRunN, hPcN.trans hEnd.symm,
    ?_, hCtx, ?_, hGoal raw out hRaw hBitmap⟩
  · unfold hintCRNodeBudget
    omega
  · intro address hOutside hOutsideCR
    exact (hFrameN address (by rcases hOutside with h | h <;> omega)).trans (hFrame address hOutsideCR)

theorem hintCRNode_total (S : CRSourceBundle) (P : Program) (E : RAMEnv) (state : RAMState)
    (A : HintCRNodeArea) (N t entry switchBase : ℕ) (other : List Stmt) (act : Stmt)
    (pre : HintCRNodePre S E N t A)
    (hPc : state.pc = entry) (hMeta : state.regs 6 = A.descriptor)
    (hFresh : ∀ addr, addr ≤ 2 ^ ((S.data N t).W + 1) → state.mem (A.memory + addr) = 0)
    (hSelect : (hintActionsWithCR S switchBase other hintNormalizeStmt)[other.length]? = some act)
    (hEntry : entry = hintActionEntry (hintActionsWithCR S switchBase other hintNormalizeStmt) switchBase other.length)
    (hAt : At P entry (act.compile entry)) :
    Sem P E entry (entry + act.len) state (fun k out => k ≤ hintCRNodeBudget S N t ∧
      out.regs 14 = A.control ∧ HintCRNodeFrame S A N t state.mem out.mem ∧
      (∀ q < N, out.mem (A.destination + q) = 0 ∨ out.mem (A.destination + q) = 1)) := by
  obtain ⟨hEnd, hCore, hFinish⟩ := hintCRAction_parts S P switchBase other hintNormalizeStmt act entry
    hSelect hEntry hAt
  let y : Fin (S.data N t).R → ZMod 2 := fun i =>
    if bitAt state.mem E.W 0 (A.offset + i.val) = 1 then 1 else 0
  have hInput (i : Fin (S.data N t).R) :
      bitAt state.mem E.W 0 (A.offset + i.val) = if y i = 1 then 1 else 0 := by
    have hb : bitAt state.mem E.W 0 (A.offset + i.val) < 2 := by
      unfold bitAt
      exact Nat.mod_lt _ (by decide)
    by_cases h : bitAt state.mem E.W 0 (A.offset + i.val) = 1
    · simp [y, h]
    · have hz : bitAt state.mem E.W 0 (A.offset + i.val) = 0 := by omega
      simp [y, hz]
  have hCoreRun := hintCRCodeList_total S P E N t A.offset A.registers A.memory A.table A.log A.descriptor
    entry state y pre.universe_pos pre.sparse_bound pre.spill hMeta (by have := pre.normalization.span; omega)
    pre.call_header pre.input_span pre.input_before hInput hFresh hCore hPc
  apply hintCRNodeCompose_sem S P E state A N t entry (entry + act.len) (fun _ => True)
    (fun mem => ∀ q < N, mem (A.destination + q) = 0 ∨ mem (A.destination + q) = 1) pre hPc
    (Sem.mono hCoreRun (by
      rintro k out ⟨hk, hs, hn, h6, hf⟩
      exact ⟨hk, hs, hn, h6.trans hMeta, hf, trivial⟩)) hFinish
  · rw [hEnd]
    change entry + ((crSourceInputCode S entry).length + 40) = _
    omega
  · intro raw out _ hBitmap q hq
    rw [hBitmap q hq]
    unfold hintStampValue hintTruth
    split
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem hintCRNode_correct (S : CRSourceBundle) (P : Program) (E : RAMEnv) (state : RAMState)
    (A : HintCRNodeArea) (N t entry switchBase : ℕ) (other : List Stmt) (act : Stmt)
    (x : Fin N → ZMod 2) (pre : HintCRNodePre S E N t A)
    (hSupport : (Finset.univ.filter fun i => x i = 1).card ≤ t)
    (hPc : state.pc = entry) (hMeta : state.regs 6 = A.descriptor)
    (hInput : ∀ i : Fin (S.data N t).R, bitAt state.mem E.W 0 (A.offset + i.val) =
      if (S.data N t).H x i = 1 then 1 else 0)
    (hFresh : ∀ addr, addr ≤ 2 ^ ((S.data N t).W + 1) → state.mem (A.memory + addr) = 0)
    (hSelect : (hintActionsWithCR S switchBase other hintNormalizeStmt)[other.length]? = some act)
    (hEntry : entry = hintActionEntry (hintActionsWithCR S switchBase other hintNormalizeStmt) switchBase other.length)
    (hAt : At P entry (act.compile entry)) :
    Sem P E entry (entry + act.len) state (fun k out => k ≤ hintCRNodeBudget S N t ∧
      out.regs 14 = A.control ∧ HintCRNodeFrame S A N t state.mem out.mem ∧
      (∀ i : Fin N, out.mem (A.destination + i.val) = (x i).val)) := by
  obtain ⟨hEnd, hCore, hFinish⟩ := hintCRAction_parts S P switchBase other hintNormalizeStmt act entry
    hSelect hEntry hAt
  have hCoreRun := hintCRCodeList_correct S P E N t A.offset A.registers A.memory A.table A.log A.descriptor
    entry state x pre.universe_pos pre.sparse_bound hSupport pre.spill hMeta
    (by have := pre.normalization.span; omega) pre.call_header pre.input_span pre.input_before hInput hFresh hCore hPc
  apply hintCRNodeCompose_sem S P E state A N t entry (entry + act.len) (fun raw => OutputsSupport raw x)
    (fun mem => ∀ i : Fin N, mem (A.destination + i.val) = (x i).val) pre hPc
    (Sem.mono hCoreRun (by
      rintro k out ⟨hk, hs, hn, hout, h6, hf⟩
      exact ⟨hk, hs, hn, h6.trans hMeta, hf, hout⟩)) hFinish
  · rw [hEnd]
    change entry + ((crSourceInputCode S entry).length + 40) = _
    omega
  · intro raw out hOut hBitmap i
    rw [hBitmap i.val i.isLt]
    exact hintNormalize_support E raw x (by have := pre.normalization.dest_span; omega) hOut i

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintCRNode_total
#print axioms LinearSetReconciliation327.Main.hintCRNode_correct
end S_HintCRNode20261120
section S_HintRootHeader20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- Decoder metadata within the existing sixteen-word header located by det[3].
The updater's own table slots retain their original interpretation. -/
structure HintRootHeader (E : RAMEnv) (header control hintMap resultMap listBase table count N : ℕ) : Prop where
  word : 15 < 2 ^ E.W
  span : header + 15 < 2 ^ E.W
  anchor : E.det 3 = header
  control_span : control + 2 < 2 ^ E.W
  normalize : HintNormalizeTable E header hintMap N control
  dispatch_table : E.det (header + 12) = table
  dispatch_count : E.det (header + 13) = count
  result_address : E.det (header + 14) = resultMap
  list_address : E.det (header + 15) = listBase
  table_fit : table < 2 ^ E.W
  count_fit : count < 2 ^ E.W
  result_fit : resultMap < 2 ^ E.W
  list_fit : listBase < 2 ^ E.W

def hintRootHintArgs : List Instr :=
  [.imm 3 3, .qDet 6 3, .imm 3 0, .add 0 1 3, .add 1 2 3]

def hintRootControlInit : List Instr :=
  [.imm 3 3, .qDet 6 3, .imm 3 12, .add 3 6 3, .qDet 9 3, .store 14 9,
    .imm 15 1, .add 3 3 15, .qDet 9 3, .add 3 14 15, .store 3 9]

def hintRootEmitArgs : List Instr :=
  [.imm 3 3, .qDet 7 3, .imm 15 1, .imm 3 15, .add 3 7 3, .qDet 4 3,
    .imm 3 14, .add 3 7 3, .qDet 5 3, .imm 3 10, .add 3 7 3, .qDet 6 3]

theorem hintRootHintArgs_spec (E : RAMEnv) (state : RAMState)
    (header control hintMap resultMap listBase table count N : ℕ)
    (hdr : HintRootHeader E header control hintMap resultMap listBase table count N)
    (hSource : state.regs 1 < 2 ^ E.W) (hLength : state.regs 2 < 2 ^ E.W) :
    let out := runBlock hintRootHintArgs E state
    out.pc = state.pc + 5 ∧ out.mem = state.mem ∧
      out.regs 6 = header ∧ out.regs 0 = state.regs 1 ∧ out.regs 1 = state.regs 2 := by
  have hWord := hdr.word
  have hSpan := hdr.span
  have h3 : 3 < 2 ^ E.W := by omega
  have hHdr : header < 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ?_, ?_⟩ <;>
    simp [hintRootHintArgs, runBlock, execInstr, hdr.anchor, Nat.mod_eq_of_lt h3,
      Nat.mod_eq_of_lt hHdr, Nat.mod_eq_of_lt hSource, Nat.mod_eq_of_lt hLength]

theorem hintRootControlInit_spec (E : RAMEnv) (state : RAMState)
    (header control hintMap resultMap listBase table count N : ℕ)
    (hdr : HintRootHeader E header control hintMap resultMap listBase table count N)
    (hCtx : state.regs 14 = control) :
    let out := runBlock hintRootControlInit E state
    out.pc = state.pc + 11 ∧
      out.mem = Function.update (Function.update state.mem control table) (control + 1) count ∧
      HintDispatchData control table count (state.mem (control + 2)) out := by
  have hSpan := hdr.span
  have hWord := hdr.word
  have hCtrlSpan := hdr.control_span
  have h1 : 1 < 2 ^ E.W := by omega
  have h3 : 3 < 2 ^ E.W := by omega
  have h12 : 12 < 2 ^ E.W := by omega
  have hHdr : header < 2 ^ E.W := by omega
  have hA12 : header + 12 < 2 ^ E.W := by omega
  have hA13 : header + 12 + 1 < 2 ^ E.W := by omega
  have hA1 : control + 1 < 2 ^ E.W := by omega
  have hc1 : control ≠ control + 1 := by omega
  have hc2 : control + 2 ≠ control := by omega
  have hc21 : control + 2 ≠ control + 1 := by omega
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    simp [hintRootControlInit, runBlock, execInstr, hCtx, hdr.anchor, hdr.dispatch_table, hdr.dispatch_count,
      Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h12, Nat.mod_eq_of_lt hHdr,
      Nat.mod_eq_of_lt hA12, Nat.mod_eq_of_lt hA13, Nat.mod_eq_of_lt hA1,
      Nat.mod_eq_of_lt hdr.table_fit, Nat.mod_eq_of_lt hdr.count_fit,
      Function.update_of_ne hc1, Function.update_of_ne hc2, Function.update_of_ne hc21]

theorem hintRootEmitArgs_spec (E : RAMEnv) (state : RAMState)
    (header control hintMap resultMap listBase table count N : ℕ)
    (hdr : HintRootHeader E header control hintMap resultMap listBase table count N) :
    let out := runBlock hintRootEmitArgs E state
    out.pc = state.pc + 12 ∧ out.mem = state.mem ∧ out.regs 14 = state.regs 14 ∧
      HintEmitArgs listBase resultMap N out := by
  have hWidth := hdr.word
  have hSpan := hdr.span
  have hN := hdr.normalize.dest_span
  have h1 : 1 < 2 ^ E.W := by omega
  have h3 : 3 < 2 ^ E.W := by omega
  have h10 : 10 < 2 ^ E.W := by omega
  have h14 : 14 < 2 ^ E.W := by omega
  have hHdr : header < 2 ^ E.W := by omega
  have hA10 : header + 10 < 2 ^ E.W := by omega
  have hA14 : header + 14 < 2 ^ E.W := by omega
  have hNFit : N < 2 ^ E.W := by omega
  refine ⟨?_, rfl, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
    simp [hintRootEmitArgs, runBlock, execInstr, hdr.anchor, hdr.result_address, hdr.list_address,
      hdr.normalize.count_value, Nat.mod_eq_of_lt hWidth, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3,
      Nat.mod_eq_of_lt h10, Nat.mod_eq_of_lt h14, Nat.mod_eq_of_lt hHdr, Nat.mod_eq_of_lt hA10,
      Nat.mod_eq_of_lt hA14, Nat.mod_eq_of_lt hSpan, Nat.mod_eq_of_lt hNFit,
      Nat.mod_eq_of_lt hdr.result_fit, Nat.mod_eq_of_lt hdr.list_fit]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRootHintArgs_spec
#print axioms LinearSetReconciliation327.Main.hintRootControlInit_spec
#print axioms LinearSetReconciliation327.Main.hintRootEmitArgs_spec
end S_HintRootHeader20261120
section S_HintRootIO20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRootEnter : Stmt :=
  .seq (.code hintRootHintArgs) (.seq hintNormalizeStmt (.code hintRootControlInit))
def hintRootExit : Stmt := .seq (.code hintRootEmitArgs) hintEmitResult

theorem hintRootEnter_len : hintRootEnter.len = 56 := rfl
theorem hintRootExit_len : hintRootExit.len = 25 := rfl

theorem hintRootEnter_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (header control hintMap resultMap listBase table count N base : ℕ)
    (hdr : HintRootHeader E header control hintMap resultMap listBase table count N)
    (hSource : state.regs 1 < 2 ^ E.W) (hLength : state.regs 2 < 2 ^ E.W)
    (hSpan : state.regs 1 + min (state.regs 2) N ≤ 2 ^ E.W)
    (hSeparate : state.regs 1 + min (state.regs 2) N ≤ hintMap ∨ hintMap + N < state.regs 1)
    (hControl : control + 2 ≤ hintMap ∨ hintMap + N < control)
    (hAt : At P base (hintRootEnter.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 56) state (fun k out => k ≤ 20 * N + 40 ∧
      HintDispatchData control table count (out.mem (control + 2)) out ∧
      (∀ q < N, out.mem (hintMap + q) = hintStampValue E (state.regs 1) (min (state.regs 2) N) state.mem q) ∧
      (∀ address, (address < hintMap ∨ hintMap + N < address) →
        address ≠ control → address ≠ control + 1 → out.mem address = state.mem address)) := by
  obtain ⟨hArgsAt, hRestAt⟩ := At.seqStmt hAt
  change At P base hintRootHintArgs at hArgsAt
  change At P (base + 5) ((Stmt.seq hintNormalizeStmt (.code hintRootControlInit)).compile (base + 5))
    at hRestAt
  obtain ⟨hNormalizeAt, hControlAt⟩ := At.seqStmt hRestAt
  change At P (base + 5) (hintNormalizeStmt.compile (base + 5)) at hNormalizeAt
  change At P (base + 45) hintRootControlInit at hControlAt
  have hSetup := hintRootHintArgs_spec E state header control hintMap resultMap listBase table count N hdr hSource hLength
  generalize hs : runBlock hintRootHintArgs E state = entered at hSetup
  obtain ⟨hSetupPc, hSetupMem, hHead, hSrc, hCount⟩ := hSetup
  have hRunSetup : (step P E)^[5] state = entered := by
    have hh := iterate_runBlock_of_at P E hintRootHintArgs state (by rwa [hPc])
      (by simp [hintRootHintArgs, NoBranch, Instr.NoBranchI])
    rw [hs] at hh
    exact hh
  obtain ⟨_, kn, marked, hRunN, hPcN, hCost, hCtxN, hHints, hFrame⟩ :=
    hintNormalizeStmt_sem P E entered header hintMap N control (base + 5) hdr.normalize hHead
      (hSrc.symm ▸ hSource) (by rw [hSrc, hCount]; exact hSpan)
      (by rw [hSrc, hCount]; exact hSeparate) hNormalizeAt (by omega)
  have hFinal := hintRootControlInit_spec E marked header control hintMap resultMap listBase table count N hdr hCtxN
  generalize hf : runBlock hintRootControlInit E marked = out at hFinal
  obtain ⟨hFinalPc, hFinalMem, hCtrl⟩ := hFinal
  have hRunFinal : (step P E)^[11] marked = out := by
    have hh := iterate_runBlock_of_at P E hintRootControlInit marked (by rwa [hPcN])
      (by simp [hintRootControlInit, NoBranch, Instr.NoBranchI])
    rw [hf] at hh
    exact hh
  refine ⟨hPc, 11 + (kn + 5), out, hintIterate_then (step P E)
      (hintIterate_then (step P E) hRunSetup hRunN) hRunFinal,
    by omega, by omega, ⟨hCtrl.context, hCtrl.table_pointer, hCtrl.size, rfl⟩, ?_, ?_⟩
  · intro q hq
    have hA : hintMap + q ≠ control := by rcases hControl with h | h <;> omega
    have hB : hintMap + q ≠ control + 1 := by rcases hControl with h | h <;> omega
    rw [hFinalMem, Function.update_of_ne hB, Function.update_of_ne hA, hHints q hq, hSrc, hCount, hSetupMem]
  · intro addr hAway hA hB
    rw [hFinalMem, Function.update_of_ne hB, Function.update_of_ne hA,
      hFrame addr (by rcases hAway with h | h <;> omega), hSetupMem]

theorem hintRootExit_sem (P : Program) (E : RAMEnv) (state : RAMState)
    (header control hintMap resultMap listBase table count N base : ℕ)
    (hdr : HintRootHeader E header control hintMap resultMap listBase table count N)
    (hSep : listBase + N ≤ resultMap) (hBitsSpan : resultMap + N ≤ 2 ^ E.W)
    (accept : ℕ → Bool)
    (hBits : ∀ q < N, state.mem (resultMap + q) = if accept q then 1 else 0)
    (hAt : At P base (hintRootExit.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 25) state (fun k out => k ≤ 9 * N + 18 ∧
      outList out = hintGatherList accept N ∧ CRMemFrame listBase (listBase + N) state.mem out.mem) := by
  obtain ⟨hArgsAt, hEmitAt⟩ := At.seqStmt hAt
  change At P base hintRootEmitArgs at hArgsAt
  change At P (base + 12) (hintEmitResult.compile (base + 12)) at hEmitAt
  have hSetup := hintRootEmitArgs_spec E state header control hintMap resultMap listBase table count N hdr
  generalize hs : runBlock hintRootEmitArgs E state = ready at hSetup
  obtain ⟨hReady, hMem, _, hArgs⟩ := hSetup
  have hRunSetup : (step P E)^[12] state = ready := by
    have h := iterate_runBlock_of_at P E hintRootEmitArgs state (by rwa [hPc])
      (by simp [hintRootEmitArgs, NoBranch, Instr.NoBranchI])
    rw [hs] at h
    exact h
  have hWidth := hdr.word
  have hN := hdr.normalize.dest_span
  have hInput : HintEmitSource E listBase resultMap N accept ready.mem := by
    refine ⟨by omega, by omega, hSep, by omega, ?_, ?_⟩
    · intro q hq; omega
    · rw [hMem]
      exact hBits
  obtain ⟨_, k, out, hRun, hEnd, hCost, _, hList, hFrame⟩ :=
    hintEmitResult_sem P E ready listBase resultMap N (base + 12) accept hInput hdr.list_fit hArgs
      hEmitAt (by omega)
  exact ⟨hPc, k + 12, out, hintIterate_then (step P E) hRunSetup hRun, by omega, by omega, hList, hMem ▸ hFrame⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRootEnter_sem
#print axioms LinearSetReconciliation327.Main.hintRootExit_sem
end S_HintRootIO20261120


