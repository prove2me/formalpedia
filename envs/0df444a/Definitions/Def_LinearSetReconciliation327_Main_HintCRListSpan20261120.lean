-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintCRListSpan20261120
-- name    : LinearSetReconciliation327_Main_HintCRListSpan20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:37:42.649871+00:00
-- url     : https://prove2.me/theorems/da457c76-3e6d-4211-9de9-0ea23d8eaa96
-- title:
--   LinearSetReconciliation327 — HintCRListSpan (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintCRListSpan20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintCRCode20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

/-- The spill interpreter returns an empty list on failure, or a list starting
in the private virtual memory. Its count is bounded separately. -/
def HintCRListSpan (w memBase : ℕ) (state : RAMState) : Prop :=
  (state.regs 0 = 0 ∧ state.regs 1 = 0) ∨
    (memBase ≤ state.regs 0 ∧ state.regs 0 ≤ memBase + 2 ^ w)

theorem hintCRSimulationList_total (P source : Program) (E : RAMEnv)
    (src p : RAMState) (w file memBase detBase logBase limit base fail ok B : ℕ) (det : ℕ → ℕ)
    (hL : CRSimLayout E w file memBase detBase logBase limit det)
    (hS : CRSimState w file memBase detBase logBase limit src p)
    (hAt : At P base (crSpillCompile source base fail ok))
    (hOutputAt : At P ok crOutputPrepare) (hFailAt : At P fail (crFailureReturn (ok + 7)))
    (hBudget : p.regs 14 = B) (hPc : p.pc = crSpillTarget source.length base fail src.pc) :
    Sem P E (crSpillTarget source.length base fail src.pc) (ok + 7) p (fun k out =>
      k ≤ 16 * B + 8 ∧ HintCRListSpan w memBase out ∧ out.regs 1 ≤ 2 ^ w ∧ out.regs 6 = p.regs 6 ∧
      CRMemFrame file (logBase + limit + 1) p.mem out.mem) := by
  obtain ⟨k, mid, srcOut, hK, hRun, hExit, hState, hRegs, hMemory⟩ :=
    crSimulation_exits_frame P source E w file memBase detBase logBase limit det base fail ok
      hL hAt B src p hS hBudget hPc
  have hSix : mid.regs 6 = p.regs 6 := hRegs 6 (by unfold CRSpillStable; decide)
  rcases hExit with hFail | hOk
  · have hFailRun := crFailureReturn_exec P E mid fail (ok + 7) hFailAt hFail
    refine ⟨hPc, 3 + k, crFailureState mid (ok + 7), ?_, rfl, by omega, ?_, ?_, ?_, hMemory⟩
    · rw [Function.iterate_add_apply, hRun, hFailRun]
    · left
      simp [crFailureState]
    · simp [crFailureState]
    · simpa only [crFailureState, Function.update_of_ne (by decide : (6 : Fin 16) ≠ 1),
        Function.update_of_ne (by decide : (6 : Fin 16) ≠ 0)] using hSix
  · have hLogTop : logBase < 2 ^ E.W := by have h := hL.log_word; omega
    have hMemLog : memBase + 2 ^ w < logBase :=
      (Nat.add_le_add_left (Nat.pow_le_pow_right (by norm_num) (by omega)) memBase).trans_lt hL.mem_before_log
    have hRead : memBase + 2 ^ w < 2 ^ E.W := hMemLog.trans hLogTop
    have hFile : file + 16 ≤ 2 ^ E.W := hL.file_before.trans ((Nat.le_add_right memBase (2 ^ w)).trans hRead.le)
    have hWide : w < E.W := by have h := hL.wide; omega
    have hNo : NoBranch crOutputPrepare := by simp [crOutputPrepare, crSpillLoad, NoBranch, Instr.NoBranchI]
    have hAtMid : At P mid.pc crOutputPrepare := by rw [hOk]; exact hOutputAt
    generalize hPrep : runBlock crOutputPrepare E mid = out
    have hExec : (step P E)^[7] mid = out := by
      have h := iterate_runBlock_of_at P E crOutputPrepare mid hAtMid hNo
      rw [hPrep] at h
      simpa only [crOutputPrepare_length] using h
    have hSpec := crOutputPrepare_spec E mid srcOut w file memBase hState.view hState.closed
      hWide hState.file_ptr hState.mem_ptr hFile hRead
    rw [hPrep] at hSpec
    obtain ⟨hOutPc, hOutMem, h0, h1, hOutFrame⟩ := hSpec
    have hEndPc : out.pc = ok + 7 := by rw [hOutPc, hOk]
    refine ⟨hPc, 7 + k, out, ?_, hEndPc, by omega, ?_, ?_, ?_, ?_⟩
    · rw [Function.iterate_add_apply, hRun, hExec]
    · right
      rw [h0]
      have hs := hState.closed.1 0
      omega
    · rw [h1]
      exact hState.closed.1 1
    · exact (hOutFrame 6 (by decide) (by decide)).trans hSix
    · rw [hOutMem]
      exact hMemory


/-- The initialized call is total for every binary source sketch, irrespective
    of whether that sketch represents a sparse input. -/
theorem hintCRCallList_total (S : CRSourceBundle) (G : Program) (E : RAMEnv)
    (N t off file memBase detBase logBase metaBase base fail ok : ℕ) (p : RAMState)
    (y : Fin (S.data N t).R → ZMod 2) (hN : 1 ≤ N) (ht : t ≤ N)
    (hL : CRSimLayout E (S.data N t).W file memBase detBase logBase (crSourceSteps S N t) (S.data N t).det)
    (h6 : p.regs 6 = metaBase) (hSpan : metaBase + 9 < 2 ^ E.W)
    (hHeader : CRCallHeader E metaBase (S.data N t).W (S.data N t).R off file memBase detBase logBase
      (crSourceSteps S N t))
    (hVM : ∀ a, a ≤ 2 ^ ((S.data N t).W + 1) →
      p.mem (memBase + a) = (decoderStart (S.data N t).W y []).mem a)
    (hInit : At G base crCallInit)
    (hCode : At G (base + 90) (crSpillCompile S.progDec (base + 90) fail ok))
    (hOutput : At G ok crOutputPrepare) (hFail : At G fail (crFailureReturn (ok + 7))) (hPc : p.pc = base) :
    Sem G E base (ok + 7) p (fun k out =>
      k ≤ 16 * crSourceSteps S N t + 98 ∧ HintCRListSpan (S.data N t).W memBase out ∧ out.regs 1 ≤ 2 ^ (S.data N t).W ∧ out.regs 6 = p.regs 6 ∧
      CRMemFrame file (logBase + crSourceSteps S N t + 1) p.mem out.mem) := by
  have hSpec := S.spec N t hN ht
  have hw : 0 < (S.data N t).W := by have hh := hSpec.1.1; omega
  have hStart := crCallInit_sem G E p base (S.data N t).W (S.data N t).R off file memBase detBase
    logBase (crSourceSteps S N t) metaBase (S.data N t).det y
    hInit hPc hw hSpec.2.1 hL h6 hSpan hHeader hVM
  obtain ⟨_, ki, mid, hRunInit, hMidPc, hKi, hState, hBudget, hSix, hInitFrame⟩ := hStart
  have hInitMemory : CRMemFrame file (logBase + crSourceSteps S N t + 1) p.mem mid.mem := by
    intro addr hOutside
    apply hInitFrame addr
    have hOrder : file + 16 ≤ logBase :=
      hL.file_before.trans ((Nat.le_add_right memBase _).trans hL.mem_before_log.le)
    rcases hOutside with hBefore | hAfter
    · exact Or.inl hBefore
    · exact Or.inr (by omega)
  have hNative := hintCRSimulationList_total G S.progDec E (decoderStart (S.data N t).W y []) mid
    (S.data N t).W file memBase detBase logBase (crSourceSteps S N t) (base + 90) fail ok
    (crSourceSteps S N t) (S.data N t).det hL hState hCode hOutput hFail hBudget
    (by simpa only [decoderStart, initState, crSource_entry_zero] using hMidPc)
  obtain ⟨_, kd, out, hRunDecode, hOutPc, hKd, hShape, hCount, hSixOut, hNativeMemory⟩ := hNative
  refine ⟨hPc, kd + ki, out, ?_, hOutPc, by omega, hShape, hCount, hSixOut.trans hSix,
    crMemFrame_trans hInitMemory hNativeMemory⟩
  rw [Function.iterate_add_apply, hRunInit, hRunDecode]

theorem hintCRInputList_total (S : CRSourceBundle) (G : Program) (E : RAMEnv)
    (N t off file memBase detBase logBase metaBase base fail ok : ℕ) (p : RAMState)
    (y : Fin (S.data N t).R → ZMod 2) (hN : 1 ≤ N) (ht : t ≤ N)
    (hL : CRSimLayout E (S.data N t).W file memBase detBase logBase (crSourceSteps S N t) (S.data N t).det)
    (h6 : p.regs 6 = metaBase) (hSpan : metaBase + 9 < 2 ^ E.W)
    (hHeader : CRCallHeader E metaBase (S.data N t).W (S.data N t).R off file memBase detBase logBase
      (crSourceSteps S N t))
    (hInputSpan : off + (S.data N t).R < 2 ^ E.W)
    (hBelow : (off + (S.data N t).R) / E.W < memBase)
    (hBits : ∀ i : Fin (S.data N t).R, bitAt p.mem E.W 0 (off + i.val) =
      if y i = 1 then 1 else 0)
    (hFresh : ∀ a, a ≤ 2 ^ ((S.data N t).W + 1) → p.mem (memBase + a) = 0)
    (hPrepare : At G base crCallPrepare)
    (hCopy : At G (base + 24) (crCopyInputLoop (base + 24) (base + 41)))
    (hInit : At G (base + 41) crCallInit)
    (hCode : At G (base + 131) (crSpillCompile S.progDec (base + 131) fail ok))
    (hOutput : At G ok crOutputPrepare) (hFail : At G fail (crFailureReturn (ok + 7))) (hPc : p.pc = base) :
    Sem G E base (ok + 7) p (fun k out =>
      k ≤ 17 * (S.data N t).R + 16 * crSourceSteps S N t + 124 ∧
      HintCRListSpan (S.data N t).W memBase out ∧ out.regs 1 ≤ 2 ^ (S.data N t).W ∧ out.regs 6 = p.regs 6 ∧ CRMemFrame file (logBase + crSourceSteps S N t + 1) p.mem out.mem) := by
  have hSpec := S.spec N t hN ht
  have hw : 0 < (S.data N t).W := by have hh := hSpec.1.1; omega
  have hWide : (S.data N t).W < E.W := by have hh := hL.wide; omega
  have hMem : memBase + 2 ^ (S.data N t).W < 2 ^ E.W := by
    have hPow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : (S.data N t).W ≤ (S.data N t).W + 1)
    have hh := hL.mem_before_log
    have hh' := hL.log_word
    omega
  have hPrep := crCallPrepare_spec E p metaBase (S.data N t).W (S.data N t).R off file memBase detBase
    logBase (crSourceSteps S N t) h6 hSpan hHeader
  have hAtP : At G p.pc crCallPrepare := by rw [hPc]; exact hPrepare
  have hRunPrep := iterate_runBlock_of_at G E crCallPrepare p hAtP crCallPrepare_noBranch
  rw [crCallPrepare_length, crCallPrepare_run] at hRunPrep
  have hPcPrep : (crCallPreparedRun E p).pc = base + 24 := by rw [hPrep.1, hPc]
  have hBitsPrep : ∀ i : Fin (S.data N t).R,
      bitAt (crCallPreparedRun E p).mem E.W 0 (off + i.val) =
        if y i = 1 then 1 else 0 := by
    rw [hPrep.2.1]
    exact hBits
  have hFreshPrep : ∀ a, a ≤ 2 ^ ((S.data N t).W + 1) → (crCallPreparedRun E p).mem (memBase + a) = 0 := by
    rw [hPrep.2.1]
    exact hFresh
  obtain ⟨mid, hRunCopy, hMidPc, _, _, hVM, hRegs, hCopyFrame⟩ :=
    crCopyInput_full G E (crCallPreparedRun E p) (S.data N t).W (S.data N t).R off memBase
      (base + 24) (base + 41) (y) hw hWide hSpec.2.1 hInputSpan hMem hBelow
      hBitsPrep hCopy hPcPrep hPrep.2.2.1 hPrep.2.2.2.2.2.1 hFreshPrep
  have hSix : mid.regs 6 = metaBase :=
    (hRegs 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hPrep.2.2.2.2.2.2.1
  have hCode' : At G ((base + 41) + 90) (crSpillCompile S.progDec ((base + 41) + 90) fail ok) := by
    simpa only [Nat.add_assoc] using hCode
  have hBeforeMemory : CRMemFrame file (logBase + crSourceSteps S N t + 1) p.mem mid.mem := by
    intro addr hOutside
    have h1 := hL.file_before
    have h2 := hL.mem_before_log
    have hCopyOutside : addr < memBase ∨ memBase + 2 ^ ((S.data N t).W + 1) < addr := by
      rcases hOutside with hBefore | hAfter
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    exact (hCopyFrame addr hCopyOutside).trans (congrFun hPrep.2.1 addr)
  have hNative := hintCRCallList_total S G E N t off file memBase detBase logBase metaBase
    (base + 41) fail ok mid y hN ht hL hSix hSpan hHeader hVM hInit hCode' hOutput hFail hMidPc
  obtain ⟨_, kd, out, hRunNative, hOutPc, hKd, hShape, hRecover, hSixOut, hNativeMemory⟩ := hNative
  refine ⟨hPc, (kd + (17 * (S.data N t).R + 2)) + 24, out, ?_, hOutPc,
    by omega, hShape, hRecover, hSixOut.trans (hSix.trans h6.symm), crMemFrame_trans hBeforeMemory hNativeMemory⟩
  rw [Function.iterate_add_apply, hRunPrep, Function.iterate_add_apply, hRunCopy, hRunNative]

theorem hintCRCodeList_total (S : CRSourceBundle) (G : Program) (E : RAMEnv)
    (N t off file memBase detBase logBase metaBase base : ℕ) (p : RAMState)
    (y : Fin (S.data N t).R → ZMod 2) (hN : 1 ≤ N) (ht : t ≤ N)
    (hL : CRSimLayout E (S.data N t).W file memBase detBase logBase (crSourceSteps S N t) (S.data N t).det)
    (h6 : p.regs 6 = metaBase) (hSpan : metaBase + 9 < 2 ^ E.W)
    (hHeader : CRCallHeader E metaBase (S.data N t).W (S.data N t).R off file memBase detBase logBase
      (crSourceSteps S N t))
    (hInputSpan : off + (S.data N t).R < 2 ^ E.W)
    (hBelow : (off + (S.data N t).R) / E.W < memBase)
    (hBits : ∀ i : Fin (S.data N t).R, bitAt p.mem E.W 0 (off + i.val) =
      if y i = 1 then 1 else 0)
    (hFresh : ∀ a, a ≤ 2 ^ ((S.data N t).W + 1) → p.mem (memBase + a) = 0)
    (hAt : At G base (crSourceInputCode S base)) (hPc : p.pc = base) :
    Sem G E base (base + (crSourceInputCode S base).length) p (fun k out =>
      k ≤ 17 * (S.data N t).R + 16 * crSourceSteps S N t + 124 ∧
      HintCRListSpan (S.data N t).W memBase out ∧ out.regs 1 ≤ 2 ^ (S.data N t).W ∧ out.regs 6 = p.regs 6 ∧ CRMemFrame file (logBase + crSourceSteps S N t + 1) p.mem out.mem) := by
  obtain ⟨hPrepare, hCopy, hInit, hKernel, hFail, hOutput⟩ := crSourceInputCode_at_parts G S base hAt
  rw [← crSourceInputCode_end]
  exact hintCRInputList_total S G E N t off file memBase detBase logBase metaBase base
    (crInputFail S base) (crInputOk S base) p y hN ht hL h6 hSpan hHeader hInputSpan hBelow hBits
    hFresh hPrepare hCopy hInit hKernel hOutput hFail hPc

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintCRCodeList_total


