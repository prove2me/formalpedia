-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintCRCall20261120
-- name    : LinearSetReconciliation327_Main_HintCRCall20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:26:53.013323+00:00
-- url     : https://prove2.me/theorems/aa3606ee-64fb-4ed1-be4f-0f251150e23c
-- title:
--   LinearSetReconciliation327 — HintCRCall (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintCRCall20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintCRInit20261120
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main

def crCallReadField (dest : Fin 16) (index : ℕ) : List Instr :=
  [.imm 0 index, .add 0 6 0, .qDet dest 0]

theorem crCallReadField_spec (E : RAMEnv) (p : RAMState) (dest : Fin 16) (index metaBase value : ℕ)
    (h6 : p.regs 6 = metaBase) (hIndex : index < 2 ^ E.W) (hAddr : metaBase + index < 2 ^ E.W)
    (hField : E.det (metaBase + index) % 2 ^ E.W = value) :
    let q := runBlock (crCallReadField dest index) E p
    q.pc = p.pc + 3 ∧ q.mem = p.mem ∧ q.regs dest = value ∧
      ∀ r, r ≠ 0 → r ≠ dest → q.regs r = p.regs r := by
  dsimp only
  refine ⟨?_, rfl, ?_, ?_⟩
  · simp [crCallReadField, runBlock, execInstr, Nat.add_assoc]
  · simp [crCallReadField, runBlock, execInstr, Function.update_apply, h6,
      Nat.mod_eq_of_lt hIndex, Nat.mod_eq_of_lt hAddr, hField]
  · intro r hr0 hrD
    simp [crCallReadField, runBlock, execInstr, Function.update_apply, hr0, hrD]

theorem crRFInit_start_view (E : RAMEnv) (p : RAMState) (w M file memBase : ℕ)
    (y : Fin M → ZMod 2) (hPtr : p.regs 8 = file) (hFile : file + 16 ≤ 2 ^ E.W)
    (hWords : p.regs 1 < 2 ^ E.W) (hCount : p.regs 1 = wordsOf w M)
    (hSeparate : file + 16 ≤ memBase)
    (hVM : ∀ a, a ≤ 2 ^ (w + 1) → p.mem (memBase + a) = (decoderStart w y []).mem a) :
    CRView w file memBase (decoderStart w y []) (runBlock crRFInit E p) := by
  constructor
  · intro r
    rw [crRFInit_registers E p file hPtr hFile hWords r, hCount]
    change (if r = 1 then wordsOf w M else 0) =
      (if r = 0 then 0 else if r = 1 then wordsOf w M else if r = 2 then 0 else 0)
    by_cases h0 : r = 0 <;> by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;> simp_all
  · intro a ha
    rw [crRFInit_mem_frame E p file (memBase + a) hPtr hFile hWords (Or.inr (by omega))]
    exact hVM a ha

theorem crDecoderStart_wordClosed (W : ℕ) (hW : 0 < W) {M : ℕ} (y : Fin M → ZMod 2)
    (hWords : wordsOf W M ≤ 2 ^ W) : CRWordClosed W (decoderStart W y []) := by
  constructor
  · intro r
    change (if r = 0 then 0 else if r = 1 then wordsOf W M else if r = 2 then 0 else 0) ≤ 2 ^ W
    split_ifs <;> first | exact hWords | exact Nat.zero_le _
  · intro a
    change hintMem W y [] a ≤ 2 ^ W
    unfold hintMem
    split_ifs
    · exact (packMem_lt W hW y a).le
    · simp

end LinearSetReconciliation327.Main
end
namespace LinearSetReconciliation327.Main

def crCallFinishMeta : List Instr :=
  crCallReadField 11 7 ++ (crCallReadField 14 8 ++ [.imm 12 0, .shl 13 15 7])

theorem crCallFinishMeta_length : crCallFinishMeta.length = 8 := rfl

theorem crCallFinishMeta_spec (E : RAMEnv) (p : RAMState) (w metaBase logBase budget : ℕ)
    (h6 : p.regs 6 = metaBase) (h7 : p.regs 7 = w) (h15 : p.regs 15 = 1)
    (hWide : w < E.W) (hMeta : metaBase + 9 < 2 ^ E.W)
    (hLog : E.det (metaBase + 7) % 2 ^ E.W = logBase)
    (hBudget : E.det (metaBase + 8) % 2 ^ E.W = budget) :
    let out := runBlock crCallFinishMeta E p
    out.pc = p.pc + 8 ∧ out.mem = p.mem ∧ out.regs 11 = logBase ∧ out.regs 14 = budget ∧
      out.regs 12 = 0 ∧ out.regs 13 = 2 ^ w ∧
      ∀ r, r ≠ 0 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → out.regs r = p.regs r := by
  let q := runBlock (crCallReadField 11 7) E p
  let u := runBlock (crCallReadField 14 8) E q
  have hQ := crCallReadField_spec E p 11 7 metaBase logBase h6 (by omega) (by omega) hLog
  have hQ6 : q.regs 6 = metaBase := (hQ.2.2.2 6 (by decide) (by decide)).trans h6
  have hU := crCallReadField_spec E q 14 8 metaBase budget hQ6 (by omega) (by omega) hBudget
  have hU7 : u.regs 7 = w := (hU.2.2.2 7 (by decide) (by decide)).trans
    ((hQ.2.2.2 7 (by decide) (by decide)).trans h7)
  have hU15 : u.regs 15 = 1 := (hU.2.2.2 15 (by decide) (by decide)).trans
    ((hQ.2.2.2 15 (by decide) (by decide)).trans h15)
  have hPow : 2 ^ w < 2 ^ E.W := Nat.pow_lt_pow_right (by decide) hWide
  have hRun : runBlock crCallFinishMeta E p = runBlock [.imm 12 0, .shl 13 15 7] E u := by
    rw [crCallFinishMeta, runBlock_append, runBlock_append]
  dsimp only
  rw [hRun]
  have hT : runBlock [.imm 12 0, .shl 13 15 7] E u =
      {u with pc := u.pc + 2, regs := Function.update (Function.update u.regs 12 0) 13 (2 ^ w)} := by
    simp [runBlock, execInstr, Function.update_apply, hU7, hU15,
      Nat.mod_eq_of_lt hPow, Nat.add_assoc]
  rw [hT]
  refine ⟨by rw [hU.1, hQ.1] <;> omega, hU.2.1.trans hQ.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Function.update_of_ne (by decide : (11 : Fin 16) ≠ 13),
      Function.update_of_ne (by decide : (11 : Fin 16) ≠ 12)]
    exact (hU.2.2.2 11 (by decide) (by decide)).trans hQ.2.2.1
  · simp only [Function.update_of_ne (by decide : (14 : Fin 16) ≠ 13),
      Function.update_of_ne (by decide : (14 : Fin 16) ≠ 12)]
    exact hU.2.2.1
  · simp
  · simp
  · intro r hr0 hr11 hr12 hr13 hr14
    simp only [Function.update_of_ne hr13, Function.update_of_ne hr12]
    exact (hU.2.2.2 r hr0 hr14).trans (hQ.2.2.2 r hr0 hr11)

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def crCallCountRun (E : RAMEnv) (p : RAMState) : RAMState := runBlock crWordCount E p
theorem crCallCountRun_eq (E : RAMEnv) (p : RAMState) : crCallCountRun E p = runBlock crWordCount E p := rfl
attribute [irreducible] crCallCountRun

def crCallRFRun (E : RAMEnv) (p : RAMState) : RAMState := runBlock crRFInit E (crCallCountRun E p)
theorem crCallRFRun_eq (E : RAMEnv) (p : RAMState) :
    crCallRFRun E p = runBlock crRFInit E (crCallCountRun E p) := rfl
attribute [irreducible] crCallRFRun

def crCallEntryRun (E : RAMEnv) (p : RAMState) : RAMState := runBlock crCallFinishMeta E (crCallRFRun E p)
theorem crCallEntryRun_eq (E : RAMEnv) (p : RAMState) :
    crCallEntryRun E p = runBlock crCallFinishMeta E (crCallRFRun E p) := rfl
attribute [irreducible] crCallEntryRun

theorem crRFInit_length : crRFInit.length = 53 := rfl

def crCallEntry : List Instr := crWordCount ++ (crRFInit ++ crCallFinishMeta)
theorem crCallEntry_length : crCallEntry.length = 66 := by
  simp [crCallEntry, crWordCount, crRFInit_length, crCallFinishMeta_length]

theorem crCallEntry_run (E : RAMEnv) (p : RAMState) : runBlock crCallEntry E p = crCallEntryRun E p := by
  rw [crCallEntry, runBlock_append, runBlock_append, ← crCallCountRun_eq, ← crCallRFRun_eq, ← crCallEntryRun_eq]

theorem crCallEntry_data (E : RAMEnv) (p : RAMState)
    (w M off file memBase detBase logBase budget metaBase : ℕ) (det : ℕ → ℕ) (y : Fin M → ZMod 2)
    (hw : 0 < w) (hM : M < 2 ^ E.W) (hWords : wordsOf w M ≤ 2 ^ w)
    (hL : CRSimLayout E w file memBase detBase logBase budget det)
    (hMeta : CRInputMeta E w M off memBase p)
    (hFilePtr : p.regs 8 = file) (hDetPtr : p.regs 10 = detBase) (h6 : p.regs 6 = metaBase)
    (hMetaSpan : metaBase + 9 < 2 ^ E.W)
    (hLog : E.det (metaBase + 7) % 2 ^ E.W = logBase)
    (hBudget : E.det (metaBase + 8) % 2 ^ E.W = budget)
    (hVM : ∀ a, a ≤ 2 ^ (w + 1) → p.mem (memBase + a) = (decoderStart w y []).mem a) :
    let q := crCallEntryRun E p
    q.pc = p.pc + 66 ∧ CRSimState w file memBase detBase logBase budget (decoderStart w y []) q ∧
      q.regs 14 = budget ∧ q.regs 6 = p.regs 6 ∧
      (∀ addr, (addr < file ∨ file + 16 ≤ addr) → q.mem addr = p.mem addr) := by
  let c := crCallCountRun E p
  let u := crCallRFRun E p
  have hWide : w < E.W := by have hh := hL.wide; omega
  have hFile : file + 16 ≤ 2 ^ E.W := by
    have hh := hL.file_before
    have hh' := hL.mem_before_log
    have hh'' := hL.log_word
    omega
  have hC := crWordCount_spec E p w M hw hWide hMeta.rows hMeta.source_width hM hWords
  rw [← crCallCountRun_eq] at hC
  have hC1 : c.regs 1 = wordsOf w M := hC.2.2.1
  have hC1Bound : c.regs 1 < 2 ^ E.W := by
    rw [hC1]
    exact hWords.trans_lt (Nat.pow_lt_pow_right (by decide) hWide)
  have hC8 : c.regs 8 = file := (hC.2.2.2 8 (by decide) (by decide) (by decide)).trans hFilePtr
  have hVMC : ∀ a, a ≤ 2 ^ (w + 1) → c.mem (memBase + a) = (decoderStart w y []).mem a := by
    intro a ha
    rw [hC.2.1]
    exact hVM a ha
  have hRF := crRFInit_spec E c file hC8 hFile hC1Bound
  have hRFview := crRFInit_start_view E c w M file memBase y hC8 hFile hC1Bound hC1 hL.file_before hVMC
  rw [← crCallRFRun_eq] at hRF hRFview
  have hFr : ∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → u.regs r = p.regs r := by
    intro r h0 h1 h2
    exact (hRF.2.2.1 r h0 h2).trans (hC.2.2.2 r h0 h1 h2)
  have hF := crCallFinishMeta_spec E u w metaBase logBase budget
    ((hFr 6 (by decide) (by decide) (by decide)).trans h6)
    ((hFr 7 (by decide) (by decide) (by decide)).trans hMeta.source_width)
    ((hFr 15 (by decide) (by decide) (by decide)).trans hMeta.one) hWide hMetaSpan hLog hBudget
  rw [← crCallEntryRun_eq] at hF
  have hStable : ∀ r, r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 15 →
      (crCallEntryRun E p).regs r = p.regs r := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hF.2.2.2.2.2.2 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (hFr _ (by decide) (by decide) (by decide))
  dsimp only
  refine ⟨?_, ?_, hF.2.2.2.1, hStable 6 (Or.inl rfl), ?_⟩
  · rw [hF.1, hRF.1, hC.1] <;> omega
  · refine ⟨crView_physical_mem hRFview hF.2.1, crDecoderStart_wordClosed w hw y hWords,
      (hStable 8 (by tauto)).trans hFilePtr, (hStable 9 (by tauto)).trans hMeta.mem_base,
      (hStable 10 (by tauto)).trans hDetPtr, hF.2.2.1, hF.2.2.2.2.2.1,
      (hStable 15 (by tauto)).trans hMeta.one, ?_⟩
    rw [hF.2.2.2.2.1, hF.2.2.2.1, Nat.zero_add]
  · intro addr hOutside
    rw [hF.2.1]
    have hFrame := crRFInit_mem_frame E c file addr hC8 hFile hC1Bound hOutside
    rw [← crCallRFRun_eq] at hFrame
    exact hFrame.trans (congrFun hC.2.1 addr)

theorem crCallEntry_noBranch : NoBranch crCallEntry := by
  have hAll : ∀ L : List ℕ, NoBranch (L.flatMap crRFZeroCell) := by
    intro L
    induction L with
    | nil => trivial
    | cons j rest ih =>
        rw [List.flatMap_cons, upNoBranch_append]
        exact ⟨by simp [crRFZeroCell, crSpillWrite, NoBranch, Instr.NoBranchI], ih⟩
  have hZero : NoBranch (crRFZeroCode 16) := hAll (List.range 16)
  simp [crCallEntry, crWordCount, crRFInit, hZero, crSpillWrite, crCallFinishMeta,
    crCallReadField, upNoBranch_append, NoBranch, Instr.NoBranchI]

theorem crCallEntry_sem (G : Program) (E : RAMEnv) (p : RAMState)
    (base w M off file memBase detBase logBase budget metaBase : ℕ) (det : ℕ → ℕ) (y : Fin M → ZMod 2)
    (hAt : At G base crCallEntry) (hPc : p.pc = base)
    (hw : 0 < w) (hM : M < 2 ^ E.W) (hWords : wordsOf w M ≤ 2 ^ w)
    (hL : CRSimLayout E w file memBase detBase logBase budget det)
    (hMeta : CRInputMeta E w M off memBase p)
    (hFilePtr : p.regs 8 = file) (hDetPtr : p.regs 10 = detBase) (h6 : p.regs 6 = metaBase)
    (hMetaSpan : metaBase + 9 < 2 ^ E.W)
    (hLog : E.det (metaBase + 7) % 2 ^ E.W = logBase)
    (hBudget : E.det (metaBase + 8) % 2 ^ E.W = budget)
    (hVM : ∀ a, a ≤ 2 ^ (w + 1) → p.mem (memBase + a) = (decoderStart w y []).mem a) :
    Sem G E base (base + 66) p (fun k out => k = 66 ∧
      CRSimState w file memBase detBase logBase budget (decoderStart w y []) out ∧
      out.regs 14 = budget ∧ out.regs 6 = p.regs 6 ∧
      (∀ addr, (addr < file ∨ file + 16 ≤ addr) → out.mem addr = p.mem addr)) := by
  have hData := crCallEntry_data E p w M off file memBase detBase logBase budget metaBase det y
    hw hM hWords hL hMeta hFilePtr hDetPtr h6 hMetaSpan hLog hBudget hVM
  have hBlock := Sem.block G E base crCallEntry p hAt crCallEntry_noBranch hPc
  have hExec : Sem G E base (base + 66) p
      (fun k out => k = 66 ∧ out = runBlock crCallEntry E p) := by
    simpa only [crCallEntry_length] using hBlock
  apply Sem.mono hExec
  intro k out hk
  refine ⟨hk.1, ?_⟩
  rw [hk.2, crCallEntry_run]
  exact hData.2

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

def crCallLoadFields (fields : List (Fin 16 × ℕ)) : List Instr :=
  fields.flatMap (fun pair => crCallReadField pair.1 pair.2)

def crCallFieldValue (E : RAMEnv) (metaBase : ℕ) : List (Fin 16 × ℕ) → Fin 16 → ℕ → ℕ
  | [], _, old => old
  | (dest, index) :: rest, r, old =>
      crCallFieldValue E metaBase rest r (if r = dest then E.det (metaBase + index) % 2 ^ E.W else old)

def crCallLoadedRun (E : RAMEnv) (fields : List (Fin 16 × ℕ)) (p : RAMState) : RAMState :=
  runBlock (crCallLoadFields fields) E p

theorem crCallLoadedRun_eq (E : RAMEnv) (fields : List (Fin 16 × ℕ)) (p : RAMState) :
    crCallLoadedRun E fields p = runBlock (crCallLoadFields fields) E p := rfl
attribute [irreducible] crCallLoadedRun

theorem crCallLoadFields_spec (E : RAMEnv) (metaBase : ℕ) (fields : List (Fin 16 × ℕ))
    (p : RAMState) (h6 : p.regs 6 = metaBase)
    (hFields : ∀ pair ∈ fields, pair.1 ≠ 6 ∧ metaBase + pair.2 < 2 ^ E.W) :
    let q := crCallLoadedRun E fields p
    q.pc = p.pc + 3 * fields.length ∧ q.mem = p.mem ∧ q.regs 6 = metaBase ∧
      ∀ r, r ≠ 0 → q.regs r = crCallFieldValue E metaBase fields r (p.regs r) := by
  rw [crCallLoadedRun_eq]
  induction fields generalizing p with
  | nil =>
      simp [crCallLoadFields, runBlock, crCallFieldValue, h6]
  | cons pair rest ih =>
      rcases pair with ⟨dest, index⟩
      let q := runBlock (crCallReadField dest index) E p
      have hValid := hFields (dest, index) (by simp)
      have hHead := crCallReadField_spec E p dest index metaBase (E.det (metaBase + index) % 2 ^ E.W)
        h6 (by omega) hValid.2 rfl
      have hQ6 : q.regs 6 = metaBase :=
        (hHead.2.2.2 6 (by decide) (Ne.symm hValid.1)).trans h6
      have hTail := ih q hQ6 (by intro pair hp; exact hFields pair (by simp [hp]))
      dsimp only
      rw [crCallLoadFields, List.flatMap_cons, runBlock_append]
      refine ⟨?_, hTail.2.1.trans hHead.2.1, hTail.2.2.1, ?_⟩
      · change (runBlock (crCallLoadFields rest) E q).pc = p.pc + 3 * (rest.length + 1)
        rw [hTail.1, hHead.1]
        omega
      · intro r hr0
        have hValue : q.regs r = if r = dest then E.det (metaBase + index) % 2 ^ E.W else p.regs r := by
          by_cases he : r = dest
          · subst r
            rw [if_pos rfl]
            exact hHead.2.2.1
          · rw [if_neg he]
            exact hHead.2.2.2 r hr0 he
        exact (hTail.2.2.2 r hr0).trans (congrArg (crCallFieldValue E metaBase rest r) hValue)

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

structure CRCallHeader (E : RAMEnv) (metaBase w M off file memBase detBase logBase budget : ℕ) : Prop where
  width_value : E.det metaBase % 2 ^ E.W = w
  rows_value : E.det (metaBase + 1) % 2 ^ E.W = M
  offset_value : E.det (metaBase + 2) % 2 ^ E.W = off
  file_value : E.det (metaBase + 3) % 2 ^ E.W = file
  mem_value : E.det (metaBase + 4) % 2 ^ E.W = memBase
  rom_value : E.det (metaBase + 5) % 2 ^ E.W = detBase
  physical_value : E.det (metaBase + 6) % 2 ^ E.W = E.W
  log_value : E.det (metaBase + 7) % 2 ^ E.W = logBase
  budget_value : E.det (metaBase + 8) % 2 ^ E.W = budget

def crCallCoreFields : List (Fin 16 × ℕ) := [(7, 0), (14, 1), (5, 2), (8, 3), (9, 4), (10, 5), (11, 6)]
def crCallPrepare : List Instr := crCallLoadFields crCallCoreFields ++ [.imm 12 0, .imm 13 2, .imm 15 1]

def crCallPreparedRun (E : RAMEnv) (p : RAMState) : RAMState :=
  runBlock [.imm 12 0, .imm 13 2, .imm 15 1] E (crCallLoadedRun E crCallCoreFields p)
theorem crCallPreparedRun_eq (E : RAMEnv) (p : RAMState) :
    crCallPreparedRun E p = runBlock [.imm 12 0, .imm 13 2, .imm 15 1] E (crCallLoadedRun E crCallCoreFields p) := rfl
attribute [irreducible] crCallPreparedRun

theorem crCallPrepare_spec (E : RAMEnv) (p : RAMState)
    (metaBase w M off file memBase detBase logBase budget : ℕ)
    (h6 : p.regs 6 = metaBase) (hSpan : metaBase + 9 < 2 ^ E.W)
    (hHeader : CRCallHeader E metaBase w M off file memBase detBase logBase budget) :
    let out := crCallPreparedRun E p
    out.pc = p.pc + 24 ∧ out.mem = p.mem ∧ CRInputMeta E w M off memBase out ∧
      out.regs 8 = file ∧ out.regs 10 = detBase ∧ out.regs 12 = 0 ∧
      out.regs 6 = metaBase ∧ out.regs 4 = p.regs 4 := by
  let q := crCallLoadedRun E crCallCoreFields p
  have hFields : ∀ pair ∈ crCallCoreFields, pair.1 ≠ 6 ∧ metaBase + pair.2 < 2 ^ E.W := by
    intro pair hp
    simp only [crCallCoreFields, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> first | decide | omega
  have hLoad := crCallLoadFields_spec E metaBase crCallCoreFields p h6 hFields
  have hR7 : q.regs 7 = w := by
    have hh := hLoad.2.2.2 7 (by decide)
    simpa [q, crCallCoreFields, crCallFieldValue, hHeader.width_value, hHeader.rows_value,
      hHeader.offset_value, hHeader.file_value, hHeader.mem_value, hHeader.rom_value, hHeader.physical_value] using hh
  have hR14 : q.regs 14 = M := by
    have hh := hLoad.2.2.2 14 (by decide)
    simpa [q, crCallCoreFields, crCallFieldValue, hHeader.width_value, hHeader.rows_value,
      hHeader.offset_value, hHeader.file_value, hHeader.mem_value, hHeader.rom_value, hHeader.physical_value] using hh
  have hR5 : q.regs 5 = off := by
    have hh := hLoad.2.2.2 5 (by decide)
    simpa [q, crCallCoreFields, crCallFieldValue, hHeader.width_value, hHeader.rows_value,
      hHeader.offset_value, hHeader.file_value, hHeader.mem_value, hHeader.rom_value, hHeader.physical_value] using hh
  have hR8 : q.regs 8 = file := by
    have hh := hLoad.2.2.2 8 (by decide)
    simpa [q, crCallCoreFields, crCallFieldValue, hHeader.width_value, hHeader.rows_value,
      hHeader.offset_value, hHeader.file_value, hHeader.mem_value, hHeader.rom_value, hHeader.physical_value] using hh
  have hR9 : q.regs 9 = memBase := by
    have hh := hLoad.2.2.2 9 (by decide)
    simpa [q, crCallCoreFields, crCallFieldValue, hHeader.width_value, hHeader.rows_value,
      hHeader.offset_value, hHeader.file_value, hHeader.mem_value, hHeader.rom_value, hHeader.physical_value] using hh
  have hR10 : q.regs 10 = detBase := by
    have hh := hLoad.2.2.2 10 (by decide)
    simpa [q, crCallCoreFields, crCallFieldValue, hHeader.width_value, hHeader.rows_value,
      hHeader.offset_value, hHeader.file_value, hHeader.mem_value, hHeader.rom_value, hHeader.physical_value] using hh
  have hR11 : q.regs 11 = E.W := by
    have hh := hLoad.2.2.2 11 (by decide)
    simpa [q, crCallCoreFields, crCallFieldValue, hHeader.width_value, hHeader.rows_value,
      hHeader.offset_value, hHeader.file_value, hHeader.mem_value, hHeader.rom_value, hHeader.physical_value] using hh
  have hR4 : q.regs 4 = p.regs 4 := by
    have hh := hLoad.2.2.2 4 (by decide)
    simpa [q, crCallCoreFields, crCallFieldValue, hHeader.width_value, hHeader.rows_value,
      hHeader.offset_value, hHeader.file_value, hHeader.mem_value, hHeader.rom_value, hHeader.physical_value] using hh
  have hPc : q.pc = p.pc + 3 * crCallCoreFields.length := hLoad.1
  have hTwo : 2 < 2 ^ E.W := by omega
  have hOne : 1 < 2 ^ E.W := by omega
  have hOut : crCallPreparedRun E p =
      {q with pc := q.pc + 3, regs := Function.update (Function.update (Function.update q.regs 12 0) 13 2) 15 1} := by
    rw [crCallPreparedRun_eq]
    change runBlock [.imm 12 0, .imm 13 2, .imm 15 1] E q = _
    simp [runBlock, execInstr, Function.update_apply, Nat.mod_eq_of_lt hTwo, Nat.mod_eq_of_lt hOne, Nat.add_assoc]
  have hFr : ∀ r, r ≠ 12 → r ≠ 13 → r ≠ 15 → (crCallPreparedRun E p).regs r = q.regs r := by
    intro r h12 h13 h15
    rw [hOut]
    simp only [Function.update_of_ne h15, Function.update_of_ne h13, Function.update_of_ne h12]
  have h12 : (crCallPreparedRun E p).regs 12 = 0 := by simp [hOut]
  have h13 : (crCallPreparedRun E p).regs 13 = 2 := by simp [hOut]
  have h15 : (crCallPreparedRun E p).regs 15 = 1 := by simp [hOut]
  dsimp only
  refine ⟨?_, ?_, ?_, (hFr 8 (by decide) (by decide) (by decide)).trans hR8,
    (hFr 10 (by decide) (by decide) (by decide)).trans hR10, h12,
    (hFr 6 (by decide) (by decide) (by decide)).trans hLoad.2.2.1,
    (hFr 4 (by decide) (by decide) (by decide)).trans hR4⟩
  · rw [hOut, hPc]
    rfl
  · rw [hOut]
    exact hLoad.2.1
  · exact ⟨(hFr 5 (by decide) (by decide) (by decide)).trans hR5,
      (hFr 7 (by decide) (by decide) (by decide)).trans hR7,
      (hFr 9 (by decide) (by decide) (by decide)).trans hR9,
      (hFr 11 (by decide) (by decide) (by decide)).trans hR11, h13,
      (hFr 14 (by decide) (by decide) (by decide)).trans hR14, h15⟩

end LinearSetReconciliation327.Main
namespace LinearSetReconciliation327.Main

theorem crCallLoadFields_length (fields : List (Fin 16 × ℕ)) :
    (crCallLoadFields fields).length = 3 * fields.length := by
  induction fields with
  | nil => rfl
  | cons pair rest ih =>
      change (crCallReadField pair.1 pair.2 ++ crCallLoadFields rest).length = _
      simp only [List.length_append, crCallReadField, List.length_cons, List.length_nil, ih]
      omega

theorem crCallPrepare_length : crCallPrepare.length = 24 := by
  simp only [crCallPrepare, List.length_append, crCallLoadFields_length]
  rfl

theorem crCallLoadFields_noBranch (fields : List (Fin 16 × ℕ)) :
    NoBranch (crCallLoadFields fields) := by
  induction fields with
  | nil => trivial
  | cons pair rest ih =>
      change NoBranch (crCallReadField pair.1 pair.2 ++ crCallLoadFields rest)
      rw [upNoBranch_append]
      exact ⟨by simp [crCallReadField, NoBranch, Instr.NoBranchI], ih⟩

theorem crCallPrepare_noBranch : NoBranch crCallPrepare := by
  rw [crCallPrepare, upNoBranch_append]
  exact ⟨crCallLoadFields_noBranch _, by simp [NoBranch, Instr.NoBranchI]⟩

theorem crCallPrepare_run (E : RAMEnv) (p : RAMState) :
    runBlock crCallPrepare E p = crCallPreparedRun E p := by
  rw [crCallPrepare, runBlock_append, ← crCallLoadedRun_eq, ← crCallPreparedRun_eq]

def crCallInit : List Instr := crCallPrepare ++ crCallEntry

def crCallInitRun (E : RAMEnv) (p : RAMState) : RAMState := crCallEntryRun E (crCallPreparedRun E p)
theorem crCallInitRun_eq (E : RAMEnv) (p : RAMState) :
    crCallInitRun E p = crCallEntryRun E (crCallPreparedRun E p) := rfl
attribute [irreducible] crCallInitRun

theorem crCallInit_length : crCallInit.length = 90 := by
  simp only [crCallInit, List.length_append, crCallPrepare_length, crCallEntry_length]

theorem crCallInit_run (E : RAMEnv) (p : RAMState) :
    runBlock crCallInit E p = crCallInitRun E p := by
  rw [crCallInit, runBlock_append, crCallPrepare_run, crCallEntry_run, ← crCallInitRun_eq]

theorem crCallInit_noBranch : NoBranch crCallInit := by
  rw [crCallInit, upNoBranch_append]
  exact ⟨crCallPrepare_noBranch, crCallEntry_noBranch⟩

theorem crCallInit_data (E : RAMEnv) (p : RAMState)
    (w M off file memBase detBase logBase budget metaBase : ℕ) (det : ℕ → ℕ) (y : Fin M → ZMod 2)
    (hw : 0 < w) (hWords : wordsOf w M ≤ 2 ^ w)
    (hL : CRSimLayout E w file memBase detBase logBase budget det)
    (h6 : p.regs 6 = metaBase) (hSpan : metaBase + 9 < 2 ^ E.W)
    (hHeader : CRCallHeader E metaBase w M off file memBase detBase logBase budget)
    (hVM : ∀ a, a ≤ 2 ^ (w + 1) → p.mem (memBase + a) = (decoderStart w y []).mem a) :
    let out := crCallInitRun E p
    out.pc = p.pc + 90 ∧ CRSimState w file memBase detBase logBase budget (decoderStart w y []) out ∧
      out.regs 14 = budget ∧ out.regs 6 = p.regs 6 ∧
      (∀ addr, (addr < file ∨ file + 16 ≤ addr) → out.mem addr = p.mem addr) := by
  have hPrep := crCallPrepare_spec E p metaBase w M off file memBase detBase logBase budget h6 hSpan hHeader
  have hM : M < 2 ^ E.W := by
    rw [← hHeader.rows_value]
    exact Nat.mod_lt _ (by positivity)
  have hVM' : ∀ a, a ≤ 2 ^ (w + 1) →
      (crCallPreparedRun E p).mem (memBase + a) = (decoderStart w y []).mem a := by
    intro a ha
    rw [hPrep.2.1]
    exact hVM a ha
  have hEntry := crCallEntry_data E (crCallPreparedRun E p) w M off file memBase detBase logBase budget metaBase det y
    hw hM hWords hL hPrep.2.2.1 hPrep.2.2.2.1 hPrep.2.2.2.2.1 hPrep.2.2.2.2.2.2.1 hSpan
    hHeader.log_value hHeader.budget_value hVM'
  dsimp only
  rw [crCallInitRun_eq]
  refine ⟨?_, hEntry.2.1, hEntry.2.2.1, ?_, ?_⟩
  · rw [hEntry.1, hPrep.1] <;> omega
  · exact hEntry.2.2.2.1.trans (hPrep.2.2.2.2.2.2.1.trans h6.symm)
  · intro addr hOutside
    exact (hEntry.2.2.2.2 addr hOutside).trans (congrFun hPrep.2.1 addr)

theorem crCallInit_sem (G : Program) (E : RAMEnv) (p : RAMState)
    (base w M off file memBase detBase logBase budget metaBase : ℕ) (det : ℕ → ℕ) (y : Fin M → ZMod 2)
    (hAt : At G base crCallInit) (hPc : p.pc = base)
    (hw : 0 < w) (hWords : wordsOf w M ≤ 2 ^ w)
    (hL : CRSimLayout E w file memBase detBase logBase budget det)
    (h6 : p.regs 6 = metaBase) (hSpan : metaBase + 9 < 2 ^ E.W)
    (hHeader : CRCallHeader E metaBase w M off file memBase detBase logBase budget)
    (hVM : ∀ a, a ≤ 2 ^ (w + 1) → p.mem (memBase + a) = (decoderStart w y []).mem a) :
    Sem G E base (base + 90) p (fun k out => k = 90 ∧
      CRSimState w file memBase detBase logBase budget (decoderStart w y []) out ∧
      out.regs 14 = budget ∧ out.regs 6 = p.regs 6 ∧
      (∀ addr, (addr < file ∨ file + 16 ≤ addr) → out.mem addr = p.mem addr)) := by
  have hData := crCallInit_data E p w M off file memBase detBase logBase budget metaBase det y
    hw hWords hL h6 hSpan hHeader hVM
  have hBlock := Sem.block G E base crCallInit p hAt crCallInit_noBranch hPc
  have hExec : Sem G E base (base + 90) p
      (fun k out => k = 90 ∧ out = runBlock crCallInit E p) := by
    simpa only [crCallInit_length] using hBlock
  apply Sem.mono hExec
  intro k out hk
  refine ⟨hk.1, ?_⟩
  rw [hk.2, crCallInit_run]
  exact hData.2

end LinearSetReconciliation327.Main
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem crSimulation_returns (P source : Program) (E : RAMEnv) (src sourceOut p : RAMState)
    (w file memBase detBase logBase limit N : ℕ) (det : ℕ → ℕ) (base fail ok B : ℕ) (T : ℝ)
    (x : Fin N → ZMod 2)
    (hL : CRSimLayout E w file memBase detBase logBase limit det)
    (hS : CRSimState w file memBase detBase logBase limit src p)
    (hAt : At P base (crSpillCompile source base fail ok))
    (hOutputAt : At P ok crOutputPrepare)
    (hBudget : p.regs 14 = B) (hPc : p.pc = crSpillTarget source.length base fail src.pc)
    (hSource : HaltsWithin source (detEnv w det) T src sourceOut) (hTime : T ≤ (B : ℝ))
    (hOutput : OutputsSupport sourceOut x) :
    Sem P E (crSpillTarget source.length base fail src.pc) (ok + 7) p
      (fun k out => k ≤ 16 * B + 8 ∧ OutputsSupport out x ∧ out.regs 6 = p.regs 6) := by
  obtain ⟨k, mid, hK, hRun, hOk, hState, hFrame⟩ := crSimulation_of_within P source E src sourceOut p
    w file memBase detBase logBase limit det base fail ok B T hL hS hAt hBudget hPc hSource hTime
  have hLogTop : logBase < 2 ^ E.W := by have h := hL.log_word; omega
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
  have hSpec := crOutputPrepare_spec E mid sourceOut w file memBase hState.view hState.closed
    hWide hState.file_ptr hState.mem_ptr hFile hRead
  rw [hPrep] at hSpec
  obtain ⟨hOutPc, hOutMem, h0, h1, hOutFrame⟩ := hSpec
  have hSupport := crOutputPrepare_support E mid sourceOut w file memBase N x hState.view hState.closed
    hWide hState.file_ptr hState.mem_ptr hFile hRead hOutput
  rw [hPrep] at hSupport
  have hEndPc : out.pc = ok + 7 := by rw [hOutPc, hOk]
  refine ⟨hPc, 7 + k, out, ?_, hEndPc, by omega, hSupport, ?_⟩
  · rw [Function.iterate_add_apply, hRun, hExec]
  · exact (hOutFrame 6 (by decide) (by decide)).trans (hFrame 6 (by unfold CRSpillStable; decide))

end LinearSetReconciliation327.Main
end
noncomputable section
namespace LinearSetReconciliation327.Main

theorem crSource_progDec_nonempty (S : CRSourceBundle) : S.progDec ≠ [] := by
  classical
  intro hEmpty
  let x : Fin 1 → ZMod 2 := 0
  have hx : (Finset.univ.filter fun i : Fin 1 => x i = 1).card ≤ 0 := by simp [x]
  obtain ⟨out, hRun, _⟩ := (S.spec 1 0 (by decide) (by decide)).2.2.2.2.2 x hx
  obtain ⟨_, _, _, hHalt⟩ := hRun
  simp [hEmpty, Halted] at hHalt

theorem crSource_progDec_pos (S : CRSourceBundle) : 0 < S.progDec.length := by
  have hh := crSource_progDec_nonempty S
  cases hp : S.progDec with
  | nil => exact False.elim (hh hp)
  | cons op rest => simp

theorem crSource_entry_zero (S : CRSourceBundle) (base fail : ℕ) :
    crSpillTarget S.progDec.length base fail 0 = base := by
  rw [crSpillTarget, if_pos (crSource_progDec_pos S), Nat.mul_zero, Nat.add_zero]

theorem crSource_native_returns (S : CRSourceBundle) (P : Program) (E : RAMEnv)
    (N t file memBase detBase logBase limit base fail ok : ℕ) (p : RAMState)
    (x : Fin N → ZMod 2) (hN : 1 ≤ N) (ht : t ≤ N)
    (hSupport : (Finset.univ.filter fun i => x i = 1).card ≤ t)
    (hL : CRSimLayout E (S.data N t).W file memBase detBase logBase limit (S.data N t).det)
    (hS : CRSimState (S.data N t).W file memBase detBase logBase limit
      (decoderStart (S.data N t).W ((S.data N t).H x) []) p)
    (hAt : At P base (crSpillCompile S.progDec base fail ok))
    (hOutputAt : At P ok crOutputPrepare)
    (hBudget : p.regs 14 = crSourceSteps S N t)
    (hPc : p.pc = base) :
    Sem P E base (ok + 7) p
      (fun k out => k ≤ 16 * crSourceSteps S N t + 8 ∧ OutputsSupport out x ∧ out.regs 6 = p.regs 6) := by
  obtain ⟨sourceOut, hRun, hOutput⟩ := (S.spec N t hN ht).2.2.2.2.2 x hSupport
  have hNative := crSimulation_returns P S.progDec E
    (decoderStart (S.data N t).W ((S.data N t).H x) []) sourceOut p
    (S.data N t).W file memBase detBase logBase limit N (S.data N t).det
    base fail ok (crSourceSteps S N t)
    (S.K * max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2))) x
    hL hS hAt hOutputAt hBudget (by simpa only [decoderStart, initState, crSource_entry_zero] using hPc)
    hRun (crSourceSteps_ge S N t) hOutput
  simpa only [decoderStart, initState, crSource_entry_zero] using hNative

end LinearSetReconciliation327.Main
end
noncomputable section
namespace LinearSetReconciliation327.Main

/-- A native call to the accepted sparse decoder.  The caller supplies the
    actual input sketch in its private VM; no decoder-output oracle is assumed. -/
theorem crSource_call_returns (S : CRSourceBundle) (G : Program) (E : RAMEnv)
    (N t off file memBase detBase logBase metaBase base fail ok : ℕ) (p : RAMState)
    (x : Fin N → ZMod 2) (hN : 1 ≤ N) (ht : t ≤ N)
    (hSupport : (Finset.univ.filter fun i => x i = 1).card ≤ t)
    (hL : CRSimLayout E (S.data N t).W file memBase detBase logBase (crSourceSteps S N t) (S.data N t).det)
    (h6 : p.regs 6 = metaBase) (hSpan : metaBase + 9 < 2 ^ E.W)
    (hHeader : CRCallHeader E metaBase (S.data N t).W (S.data N t).R off file memBase detBase logBase
      (crSourceSteps S N t))
    (hVM : ∀ a, a ≤ 2 ^ ((S.data N t).W + 1) →
      p.mem (memBase + a) = (decoderStart (S.data N t).W ((S.data N t).H x) []).mem a)
    (hInit : At G base crCallInit)
    (hCode : At G (base + 90) (crSpillCompile S.progDec (base + 90) fail ok))
    (hOutput : At G ok crOutputPrepare) (hPc : p.pc = base) :
    Sem G E base (ok + 7) p (fun k out =>
      k ≤ 16 * crSourceSteps S N t + 98 ∧ OutputsSupport out x ∧ out.regs 6 = p.regs 6) := by
  have hSpec := S.spec N t hN ht
  have hw : 0 < (S.data N t).W := by have hh := hSpec.1.1; omega
  have hStart := crCallInit_sem G E p base (S.data N t).W (S.data N t).R off file memBase detBase
    logBase (crSourceSteps S N t) metaBase (S.data N t).det ((S.data N t).H x)
    hInit hPc hw hSpec.2.1 hL h6 hSpan hHeader hVM
  obtain ⟨_, ki, mid, hRunInit, hMidPc, hKi, hState, hBudget, hSix, _⟩ := hStart
  have hNative := crSource_native_returns S G E N t file memBase detBase logBase
    (crSourceSteps S N t) (base + 90) fail ok mid x hN ht hSupport hL hState hCode hOutput hBudget hMidPc
  obtain ⟨_, kd, out, hRunDecode, hOutPc, hKd, hRecover, hSixOut⟩ := hNative
  refine ⟨hPc, kd + ki, out, ?_, hOutPc, by omega, hRecover, hSixOut.trans hSix⟩
  rw [Function.iterate_add_apply, hRunInit, hRunDecode]

end LinearSetReconciliation327.Main
end
noncomputable section
namespace LinearSetReconciliation327.Main

/-- The full input adapter reads the physical syndrome, constructs the source
    representation, then invokes the accepted decoder.  Its VM is private and fresh. -/
theorem crSource_input_call_returns (S : CRSourceBundle) (G : Program) (E : RAMEnv)
    (N t off file memBase detBase logBase metaBase base fail ok : ℕ) (p : RAMState)
    (x : Fin N → ZMod 2) (hN : 1 ≤ N) (ht : t ≤ N)
    (hSupport : (Finset.univ.filter fun i => x i = 1).card ≤ t)
    (hL : CRSimLayout E (S.data N t).W file memBase detBase logBase (crSourceSteps S N t) (S.data N t).det)
    (h6 : p.regs 6 = metaBase) (hSpan : metaBase + 9 < 2 ^ E.W)
    (hHeader : CRCallHeader E metaBase (S.data N t).W (S.data N t).R off file memBase detBase logBase
      (crSourceSteps S N t))
    (hInputSpan : off + (S.data N t).R < 2 ^ E.W)
    (hBelow : (off + (S.data N t).R) / E.W < memBase)
    (hBits : ∀ i : Fin (S.data N t).R, bitAt p.mem E.W 0 (off + i.val) =
      if (S.data N t).H x i = 1 then 1 else 0)
    (hFresh : ∀ a, a ≤ 2 ^ ((S.data N t).W + 1) → p.mem (memBase + a) = 0)
    (hPrepare : At G base crCallPrepare)
    (hCopy : At G (base + 24) (crCopyInputLoop (base + 24) (base + 41)))
    (hInit : At G (base + 41) crCallInit)
    (hCode : At G (base + 131) (crSpillCompile S.progDec (base + 131) fail ok))
    (hOutput : At G ok crOutputPrepare) (hPc : p.pc = base) :
    Sem G E base (ok + 7) p (fun k out =>
      k ≤ 17 * (S.data N t).R + 16 * crSourceSteps S N t + 124 ∧
      OutputsSupport out x ∧ out.regs 6 = p.regs 6) := by
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
        if (S.data N t).H x i = 1 then 1 else 0 := by
    rw [hPrep.2.1]
    exact hBits
  have hFreshPrep : ∀ a, a ≤ 2 ^ ((S.data N t).W + 1) → (crCallPreparedRun E p).mem (memBase + a) = 0 := by
    rw [hPrep.2.1]
    exact hFresh
  obtain ⟨mid, hRunCopy, hMidPc, _, _, hVM, hRegs, _⟩ :=
    crCopyInput_full G E (crCallPreparedRun E p) (S.data N t).W (S.data N t).R off memBase
      (base + 24) (base + 41) ((S.data N t).H x) hw hWide hSpec.2.1 hInputSpan hMem hBelow
      hBitsPrep hCopy hPcPrep hPrep.2.2.1 hPrep.2.2.2.2.2.1 hFreshPrep
  have hSix : mid.regs 6 = metaBase :=
    (hRegs 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hPrep.2.2.2.2.2.2.1
  have hCode' : At G ((base + 41) + 90) (crSpillCompile S.progDec ((base + 41) + 90) fail ok) := by
    simpa only [Nat.add_assoc] using hCode
  have hNative := crSource_call_returns S G E N t off file memBase detBase logBase metaBase
    (base + 41) fail ok mid x hN ht hSupport hL hSix hSpan hHeader hVM hInit hCode' hOutput hMidPc
  obtain ⟨_, kd, out, hRunNative, hOutPc, hKd, hRecover, hSixOut⟩ := hNative
  refine ⟨hPc, (kd + (17 * (S.data N t).R + 2)) + 24, out, ?_, hOutPc,
    by omega, hRecover, hSixOut.trans (hSix.trans h6.symm)⟩
  rw [Function.iterate_add_apply, hRunPrep, Function.iterate_add_apply, hRunCopy, hRunNative]

end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem crList_getD_past (J : List ℕ) (k : ℕ) (hk : J.length ≤ k) : J.getD k 0 = 0 := by
  induction J generalizing k with
  | nil => simp
  | cons x rest ih =>
      cases k with
      | zero => simp at hk
      | succ k =>
          exact (by simpa using ih k (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using hk))

theorem crDecoderStart_fresh {M : ℕ} (W : ℕ) (y : Fin M → ZMod 2) (J : List ℕ)
    (addr : ℕ) (hAddr : wordsOf W M + J.length ≤ addr) :
    (decoderStart W y J).mem addr = 0 := by
  have hOutside : ¬ addr < wordsOf W M := by omega
  have hPast : J.length ≤ addr - wordsOf W M := by omega
  simp only [decoderStart, initState, hintMem, if_neg hOutside]
  exact crList_getD_past J _ hPast

theorem crDecoderStart_freshVM {M : ℕ} (W : ℕ) (y : Fin M → ZMod 2) (J : List ℕ)
    (memBase w : ℕ) (hStart : wordsOf W M + J.length ≤ memBase) :
    ∀ a, a ≤ 2 ^ (w + 1) → (decoderStart W y J).mem (memBase + a) = 0 := by
  intro a _
  exact crDecoderStart_fresh W y J (memBase + a) (by omega)

/-- Disjoint callers preserve the zero values reserved for a future private VM. -/
theorem crFreshVM_after_frame (s s' : RAMState) (memBase w usedEnd : ℕ)
    (hFresh : ∀ a, a ≤ 2 ^ (w + 1) → s.mem (memBase + a) = 0)
    (hEnd : usedEnd ≤ memBase)
    (hFrame : ∀ addr, usedEnd ≤ addr → s'.mem addr = s.mem addr) :
    ∀ a, a ≤ 2 ^ (w + 1) → s'.mem (memBase + a) = 0 := by
  intro a ha
  rw [hFrame (memBase + a) (by omega)]
  exact hFresh a ha

end LinearSetReconciliation327.Main

#print axioms LinearSetReconciliation327.Main.crSource_input_call_returns
#print axioms LinearSetReconciliation327.Main.crDecoderStart_freshVM


