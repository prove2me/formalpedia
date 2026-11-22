-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_11
-- name    : LinearSetReconciliation327_Main_Bundle51_11
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T15:53:24.216842+00:00
-- url     : https://prove2.me/theorems/99eda5c2-d92f-4ade-ab37-df6a11cbc284
-- title:
--   LinearSetReconciliation327 鈥?Bundle51_11
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_11` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_09
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_10
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_11a

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_11
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintBinaryLeafAt20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintBinaryResidualTail20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDirectSchedule20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDirectPhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedDirectRead20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDirectReadPhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRecursiveSchedule20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDirectRootIndex20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintBinaryLeafAt20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintStoreAt_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node first word N : ℕ) (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hWord : 2 < 2 ^ E.W)
    (hEvent : D.events[first]? = some (.store node (word * E.W) N)) :
    let A := D.placement.arena node
    D.control + 2 < A.result →
    A.result < 2 ^ E.W →
    word * E.W < 2 ^ E.W →
    HintUnpackPre E A.result (word * E.W) N →
    (∀ pos : Fin D.events.length, pos.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H D.placement) pos.val + 3 < 2 ^ E.W) →
    (D.control + 2 < word ∨ word + wordsOf E.W N ≤ D.control + 2) →
    (∀ m m', CRMemFrame A.result (A.result + N) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      keep
      (fun m => (∀ q < N, m (A.result + q) < 2) ∧ keep m) := by
  let A := D.placement.arena node
  dsimp only
  intro hCtrl hDest hOffset hPre hDescriptor hInputFrame hKeep hCursor
  change D.control + 2 < A.result at hCtrl
  apply HintDecoderPhase.single (time := 12 * N + 12)
  · exact hCursor
  · rintro m v ⟨hb, hk⟩
    refine ⟨?_, hCursor m v hk⟩
    intro a ha
    rw [Function.update_of_ne (by omega : A.result + a ≠ D.control + 2)]
    exact hb a ha
  · intro pos hPos act base state
    dsimp only
    intro hSelect _ hAt hPc hArg hCtx _ hInv hRecord
    have he : D.events[pos.val]? = some (.store node (word * E.W) N) := by
      rw [hPos]
      exact hEvent
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans he)
    have hTag : D.events[pos.val].tag = 0 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintUnpackAction := (Option.some.inj hSelect).symm
    subst act
    rw [hEq] at hRecord
    let desc := hintEventDescriptor header D.events (hintEventRecord S H D.placement) pos.val
    have hBlock : (hintUnpackDetBlock A.result (word * E.W) E.W N).At E desc := by
      change (hintUnpackDetBlock A.result (word * E.W) D.placement.width N).At E desc at hRecord
      rw [← hWidth] at hRecord
      exact hRecord
    have hTable := HintUnpackTable.of_block E desc A.result (word * E.W) N hBlock hWord
      (hDescriptor pos hPos) hDest hOffset hPre.count_fit
    have hRun := hintUnpackAction_sem (hintNativeProgram S) E state desc A.result (word * E.W) N base
      hTable hArg hPre hAt hPc
    change Sem (hintNativeProgram S) E base (base + 22) state _
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hb, hf⟩
    refine ⟨hk, ⟨?_, hKeep _ _ hf hInv⟩, hc.trans hCtx, fun a _ ha => hf a (Or.inl (ha.trans_lt hCtrl))⟩
    intro i hi
    rw [hb i hi]
    unfold bitAt
    exact Nat.mod_lt _ (by decide)

noncomputable def hintCRAt_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node first word N t : ℕ) (keep : (ℕ → ℕ) → Prop)
    (hControl : D.placement.control = D.control)
    (hWidth : E.W = D.placement.width) (hW : 0 < E.W)
    (hN : 1 ≤ N) (ht : t ≤ N)
    (hWord : 11 < 2 ^ E.W) (hEvent : D.events[first]? = some (.decodeLeaf node (word * E.W) N t)) :
    let L := D.placement
    let A := L.arena node
    let data := S.data N t
    let spill := A.crRegisters + 16
    let spillSize := 2 ^ (data.W + 1) + 1
    let spillEnd := spill + spillSize + crSourceSteps S N t + 1
    D.control + 2 < A.result →
    A.result + N < A.crRegisters →
    spillEnd < 2 ^ E.W →
    data.W + 1 < E.W →
    L.crTable node + 2 ^ data.W < 2 ^ E.W →
    word * E.W + data.R < 2 ^ E.W →
    (word * E.W + data.R) / E.W < spill →
    (hintCRTableBlock data.W data.det).At E (L.crTable node) →
    (∀ pos : Fin D.events.length, pos.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 11 < 2 ^ E.W) →
    (D.control + 2 < word ∨ word + wordsOf E.W data.R ≤ D.control + 2) →
    (∀ m m', CRMemFrame A.result spillEnd m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      (fun m => HintFreshWords spill spillSize m ∧ keep m)
      (fun m => (∀ q < N, m (A.result + q) < 2) ∧ keep m) := by
  let L := D.placement
  let A := L.arena node
  let data := S.data N t
  let spill := A.crRegisters + 16
  let spillSize := 2 ^ (data.W + 1) + 1
  let spillEnd := spill + spillSize + crSourceSteps S N t + 1
  dsimp only
  intro hCtrl hOut hSpill hSmall hTable hInput hSep hCRTable hDescriptor hInputFrame hKeep hCursor
  change D.control + 2 < A.result at hCtrl
  change A.result + N < A.crRegisters at hOut
  change spillEnd < 2 ^ E.W at hSpill
  change (D.control + 2 < word ∨ word + wordsOf E.W data.R ≤ D.control + 2) at hInputFrame
  have hCtrlSpill : D.control + 2 < spill := by dsimp only [spill]; omega
  have hRegEnd : A.crRegisters < spillEnd := by
    dsimp only [spillEnd, spill]
    exact (Nat.lt_add_of_pos_right (by decide : 0 < 16)).trans_le
      ((Nat.le_add_right _ spillSize).trans ((Nat.le_add_right _ (crSourceSteps S N t)).trans (Nat.le_add_right _ 1)))
  have hCtrlWord : L.control < 2 ^ E.W := by change D.placement.control < _; rw [hControl]; omega
  apply HintDecoderPhase.single (time := hintCRNodeBudget S N t)
  · rintro m v ⟨hf, hk⟩
    exact ⟨hf.update_below _ _ hCtrlSpill, hCursor _ _ hk⟩
  · rintro m v ⟨hb, hk⟩
    refine ⟨?_, hCursor m v hk⟩
    intro a ha
    rw [Function.update_of_ne (by omega : A.result + a ≠ D.control + 2)]
    exact hb a ha
  · intro pos hPos act base state
    dsimp only
    intro hSelect hEntry hAt hPc hArg _ _ hInv hRecord
    have he : D.events[pos.val]? = some (.decodeLeaf node (word * E.W) N t) := by
      rw [hPos]
      exact hEvent
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans he)
    have hTag : D.events[pos.val].tag = hintNativeOtherActions.length := by rw [hEq]; rfl
    rw [hTag] at hSelect hEntry
    rw [hEq] at hRecord
    obtain ⟨hFresh, hK⟩ := hInv
    let desc := hintEventDescriptor header D.events (hintEventRecord S H L) pos.val
    let area := hintCRArea data.W (word * E.W) A.crRegisters (L.crTable node) desc A.result L.control
    have hBlock : (hintCREventBlock S L node (word * E.W) A.result N t).At E desc := hRecord
    have hReq : (hintCRCallBlock area E.W data.W data.R (crSourceSteps S N t) N).At E desc := by
      rw [hintCREventBlock_descriptor S L node _ _ _ _ desc] at hBlock
      simpa only [area, A, hWidth] using hBlock
    have hEnd : spill + 2 ^ (data.W + 1) + 1 + crSourceSteps S N t + 1 < 2 ^ E.W := by
      simpa only [spillEnd, spillSize, Nat.add_assoc] using hSpill
    have hPre := hintCRArea_pre S E N t (word * E.W) A.crRegisters (L.crTable node)
      desc A.result L.control hN ht hSmall hWord (hDescriptor pos hPos) hCtrlWord hEnd hTable
      hOut hInput hSep hCRTable hReq
    have hRun := hintCRNode_total S (hintNativeProgram S) E state area N t base 75 hintNativeOtherActions act
      hPre hPc hArg
      (fun a ha => hFresh a (Nat.lt_succ_of_le ha)) hSelect hEntry hAt
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hf, hb⟩
    have hFrame (a : ℕ) (ha : a < A.result ∨ spillEnd ≤ a) : out.mem a = state.mem a := by
      change (∀ q, (q < A.result ∨ A.result + N < q) →
        (q < A.crRegisters ∨ spillEnd ≤ q) → out.mem q = state.mem q) at hf
      rcases ha with h | h
      · exact hf a (Or.inl h) (Or.inl (by omega))
      · exact hf a (Or.inr (by omega)) (Or.inr h)
    refine ⟨hk, ⟨?_, hKeep _ _ hFrame hK⟩, hc.trans hControl, fun a _ ha => hFrame a (Or.inl (ha.trans_lt hCtrl))⟩
    intro i hi
    exact (hb i hi).elim (fun h => h ▸ (by decide : 0 < 2)) (fun h => h ▸ (by decide : 1 < 2))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintStoreAt_total
#print axioms LinearSetReconciliation327.Main.hintCRAt_total
end -- Def_LinearSetReconciliation327_Main_HintBinaryLeafAt20261120

section -- Def_LinearSetReconciliation327_Main_HintBinaryResidualTail20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintResidualDecode_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first t : ℕ) (N : ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hControl : D.placement.control = D.control)
    (hWidth : E.W = D.placement.width) (hW : 0 < E.W)
    (hN : 1 ≤ N) (ht : t ≤ N) (hWord : 11 < 2 ^ E.W)
    (hEvent : D.events[first]? = some (.decodeResidual node N t)) :
    let L := D.placement
    let A := L.arena node
    let w := (S.data N t).W
    let spill := A.crRegisters + 16
    let spillSize := 2 ^ (w + 1) + 1
    let spillEnd := spill + spillSize + crSourceSteps S N t + 1
    D.control + 2 < A.result →
    A.result + N ≤ A.residual →
    A.result + N ≤ A.residualBitmap →
    A.residualBitmap + N < A.crRegisters →
    spillEnd < 2 ^ E.W →
    w + 1 < E.W →
    L.crTable node + 2 ^ w < 2 ^ E.W →
    A.residual * E.W + (S.data N t).R < 2 ^ E.W →
    (A.residual * E.W + (S.data N t).R) / E.W < spill →
    (hintCRTableBlock w (S.data N t).det).At E (L.crTable node) →
    (∀ p : Fin D.events.length, p.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H L) p.val + 11 < 2 ^ E.W) →
    (∀ m m', CRMemFrame A.residualBitmap spillEnd m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      (fun m => HintBinaryMemory m A.result N ∧
        HintFreshWords spill spillSize m ∧ keep m)
      (fun m => HintBinaryMemory m A.result N ∧ HintBinaryMemory m A.residualBitmap N ∧ keep m) := by
  let L := D.placement
  let A := L.arena node
  let w := (S.data N t).W
  let spill := A.crRegisters + 16
  let spillSize := 2 ^ (w + 1) + 1
  let spillEnd := spill + spillSize + crSourceSteps S N t + 1
  dsimp only
  intro hCtrl hPayload hBefore hOut hEnd hSM hTable hIn hInSep hCRTable hDesc hKeep hCursor
  change D.control + 2 < A.result at hCtrl
  change A.result + N ≤ A.residual at hPayload
  change A.result + N ≤ A.residualBitmap at hBefore
  change A.residualBitmap + N < A.crRegisters at hOut
  change spillEnd < 2 ^ E.W at hEnd
  have hPow : 0 < 2 ^ (w + 1) := Nat.two_pow_pos _
  have hSpillAfter : A.crRegisters < spillEnd := by dsimp [spillEnd, spill, spillSize]; omega
  have hControlWord : L.control < 2 ^ E.W := by
    change D.placement.control < 2 ^ E.W
    rw [hControl]
    omega
  have hCtrlP : D.control + 2 < A.residual := by omega
  have hCtrlB : D.control + 2 < A.residualBitmap := by omega
  have hCtrlSpill : D.control + 2 < spill := by
    change D.control + 2 < A.crRegisters + 16
    omega
  apply HintDecoderPhase.single (time := hintCRNodeBudget S N t)
  · rintro m v ⟨hb, hf, hk⟩
    exact ⟨hb.update_below _ hCtrl,
      hf.update_below _ _ hCtrlSpill, hCursor _ _ hk⟩
  · rintro m v ⟨hb, he, hk⟩
    exact ⟨hb.update_below _ hCtrl, he.update_below _ hCtrlB, hCursor _ _ hk⟩
  · intro pos hPos act base state
    dsimp only
    intro hSelect hEntry hAt hPc hArg hCtx _ hStart hRec
    have hOpt : D.events[pos.val]? = some (.decodeResidual node N t) := by
      rw [hPos]
      exact hEvent
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans hOpt)
    have hTag : D.events[pos.val].tag = 6 := by rw [hEq]; rfl
    rw [hTag] at hSelect hEntry
    rw [hEq] at hRec
    obtain ⟨hEst, hFresh, hK⟩ := hStart
    let descriptor := hintEventDescriptor header D.events (hintEventRecord S H L) pos.val
    have hRec' : (hintCREventBlock S L node (A.residual * L.width) A.residualBitmap N t).At E
        descriptor := hRec
    let data := S.data N t
    let area := hintCRArea data.W (A.residual * E.W) A.crRegisters (L.crTable node) descriptor A.residualBitmap L.control
    have hReq : (hintCRCallBlock area E.W data.W data.R (crSourceSteps S N t) N).At E descriptor := by
      rw [hintCREventBlock_descriptor S L node _ _ _ _ descriptor] at hRec'
      have hWidth' : L.width = E.W := hWidth.symm
      simpa only [area, A, data, hWidth'] using hRec'
    have hSpillBound : spill + 2 ^ (data.W + 1) + 1 + crSourceSteps S N t + 1 < 2 ^ E.W := by
      simpa only [spillEnd, spillSize, w, data, Nat.add_assoc] using hEnd
    have hPre := hintCRArea_pre S E N t (A.residual * E.W) A.crRegisters (L.crTable node)
      descriptor A.residualBitmap L.control hN ht hSM hWord (hDesc pos hPos) hControlWord hSpillBound hTable
      hOut hIn hInSep hCRTable hReq
    have hRun := hintCRNode_total S (hintNativeProgram S) E state area N t base 75 hintNativeOtherActions act
      hPre hPc hArg (fun a ha => hFresh a (Nat.lt_succ_of_le ha)) hSelect hEntry hAt
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hf, hb⟩
    have hBinary : HintBinaryMemory out.mem A.residualBitmap N := by
      intro q hq
      have he : area.destination = A.residualBitmap := rfl
      have hBit := hb q hq
      rw [he] at hBit
      change out.mem (A.residualBitmap + q) < 2
      omega
    have hf' : ∀ a, (a < A.residualBitmap ∨ A.residualBitmap + N < a) →
        (a < A.crRegisters ∨ spillEnd ≤ a) → out.mem a = state.mem a := hf
    have frame : CRMemFrame A.residualBitmap spillEnd state.mem out.mem := by
      intro a ha
      rcases ha with h | h
      · exact hf' a (Or.inl h) (Or.inl (h.trans (by omega)))
      · exact hf' a (Or.inr (by omega)) (Or.inr h)
    refine ⟨hk, ⟨?_, hBinary, hKeep _ _ frame hK⟩, hc.trans hControl, ?_⟩
    · intro q hq
      have hBeforeBit : A.result + q < A.residualBitmap := by omega
      rw [frame _ (Or.inl hBeforeBit)]
      exact hEst q hq
    · intro a _ ha
      exact frame a (Or.inl (by omega))

noncomputable def hintCorrectEstimate_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first : ℕ) (N : ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hInfo : (D.placement.info node).universeSize = N)
    (hEvent : D.events[first]? = some (.correctEstimate node)) :
    let A := D.placement.arena node
    1 < 2 ^ E.W →
    D.control + 2 < A.result →
    A.result < 2 ^ E.W →
    A.residualBitmap < 2 ^ E.W →
    N < 2 ^ E.W →
    A.result + N ≤ A.residualBitmap →
    A.residualBitmap + N ≤ 2 ^ E.W →
    (∀ p : Fin D.events.length, p.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H D.placement) p.val + 2 < 2 ^ E.W) →
    (∀ m m', CRMemFrame A.result (A.result + N) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      (fun m => HintBinaryMemory m A.result N ∧
        HintBinaryMemory m A.residualBitmap N ∧ keep m)
      (fun m => HintBinaryMemory m A.result N ∧ keep m) := by
  let A := D.placement.arena node
  dsimp only
  intro hWord hCtrl hDest hSource hSize hSep hEnd hDescriptor hKeep hCursor
  have hCtrlSrc : D.control + 2 < A.residualBitmap := by
    change D.control + 2 < A.result at hCtrl
    change A.result + N ≤ A.residualBitmap at hSep
    omega
  apply HintDecoderPhase.single (time := 11 * N + 11)
  · rintro m v ⟨hE, hR, hk⟩
    exact ⟨hE.update_below _ hCtrl, hR.update_below _ hCtrlSrc, hCursor _ _ hk⟩
  · rintro m v ⟨hX, hk⟩
    exact ⟨hX.update_below _ hCtrl, hCursor _ _ hk⟩
  · intro pos hPos act base state
    dsimp only
    intro hSelect _ hAt hPc hArg hCtx _ hPre hRec
    have hOpt : D.events[pos.val]? = some (.correctEstimate node) := by
      rw [hPos]
      exact hEvent
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans hOpt)
    have hTag : D.events[pos.val].tag = 5 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintColumnAddAction := (Option.some.inj hSelect).symm
    subst act
    rw [hEq] at hRec
    obtain ⟨hE, hR, hk⟩ := hPre
    obtain ⟨estimate, _, hEstimate⟩ := hE.to_bitmap
    obtain ⟨err, _, hError⟩ := hR.to_bitmap
    let descriptor := hintEventDescriptor header D.events (hintEventRecord S H D.placement) pos.val
    have hBlock : (hintColumnAddBlock A.result A.residualBitmap N).At E descriptor := by
      simpa only [hintEventRecord, hInfo] using hRec
    have hTable := HintColumnAddTable.of_block E descriptor A.result A.residualBitmap N
      hBlock hWord (hDescriptor pos hPos) hDest hSource (hSep.trans hSource.le) hEnd hSize
    have hRun := hintAddBitmaps_sem (hintNativeProgram S) E state descriptor A.result A.residualBitmap N base
      estimate err hTable hArg hEstimate hError (Or.inl hSep) hAt hPc
    change Sem (hintNativeProgram S) E base (base + 20) state _
    apply Sem.mono hRun
    rintro k out ⟨ht, hc, hX, hf⟩
    exact ⟨ht, ⟨HintBinaryMemory.of_bitmap hX, hKeep _ _ hf hk⟩, hc.trans hCtx,
      fun a _ ha => hf a (Or.inl (ha.trans_lt hCtrl))⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintResidualDecode_total
#print axioms LinearSetReconciliation327.Main.hintCorrectEstimate_total
end -- Def_LinearSetReconciliation327_Main_HintBinaryResidualTail20261120

section -- Def_LinearSetReconciliation327_Main_HintDirectSchedule20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintDirectReads (sch : RowScheme) (node offset : ℕ) : List HintTreeEvent :=
  (List.ofFn fun j : Fin sch.m => (List.range sch.ℓ).map fun s =>
    HintTreeEvent.directBit node j.val s (offset + j.val * sch.ℓ + s)).flatten

theorem hintTreeEvents_direct {CR : CRFamily} (payloadOffset : ℕ → ℕ)
    (sch : RowScheme) (t node seedIndex offset : ℕ) :
    hintTreeEvents CR payloadOffset (.direct sch t) node seedIndex offset =
      hintDirectReads sch node offset ++
        (List.range sch.m).map (.finishRow node seedIndex) ++
        hintResidualEvents CR node (offset + sch.m * sch.ℓ) sch.N t := by
  rw [hintTreeEvents]
  rfl

theorem hintDirectReads_length (sch : RowScheme) (node offset : ℕ) :
    (hintDirectReads sch node offset).length = sch.m * sch.ℓ := by
  unfold hintDirectReads
  rw [length_flatten_ofFn]
  simp

theorem hintDirectReads_at (sch : RowScheme) (node offset : ℕ)
    (j : Fin sch.m) (s : Fin sch.ℓ) :
    (hintDirectReads sch node offset)[j.val * sch.ℓ + s.val]? =
      some (.directBit node j.val s.val (offset + j.val * sch.ℓ + s.val)) := by
  let row : Fin sch.m → List HintTreeEvent := fun i =>
    (List.range sch.ℓ).map fun c => .directBit node i.val c (offset + i.val * sch.ℓ + c)
  have hLen (i : Fin sch.m) : (row i).length = sch.ℓ := by simp [row]
  have hAt := getElem?_flatten_ofFn' sch.m row j s.val (by rw [hLen]; exact s.isLt)
  have hBefore : ((List.ofFn fun i => (row i).length).take j.val).sum = j.val * sch.ℓ := by
    rw [take_sum_ofFn_eq_sum_fin _ j.isLt.le]
    simp [hLen]
  rw [hBefore] at hAt
  change (List.ofFn row).flatten[j.val * sch.ℓ + s.val]? = _
  rw [hAt]
  have hInside : s.val < (List.range sch.ℓ).length := by simpa using s.isLt
  simp [row, List.getElem?_map, List.getElem?_eq_getElem hInside]

theorem hintDirectReads_split {sch : RowScheme} (i : Fin (sch.m * sch.ℓ)) :
    ∃ j : Fin sch.m, ∃ s : Fin sch.ℓ, i.val = j.val * sch.ℓ + s.val := by
  let js := finProdFinEquiv.symm i
  refine ⟨js.1, js.2, ?_⟩
  have h := congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv i)
  change js.2.val + sch.ℓ * js.1.val = i.val at h
  rw [Nat.mul_comm sch.ℓ, Nat.add_comm] at h
  exact h.symm

theorem hintTranscript_read_step (sch : RowScheme) (r : sch.LocalSeed) (x : Finset ℕ)
    (transcript : ℕ) (before after : ℕ → ℕ) (j : Fin sch.m) (s : Fin sch.ℓ)
    (hPrev : HintTranscriptCorrect sch r x transcript
      (fun j' s' => j'.val * sch.ℓ + s'.val < j.val * sch.ℓ + s.val) before)
    (hNew : after (hintTranscriptCell transcript sch.m j.val s.val) =
       (sch.code j (r.2 j) (sch.rowOf r x j) s).val)
    (hFrame : CRMemFrame (hintTranscriptCell transcript sch.m j.val s.val)
      (hintTranscriptCell transcript sch.m j.val s.val + 1) before after) :
    HintTranscriptCorrect sch r x transcript
      (fun j' s' => j'.val * sch.ℓ + s'.val < j.val * sch.ℓ + s.val + 1) after := by
  have hWrite := hintTranscript_write sch r x transcript _ before after j s hPrev hNew hFrame
  intro j' s' hRead
  apply hWrite j' s'
  by_cases hEq : j'.val * sch.ℓ + s'.val = j.val * sch.ℓ + s.val
  · have hCell : hintTranscriptCell 0 sch.ℓ s'.val j'.val =
        hintTranscriptCell 0 sch.ℓ s.val j.val := by
      simpa only [hintTranscriptCell, Nat.zero_add] using hEq
    obtain ⟨hs, hj⟩ := (hintTranscriptCell_eq_iff 0 s' s j' j).mp hCell
    exact Or.inr ⟨hj, hs⟩
  · exact Or.inl (by omega)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectReads_at
#print axioms LinearSetReconciliation327.Main.hintTranscript_read_step
end -- Def_LinearSetReconciliation327_Main_HintDirectSchedule20261120

section -- Def_LinearSetReconciliation327_Main_HintDirectPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintDirectPhase_step {CR : CRFamily} (P : Program) (E : RAMEnv) (state : RAMState)
    (sch : RowScheme) (t : ℕ) (r : sch.LocalSeed) (x : Finset ℕ)
    (node word transcript descriptor base : ℕ) (i : Fin (sch.m * sch.ℓ))
    (event : HintTreeEvent)
    (hEvent : (hintDirectReads sch node (word * E.W))[i.val]? = some event)
    (hRecord : ∀ row col offset, event = .directBit node row col offset →
      (hintDirectBitBlock E.W transcript sch.m row col offset).At E descriptor)
    (hPacked : ∀ a < wordsOf E.W (synLen CR (.direct sch t)),
      state.mem (word + a) = packMem E.W (hintSketchVector CR (.direct sch t) r x) a)
    (hRead : HintTranscriptCorrect sch r x transcript (fun j s => j.val * sch.ℓ + s.val < i.val) state.mem)
    (hW : 0 < E.W) (hWord : 2 < 2 ^ E.W) (hDescSpan : descriptor + 3 < 2 ^ E.W)
    (hInput : word * E.W + synLen CR (.direct sch t) ≤ 2 ^ E.W)
    (hSep : word + wordsOf E.W (synLen CR (.direct sch t)) ≤ transcript)
    (hBefore : (word * E.W + synLen CR (.direct sch t)) / E.W < transcript)
    (hTranscript : transcript + sch.m * sch.ℓ ≤ 2 ^ E.W)
    (hArg : state.regs 6 = descriptor)
    (hAt : At P base (hintUnpackAction.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 22) state (fun k out => k ≤ 24 ∧
      out.regs 14 = state.regs 14 ∧
      (∀ a < wordsOf E.W (synLen CR (.direct sch t)),
        out.mem (word + a) = packMem E.W (hintSketchVector CR (.direct sch t) r x) a) ∧
      HintTranscriptCorrect sch r x transcript (fun j s => j.val * sch.ℓ + s.val < i.val + 1) out.mem ∧
      CRMemFrame transcript (transcript + sch.m * sch.ℓ) state.mem out.mem) := by
  obtain ⟨j, s, hIdx⟩ := hintDirectReads_split i
  have hEvent' := hintDirectReads_at sch node (word * E.W) j s
  rw [hIdx, hEvent'] at hEvent
  have hTab := hRecord j.val s.val (word * E.W + j.val * sch.ℓ + s.val) (Option.some.inj hEvent.symm)
  have hPre := hintDirectBit_pre (CR := CR) E sch t word transcript j s hW hWord hInput hBefore hTranscript
  have hRun := hintDirectBit_sem (CR := CR) P E state sch t r x j s word transcript descriptor base
    hPacked hArg hWord hDescSpan hTab hPre hAt hPc
  apply Sem.mono hRun
  rintro k out ⟨hk, hc, hb, hf⟩
  have hPrev := hRead
  simp only [hIdx] at hPrev ⊢
  have hCell := hintPairOffset_lt s j
  rw [Nat.mul_comm sch.ℓ sch.m] at hCell
  have hKeep : CRMemFrame transcript (transcript + sch.m * sch.ℓ) state.mem out.mem := by
    intro addr ha
    apply hf
    unfold hintTranscriptCell
    rcases ha with ha | ha
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  refine ⟨hk, hc, ?_, hintTranscript_read_step sch r x transcript state.mem out.mem j s hPrev hb hf, hKeep⟩
  intro a ha
  rw [hKeep _ (Or.inl (by omega)), hPacked a ha]

theorem hintDirectPhase_end (sch : RowScheme) (r : sch.LocalSeed) (x : Finset ℕ)
    (transcript : ℕ) (mem : ℕ → ℕ)
    (h : HintTranscriptCorrect sch r x transcript (fun j s => j.val * sch.ℓ + s.val < sch.m * sch.ℓ) mem) :
    HintTranscriptCorrect sch r x transcript (fun _ _ => True) mem :=
  fun j s _ => h j s (hintPairOffset_lt j s)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectPhase_step
#print axioms LinearSetReconciliation327.Main.hintDirectPhase_end
end -- Def_LinearSetReconciliation327_Main_HintDirectPhase20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedDirectRead20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintPlacedDirectRead_step (S : CRSourceBundle) (H : HintParams)
    (N X Y t W Bc header : ℕ) (lr : (H.scheme N X Y).LocalSeed) (x : Finset ℕ)
    (E : RAMEnv) (state : RAMState) (up previous : ℕ → ℕ) (base : ℕ)
    (i : Fin ((H.scheme N X Y).m * (H.scheme N X Y).ℓ))
    (hWidth : E.W = W) (hHeader : 3 < header)
    (hDet : E.det = (hintDecoderTables S H (.direct N X Y t) W Bc header).det S H up previous header N)
    (hWord : 2 < 2 ^ E.W) (hW : 0 < E.W)
    (hInput : synLen (crFamily S) (.direct (H.scheme N X Y) t) ≤ 2 ^ E.W)
    (hPacked : ∀ a < wordsOf E.W (synLen (crFamily S) (.direct (H.scheme N X Y) t)),
      state.mem a = packMem E.W (hintSketchVector (crFamily S) (.direct (H.scheme N X Y) t) lr x) a)
    (hAt : At (hintNativeProgram S) base (hintUnpackAction.compile base)) (hPc : state.pc = base) :
    let sch := H.scheme N X Y
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    let transcript := (D.placement.arena 0).transcript
    let record := hintEventRecord S H D.placement
    let descriptor := hintEventDescriptor header D.events record i.val
    descriptor + 3 < 2 ^ E.W → state.regs 6 = descriptor →
    transcript + sch.m * sch.ℓ ≤ 2 ^ E.W →
    HintTranscriptCorrect sch lr x transcript (fun j s => j.val * sch.ℓ + s.val < i.val) state.mem →
    Sem (hintNativeProgram S) E base (base + 22) state (fun k out =>
      k ≤ 24 ∧ out.regs 14 = state.regs 14 ∧
      (∀ a < wordsOf E.W (synLen (crFamily S) (.direct sch t)),
        out.mem a = packMem E.W (hintSketchVector (crFamily S) (.direct sch t) lr x) a) ∧
      HintTranscriptCorrect sch lr x transcript (fun j s => j.val * sch.ℓ + s.val < i.val + 1) out.mem ∧
      CRMemFrame transcript (transcript + sch.m * sch.ℓ) state.mem out.mem) := by
  let CR := crFamily S
  let sch := H.scheme N X Y
  let D := hintDecoderTables S H (.direct N X Y t) W Bc header
  let A := D.placement.arena 0
  let M := synLen CR (.direct sch t)
  let record := hintEventRecord S H D.placement
  let desc := hintEventDescriptor header D.events record i.val
  have hPrefix : D.events = hintDirectReads sch 0 0 ++
      (List.range sch.m).map (.finishRow 0 0) ++ hintResidualEvents CR 0 (sch.m * sch.ℓ) sch.N t := by
    change hintTreeEvents CR (fun node => if node = 0 then 0 else (D.placement.arena node).payload * W)
      (.direct sch t) 0 0 0 = _
    simpa only [Nat.zero_add] using
      (hintTreeEvents_direct (CR := CR) (fun node => if node = 0 then 0 else (D.placement.arena node).payload * W)
        sch t 0 0 0)
  have hReadLt : i.val < (hintDirectReads sch 0 0).length := by
    rw [hintDirectReads_length]
    exact i.isLt
  have hIn : i.val < D.events.length := by
    simp only [hPrefix, List.length_append]
    omega
  let pos : Fin D.events.length := ⟨i.val, hIn⟩
  have hEvent : (hintDirectReads sch 0 0)[i.val]? = some D.events[pos.val] := by
    have hIdx : D.events[i.val]? = (hintDirectReads sch 0 0)[i.val]? := by
      rw [hPrefix, List.append_assoc, List.getElem?_append_left hReadLt]
    exact hIdx.symm.trans (List.getElem?_eq_getElem (l := D.events) hIn)
  have hPlaced := hintDecoderTables_event_At S H D E up previous header N hHeader hDet pos
  have hTable (row col off : ℕ) (h : D.events[pos.val] = .directBit 0 row col off) :
      (hintDirectBitBlock E.W A.transcript sch.m row col off).At E desc := by
    change (record D.events[pos.val]).At E desc at hPlaced
    rw [h] at hPlaced
    rw [hWidth]
    exact hPlaced
  have hArena (start : ℕ) :
      (hintArenaFor S H W (hintNodeInfo (P := H) CR (.direct N X Y t) 0 0) start).transcript =
        (hintNodeArena start W M 1 sch.m sch.ℓ N (S.data N t).R (S.data N t).W (crSourceSteps S N t)).transcript := rfl
  have hMemBefore : M / E.W < A.transcript := by
    rw [hWidth]
    change M / W < (hintArenaFor S H W (hintNodeInfo (P := H) CR (.direct N X Y t) 0 0)
      (hintArenaStart D.heap D.stride 0)).transcript
    rw [hArena]
    have h := hintNodeArena_input_before (hintArenaStart D.heap D.stride 0)
      W M 1 sch.m sch.ℓ N (S.data N t).R (S.data N t).W (crSourceSteps S N t)
      (hWidth ▸ hW) 0 (Nat.zero_le _)
    simpa only [Nat.zero_mul, Nat.zero_add] using h
  have hSep : wordsOf E.W M ≤ A.transcript := by
    rw [hWidth]
    change wordsOf W M ≤ (hintArenaFor S H W (hintNodeInfo (P := H) CR (.direct N X Y t) 0 0)
      (hintArenaStart D.heap D.stride 0)).transcript
    rw [hArena]
    dsimp only [hintNodeArena]
    omega
  dsimp only
  intro hDesc hArg hFit hRead
  have hRun := hintDirectPhase_step (CR := CR) (hintNativeProgram S) E state sch t lr x
    0 0 A.transcript desc base i D.events[pos.val] (by simpa only [Nat.zero_mul] using hEvent)
    hTable (by simpa only [Nat.zero_add] using hPacked) hRead hW hWord hDesc
    (by simpa only [Nat.zero_mul, Nat.zero_add] using hInput)
    (by simpa only [Nat.zero_add] using hSep)
    (by simpa only [Nat.zero_mul, Nat.zero_add] using hMemBefore)
    hFit hArg hAt hPc
  simpa only [Nat.zero_add] using hRun

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedDirectRead_step
end -- Def_LinearSetReconciliation327_Main_HintPlacedDirectRead20261120

section -- Def_LinearSetReconciliation327_Main_HintDirectReadPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintDirectRoot_events (S : CRSourceBundle) (H : HintParams) (N X Y t W Bc header : ℕ) :
    let sch := H.scheme N X Y
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    D.events = hintDirectReads sch 0 0 ++ (List.range sch.m).map (.finishRow 0 0) ++
      hintResidualEvents (crFamily S) 0 (sch.m * sch.ℓ) sch.N t := by
  let sch := H.scheme N X Y
  let D := hintDecoderTables S H (.direct N X Y t) W Bc header
  let offset := fun node => if node = 0 then 0 else (D.placement.arena node).payload * W
  change hintTreeEvents (crFamily S) offset (.direct sch t) 0 0 0 = _
  simpa only [Nat.zero_add] using
    (hintTreeEvents_direct (CR := crFamily S) offset sch t 0 0 0)

noncomputable def hintDirectRead_phase (S : CRSourceBundle) (H : HintParams)
    (N X Y t W Bc header : ℕ) (lr : (H.scheme N X Y).LocalSeed) (x : Finset ℕ)
    (E : RAMEnv) (up previous : ℕ → ℕ) (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = W) (hHeader : 3 < header)
    (hDet : E.det = (hintDecoderTables S H (.direct N X Y t) W Bc header).det S H up previous header N)
    (hWord : 2 < 2 ^ E.W) (hW : 0 < E.W)
    (hInput : synLen (crFamily S) (.direct (H.scheme N X Y) t) ≤ 2 ^ E.W) :
    let sch := H.scheme N X Y
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    let transcript := (D.placement.arena 0).transcript
    let M := synLen (crFamily S) (.direct sch t)
    let packed := fun m : ℕ → ℕ => ∀ a < wordsOf E.W M, m a =
      packMem E.W (hintSketchVector (crFamily S) (.direct sch t) lr x) a
    transcript + sch.m * sch.ℓ ≤ 2 ^ E.W →
    wordsOf E.W M ≤ D.control + 2 → D.control + 2 < transcript →
    (∀ j : Fin D.events.length, hintEventDescriptor header D.events
      (hintEventRecord S H D.placement) j.val + 3 < 2 ^ E.W) →
    (∀ m m', CRMemFrame transcript (transcript + sch.m * sch.ℓ) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header 0 (sch.m * sch.ℓ)
      (fun m => packed m ∧ keep m)
      (fun m => packed m ∧ HintTranscriptCorrect sch lr x transcript (fun _ _ => True) m ∧ keep m) := by
  let sch := H.scheme N X Y
  let D := hintDecoderTables S H (.direct N X Y t) W Bc header
  let A := D.placement.arena 0
  let M := synLen (crFamily S) (.direct sch t)
  let packed := fun m : ℕ → ℕ => ∀ a < wordsOf E.W M, m a =
    packMem E.W (hintSketchVector (crFamily S) (.direct sch t) lr x) a
  let inv := fun i m =>
    packed m ∧ HintTranscriptCorrect sch lr x A.transcript (fun j s => j.val * sch.ℓ + s.val < i) m ∧ keep m
  dsimp only
  intro hFit hControlLow hControlHigh hDescriptors hKeep hKeepCursor
  change wordsOf E.W M ≤ D.control + 2 at hControlLow
  change D.control + 2 < A.transcript at hControlHigh
  refine ⟨fun _ => 24, inv, ?_, ?_, ?_, ?_⟩
  · intro m
    constructor
    · rintro ⟨hP, _, hK⟩
      exact ⟨hP, hK⟩
    · rintro ⟨hP, hK⟩
      exact ⟨hP, fun j s h => (Nat.not_lt_zero _ h).elim, hK⟩
  · intro m
    constructor
    · rintro ⟨hP, hT, hK⟩
      exact ⟨hP, hintDirectPhase_end sch lr x _ m hT, hK⟩
    · rintro ⟨hP, hT, hK⟩
      exact ⟨hP, fun j s _ => hT j s trivial, hK⟩
  · intro i m v hm
    rcases hm with ⟨hP, hT, hK⟩
    refine ⟨?_, ?_, hKeepCursor m v hK⟩
    · intro a ha
      rw [Function.update_of_ne (by omega : a ≠ D.control + 2)]
      exact hP a ha
    · intro j s hs
      have hAddr : hintTranscriptCell A.transcript sch.m j.val s.val ≠ D.control + 2 := by
        unfold hintTranscriptCell
        omega
      rw [Function.update_of_ne hAddr]
      exact hT j s hs
  · intro i hi j hj act base state
    dsimp only
    intro hSelect _ hAt hPc hArg hCtx _ hInv _
    have hPos : j.val = i := by omega
    let p : Fin (sch.m * sch.ℓ) := ⟨i, hi⟩
    obtain ⟨row, col, hRC⟩ := hintDirectReads_split p
    have hIn : i < (hintDirectReads sch 0 0).length := by
      rw [hintDirectReads_length]
      exact hi
    have hEv : D.events[j.val]? = some (.directBit 0 row.val col.val (row.val * sch.ℓ + col.val)) := by
      rw [hPos, hintDirectRoot_events S H N X Y t W Bc header, List.append_assoc,
        List.getElem?_append_left hIn]
      change p.val = _ at hRC
      rw [show i = row.val * sch.ℓ + col.val from hRC]
      simpa only [Nat.zero_add] using hintDirectReads_at sch 0 0 row col
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) j.isLt).symm.trans hEv)
    have hTag : D.events[j.val].tag = 0 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintUnpackAction := (Option.some.inj hSelect).symm
    subst act
    obtain ⟨hP, hT, hK⟩ := hInv
    have hArg' : state.regs 6 = hintEventDescriptor header D.events (hintEventRecord S H D.placement) p.val := by
      simpa only [p, hPos] using hArg
    have hStep := hintPlacedDirectRead_step S H N X Y t W Bc header lr x E state up previous base p
      hWidth hHeader hDet hWord hW hInput hP hAt hPc
      (by simpa only [p, hPos] using hDescriptors j) hArg' hFit hT
    change Sem (hintNativeProgram S) E base (base + 22) state _
    apply Sem.mono hStep
    rintro k out ⟨hk, hc, hP', hT', hf⟩
    refine ⟨hk, ⟨hP', hT', hKeep _ _ hf hK⟩, hc.trans hCtx, ?_⟩
    intro a _ ha
    exact hf a (Or.inl (ha.trans_lt hControlHigh))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectRead_phase
end -- Def_LinearSetReconciliation327_Main_HintDirectReadPhase20261120

section -- Def_LinearSetReconciliation327_Main_HintRecursiveSchedule20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintRecursiveColumnEvents (CR : CRFamily) (payloadOffset : ℕ → ℕ)
    (sch : RowScheme) (children : Fin sch.ℓ → Node) (node seed offset : ℕ) (s : Fin sch.ℓ) :
    List HintTreeEvent :=
  let childNode := hintChildPhysicalIndex children node s
  let childSeed := hintChildSchemeIndex children seed s
  let childOff := offset + ((List.ofFn fun i => synLen CR (children i)).take s.val).sum
  (List.range sch.m).map (.predict node seed s.val) ++
    [.childCopy node s.val childNode childOff (synLen CR (children s))] ++
    (List.range sch.m).map (.childToggle node s.val childNode childSeed) ++
    hintTreeEvents CR payloadOffset (children s) childNode childSeed (payloadOffset childNode) ++
    [.recoverColumn node s.val childNode]

theorem hintTreeEvents_recursive {CR : CRFamily} (payloadOffset : ℕ → ℕ) (sch : RowScheme)
    (t : ℕ) (Xs Ys : Fin sch.ℓ → ℕ) (children : Fin sch.ℓ → Node) (node seed offset : ℕ) :
    hintTreeEvents CR payloadOffset (.recursive sch t Xs Ys children) node seed offset =
      (List.ofFn (hintRecursiveColumnEvents CR payloadOffset sch children node seed offset)).flatten ++
        (List.range sch.m).map (.finishRow node seed) ++
        hintResidualEvents CR node (offset + ∑ s, synLen CR (children s)) sch.N t := by
  rw [hintTreeEvents]
  rfl

theorem hintRecursiveColumnEvents_at (CR : CRFamily) (payloadOffset : ℕ → ℕ)
    (sch : RowScheme) (children : Fin sch.ℓ → Node) (node seed offset : ℕ)
    (s : Fin sch.ℓ) (j : ℕ)
    (hj : j < (hintRecursiveColumnEvents CR payloadOffset sch children node seed offset s).length) :
    let columns := hintRecursiveColumnEvents CR payloadOffset sch children node seed offset
    let k := ((List.ofFn fun q => (columns q).length).take s.val).sum + j
    (List.ofFn columns).flatten[k]? = (columns s)[j]? :=
  getElem?_flatten_ofFn' sch.ℓ _ s j hj

theorem hintResidualEvents_length (CR : CRFamily) (node offset N t : ℕ) :
    (hintResidualEvents CR node offset N t).length = N + 3 := by
  simp [hintResidualEvents]

theorem hintResidualEvents_toggle (CR : CRFamily) (node offset N t q : ℕ) (hq : q < N) :
    (hintResidualEvents CR node offset N t)[1 + q]? = some (.residualToggle node q) := by
  have hq' : q < (List.range N).length := by simpa using hq
  have hMap : q < ((List.range N).map (HintTreeEvent.residualToggle node)).length := by simpa using hq
  simp only [hintResidualEvents, List.cons_append, List.nil_append, Nat.one_add,
    List.getElem?_cons_succ, List.getElem?_append_left hMap, List.getElem?_map,
    List.getElem?_eq_getElem hq', List.getElem_range, Option.map_some]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintTreeEvents_recursive
#print axioms LinearSetReconciliation327.Main.hintRecursiveColumnEvents_at
#print axioms LinearSetReconciliation327.Main.hintResidualEvents_toggle
end -- Def_LinearSetReconciliation327_Main_HintRecursiveSchedule20261120

section -- Def_LinearSetReconciliation327_Main_HintDirectRootIndex20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintResidualEvents_copy (CR : CRFamily) (node offset N t : ℕ) :
    (hintResidualEvents CR node offset N t)[0]? = some (.residualCopy node offset (CR.rows N t)) := rfl

theorem hintResidualEvents_decode (CR : CRFamily) (node offset N t : ℕ) :
    (hintResidualEvents CR node offset N t)[1 + N]? = some (.decodeResidual node N t) := by
  let body := [.residualCopy node offset (CR.rows N t)] ++ (List.range N).map (HintTreeEvent.residualToggle node)
  have hLen : body.length = 1 + N := by simp [body, Nat.add_comm]
  change (body ++ [.decodeResidual node N t, .correctEstimate node])[1 + N]? = _
  rw [List.getElem?_append_right (by omega), hLen, Nat.sub_self]
  rfl

theorem hintResidualEvents_correct (CR : CRFamily) (node offset N t : ℕ) :
    (hintResidualEvents CR node offset N t)[1 + N + 1]? = some (.correctEstimate node) := by
  let body := [.residualCopy node offset (CR.rows N t)] ++ (List.range N).map (HintTreeEvent.residualToggle node)
  have hLen : body.length = 1 + N := by simp [body, Nat.add_comm]
  change (body ++ [.decodeResidual node N t, .correctEstimate node])[1 + N + 1]? = _
  rw [List.getElem?_append_right (by omega), hLen]
  rw [show 1 + N + 1 - (1 + N) = 1 by omega]
  rfl

theorem hintDirectRoot_row (S : CRSourceBundle) (H : HintParams) (N X Y t W Bc header q : ℕ)
    (hq : q < H.rows X Y) :
    let sch := H.scheme N X Y
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    D.events[sch.m * sch.ℓ + q]? = some (.finishRow 0 0 q) := by
  let sch := H.scheme N X Y
  let D := hintDecoderTables S H (.direct N X Y t) W Bc header
  let body := (List.range sch.m).map (HintTreeEvent.finishRow 0 0)
  have hLen := hintDirectReads_length sch 0 0
  change q < sch.m at hq
  have hBody : q < body.length := by simpa [body] using hq
  have hRange : q < (List.range sch.m).length := by simpa using hq
  have hEvents := hintDirectRoot_events S H N X Y t W Bc header
  change D.events[sch.m * sch.ℓ + q]? = _
  rw [hEvents, List.append_assoc]
  change ((hintDirectReads sch 0 0) ++ (body ++ _))[sch.m * sch.ℓ + q]? = _
  rw [List.getElem?_append_right (by rw [hLen]; omega), hLen]
  have hOffset : sch.m * sch.ℓ + q - sch.m * sch.ℓ = q := by omega
  rw [hOffset, List.getElem?_append_left hBody]
  simp [body, List.getElem?_map, List.getElem?_eq_getElem hRange]

theorem hintDirectRoot_residual (S : CRSourceBundle) (H : HintParams) (N X Y t W Bc header q : ℕ) :
    let sch := H.scheme N X Y
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    D.events[sch.m * sch.ℓ + sch.m + q]? =
      (hintResidualEvents (crFamily S) 0 (sch.m * sch.ℓ) sch.N t)[q]? := by
  let sch := H.scheme N X Y
  let D := hintDecoderTables S H (.direct N X Y t) W Bc header
  let body := hintDirectReads sch 0 0 ++ (List.range sch.m).map (HintTreeEvent.finishRow 0 0)
  have hLen : body.length = sch.m * sch.ℓ + sch.m := by simp [body, hintDirectReads_length]
  have hEvents := hintDirectRoot_events S H N X Y t W Bc header
  change D.events[sch.m * sch.ℓ + sch.m + q]? = _
  rw [hEvents]
  change (body ++ hintResidualEvents (crFamily S) 0 (sch.m * sch.ℓ) sch.N t)[sch.m * sch.ℓ + sch.m + q]? = _
  rw [List.getElem?_append_right (by omega), hLen]
  have hOffset : sch.m * sch.ℓ + sch.m + q - (sch.m * sch.ℓ + sch.m) = q := by omega
  rw [hOffset]

theorem hintDirectRoot_count (S : CRSourceBundle) (H : HintParams) (N X Y t W Bc header : ℕ) :
    let sch := H.scheme N X Y
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    D.events.length = sch.m * sch.ℓ + sch.m + (1 + sch.N + 1 + 1) := by
  let sch := H.scheme N X Y
  let D := hintDecoderTables S H (.direct N X Y t) W Bc header
  have hEvents := hintDirectRoot_events S H N X Y t W Bc header
  change D.events.length = sch.m * sch.ℓ + sch.m + (1 + sch.N + 1 + 1)
  rw [hEvents]
  simp only [List.length_append, hintDirectReads_length, List.length_map, List.length_range,
    hintResidualEvents_length]
  change sch.m * sch.ℓ + sch.m + (sch.N + 3) = sch.m * sch.ℓ + sch.m + (1 + sch.N + 1 + 1)
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectRoot_row
#print axioms LinearSetReconciliation327.Main.hintDirectRoot_residual
#print axioms LinearSetReconciliation327.Main.hintDirectRoot_count
end -- Def_LinearSetReconciliation327_Main_HintDirectRootIndex20261120


