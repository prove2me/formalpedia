-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_10Part1
-- name    : LinearSetReconciliation327_Main_B65_10Part1
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T14:10:26.557004+00:00
-- url     : https://prove2.me/theorems/7dfd6f41-d189-569c-aacb-41f80c49555e
-- title:
--   Theorem 6.5 supporting machine proof B65_10Part1
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_10Setup
set_option autoImplicit false

section S_HintChildSpan20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintChildSlice_span (CR : CRFamily) (sch : RowScheme) (t : ℕ)
    (Xs Ys : Fin sch.ℓ → ℕ) (children : Fin sch.ℓ → Node) (s : Fin sch.ℓ) :
    ((List.ofFn fun i => synLen CR (children i)).take s.val).sum + synLen CR (children s) ≤
      synLen CR (.recursive sch t Xs Ys children) := by
  let pieces := List.ofFn (fun i => synLen CR (children i))
  have hIndex : s.val < pieces.length := by simp [pieces]
  have hTake := hintTakeSum_succ pieces s.val hIndex
  have hChild : pieces[s.val] = synLen CR (children s) := by simp [pieces]
  have hLe := hintTakeSum_mono pieces (Nat.succ_le_of_lt hIndex)
  rw [List.take_of_length_le le_rfl, hTake, hChild] at hLe
  have hLen : synLen CR (.recursive sch t Xs Ys children) = pieces.sum + CR.rows sch.N t := by
    simp only [synLen, pieces, List.sum_ofFn]
  rw [hLen]
  exact hLe.trans (Nat.le_add_right _ _)

theorem hintStageChild_pre {CR : CRFamily} (E : RAMEnv) (sch : RowScheme) (t : ℕ)
    (Xs Ys : Fin sch.ℓ → ℕ) (children : Fin sch.ℓ → Node) (s : Fin sch.ℓ)
    (word dest : ℕ)
    (hWord : 1 < 2 ^ E.W) (hWidth : 0 < E.W)
    (hInput : word * E.W + synLen CR (.recursive sch t Xs Ys children) < 2 ^ E.W)
    (hDest : dest + wordsOf E.W (synLen CR (children s)) ≤ 2 ^ E.W)
    (hSep : (word * E.W + synLen CR (.recursive sch t Xs Ys children)) / E.W < dest) :
    let off := word * E.W + ((List.ofFn fun z => synLen CR (children z)).take s.val).sum
    HintStagePre E E.W (synLen CR (children s)) off dest := by
  have hSize := hintChildSlice_span CR sch t Xs Ys children s
  have hSpan := Nat.add_le_add_left hSize (word * E.W)
  rw [← Nat.add_assoc] at hSpan
  exact ⟨hWord, hWidth, le_rfl, hSpan.trans_lt hInput, hDest,
    (Nat.div_le_div_right hSpan).trans_lt hSep⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintChildSlice_span
#print axioms LinearSetReconciliation327.Main.hintStageChild_pre
end S_HintChildSpan20261120
section S_HintChildCopyPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintChildCopy_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node childNode first word : ℕ) (sch : RowScheme) (t : ℕ)
    (Xs Ys : Fin sch.ℓ → ℕ) (children : Fin sch.ℓ → Node)
    (r : (Node.recursive sch t Xs Ys children).Seed) (x : Finset ℕ) (col : Fin sch.ℓ)
    (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hWord : 2 < 2 ^ E.W)
    (hW : 0 < E.W) :
    let L := D.placement
    let CR := crFamily S
    let child := children col
    let dest := (L.arena childNode).payload
    let offset := word * E.W + ((List.ofFn fun s => synLen CR (children s)).take col.val).sum
    let count := synLen CR child
    let words := wordsOf E.W count
    D.events[first]? = some (.childCopy node col.val childNode offset count) →
    D.control + 2 < dest →
    dest < 2 ^ E.W →
    word * E.W + synLen CR (.recursive sch t Xs Ys children) < 2 ^ E.W →
    dest + words ≤ 2 ^ E.W →
    (word * E.W + synLen CR (.recursive sch t Xs Ys children)) / E.W < dest →
    (∀ pos : Fin D.events.length, pos.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ E.W) →
    (∀ m, keep m → HintMemoryWords E.W word
      (hintSketchVector CR (.recursive sch t Xs Ys children) r x) m) →
    (∀ m m', CRMemFrame dest (dest + words) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      (fun m => HintFreshWords dest words m ∧ keep m)
      (fun m => HintMemoryWords E.W dest
        (hintSketchVector CR child (r.2 col) (sch.column r.1 x col)) m ∧ keep m) := by
  let L := D.placement
  let CR := crFamily S
  let child := children col
  let dest := (L.arena childNode).payload
  let offset := word * E.W + ((List.ofFn fun s => synLen CR (children s)).take col.val).sum
  let count := synLen CR child
  let words := wordsOf E.W count
  dsimp only
  intro hEvent hControl hAddress hInput hDest hSeparate hDescriptor hPacked hKeep hCursor
  change D.control + 2 < dest at hControl
  have hPre : HintStagePre E E.W count offset dest :=
    hintStageChild_pre E sch t Xs Ys children col word dest (Nat.lt_trans (by decide) hWord)
      hW hInput hDest hSeparate
  apply HintDecoderPhase.single (time := 17 * count + 13)
  · rintro m v ⟨hf, hk⟩
    exact ⟨hf.update_below _ _ hControl, hCursor _ _ hk⟩
  · rintro m v ⟨hp, hk⟩
    exact ⟨hp.update_below _ _ hControl, hCursor _ _ hk⟩
  · intro pos hPos act base state
    dsimp only
    intro hSelect _ hAt hPc hArg hCtx _ hInv hRecord
    have hEvent' : D.events[pos.val]? = some (.childCopy node col.val childNode offset count) := by
      rw [hPos]
      exact hEvent
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans hEvent')
    have hTag : D.events[pos.val].tag = 1 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintStageAction := (Option.some.inj hSelect).symm
    subst act
    rw [hEq] at hRecord
    obtain ⟨hFresh, hK⟩ := hInv
    let desc := hintEventDescriptor header D.events (hintEventRecord S H L) pos.val
    have hSlot : (hintUnpackDetBlock dest offset E.W count).At E desc := by
      rw [hWidth]
      exact hRecord
    have hRun := hintStageChild_exact (CR := CR) (hintNativeProgram S) E state sch t Xs Ys children
      r x col word dest desc base (hPacked _ hK) hWord (hDescriptor pos hPos) hAddress hSlot hPre hFresh hArg hAt hPc
    change Sem (hintNativeProgram S) E base (base + 28) state _
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hp, hf⟩
    exact ⟨hk, ⟨hp, hKeep _ _ hf hK⟩, hc.trans hCtx, fun a _ ha => hf a (Or.inl (ha.trans_lt hControl))⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintChildCopy_phase
end S_HintChildCopyPhase20261120
section S_HintChildTogglePhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintChildToggle_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node child seed col first X Y Bc workStart sav : ℕ)
    (T : Node) (r : T.Seed) (x selected : Finset ℕ)
    (keep : (ℕ → ℕ) → Prop)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hSelected : selected ⊆ Finset.range T.N)
    (hEvent : ∀ q < T.N, D.events[first + q]? = some (.childToggle node col child seed q))
    (hWord : 16 < 2 ^ E.W) (hSize : T.N ≤ 2 ^ E.W) :
    let L := D.placement
    let CR := crFamily S
    let gate := (L.arena node).transcript + col * H.rows X Y
    let dest := (L.arena child).payload
    let words := wordsOf E.W (synLen CR T)
    let colBase := hintSubtreeColBase Bc T
    let items := hintChildUpdateSchedule CR Bc colBase T seed sav
    let detBase := L.updateTable child
    let initial := hintSketchVector CR T r x
    D.control + 2 < gate →
    gate + T.N ≤ dest →
    dest + (sav + 2) ≤ 2 ^ E.W →
    words ≤ workStart → UpSaveRoom workStart sav T →
    detBase + 3 < 2 ^ E.W →
    E.det (detBase + 3) = D.control →
    UpSavedLayout E detBase items →
    E.det (detBase % 2 ^ E.W) % 2 ^ E.W = items.length →
    (∀ i < T.N, UpLocalTree CR (upShiftDetEnv E detBase) i Bc colBase T r seed 0 0) →
    (∀ p : Fin D.events.length, first ≤ p.val → p.val < first + T.N →
      hintEventDescriptor header D.events (hintEventRecord S H L) p.val + 3 < 2 ^ E.W) →
    (∀ m m', CRMemFrame dest (dest + sav + 2) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first T.N
      (fun m => HintBitmap m gate T.N selected ∧ HintMemoryWords E.W dest initial m ∧ keep m)
      (fun m => HintBitmap m gate T.N selected ∧
        HintMemoryWords E.W dest (hintSketchVector CR T r (symmDiff x selected)) m ∧ keep m) := by
  let L := D.placement
  let CR := crFamily S
  let gate := (L.arena node).transcript + col * H.rows X Y
  let dest := (L.arena child).payload
  let words := wordsOf E.W (synLen CR T)
  let colBase := hintSubtreeColBase Bc T
  let items := hintChildUpdateSchedule CR Bc colBase T seed sav
  let detBase := L.updateTable child
  let initial := hintSketchVector CR T r x
  let inv := fun i m => HintBitmap m gate T.N selected ∧
    HintMemoryWords E.W dest (initial + hintSketchVector CR T r (selected ∩ Finset.range i)) m ∧ keep m
  dsimp only
  intro hCtrl hBefore hPay hGap hRoom hDet hReturn hLayout hCount hLocal hDescriptor hKeep hCursor
  change D.control + 2 < gate at hCtrl
  change gate + T.N ≤ dest at hBefore
  change dest + (sav + 2) ≤ 2 ^ E.W at hPay
  change words ≤ workStart at hGap
  have hPayFit : dest < 2 ^ E.W := by omega
  have hCtrlWord : D.control < 2 ^ E.W := by omega
  have hCtrlPay : D.control + 2 < dest := by omega
  refine ⟨fun _ => 147 * items.length + 24, inv, ?_, ?_, ?_, ?_⟩
  · intro m
    have hZero := hintSketchVector_empty CR T r
    simp only [inv, Finset.range_zero, Finset.inter_empty, hZero, add_zero]
    rfl
  · intro m
    change (HintBitmap m gate T.N selected ∧
      HintMemoryWords E.W dest (initial + hintSketchVector CR T r (selected ∩ Finset.range T.N)) m ∧ keep m) ↔ _
    change _ ↔ HintBitmap m gate T.N selected ∧
      HintMemoryWords E.W dest (hintSketchVector CR T r (symmDiff x selected)) m ∧ keep m
    rw [Finset.inter_eq_left.mpr hSelected, hintSketchVector_xor]
  · rintro i m v ⟨he, hp, hk⟩
    exact ⟨he.update_below _ _ hCtrl, hp.update_below _ _ hCtrlPay, hCursor _ _ hk⟩
  · intro i hi pos hPos act base state
    dsimp only
    intro hSelect _ hAt hPc hArg _ hWState hInv hRec
    have hEvent' : D.events[pos.val]? = some (.childToggle node col child seed i) := by
      rw [hPos]
      exact hEvent i hi
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans hEvent')
    have hTag : D.events[pos.val].tag = 4 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintToggleGateAction := (Option.some.inj hSelect).symm
    subst act
    rw [hEq] at hRec
    obtain ⟨hEst, hPacked, hK⟩ := hInv
    let coord : Fin T.N := ⟨i, hi⟩
    let desc := hintEventDescriptor header D.events (hintEventRecord S H L) pos.val
    have hOrd : gate + i < 2 ^ E.W := by omega
    have hCoord : i < 2 ^ E.W := hi.trans_le hSize
    have hRecord : (hintGateBlock (gate + i) i detBase dest).At E desc := by
      simpa only [hintEventRecord, hInfoXY, Option.getD_some] using hRec
    have hTable := HintToggleGateTable.of_block E desc (gate + i) i detBase dest D.control
      hRecord (by omega) (hDescriptor pos (by omega) (by omega)) hDet hOrd hCoord hPayFit hCtrlWord hReturn
    have hRun := hintUpdate_prefix_step CR T r selected initial coord (hintNativeProgram S) E state
      seed base desc (gate + i) detBase dest D.control Bc colBase workStart sav hTable hArg hWState hAt hPc
      (hEst i hi) hPay hGap hWord hSize hPacked (hLocal i hi) hRoom hLayout hCount
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hp, hf⟩
    have frame : CRMemFrame dest (dest + sav + 2) state.mem out.mem := by
      intro a ha
      apply hf a
      intro h
      unfold UpTwoRegion at h
      have hWork : workStart ≤ sav := Nat.le_trans (Nat.le_add_right _ _) hRoom
      rcases h with h | h <;> omega
    refine ⟨hk, ⟨?_, hp, hKeep _ _ frame hK⟩, hc, ?_⟩
    · intro q hq
      rw [frame (gate + q) (Or.inl (by omega))]
      exact hEst q hq
    · intro a _ ha
      exact frame a (Or.inl (ha.trans_lt hCtrlPay))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintChildToggle_phase
end S_HintChildTogglePhase20261120
section S_HintTranscriptTrace20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintPairOffset_lt {m n : ℕ} (i : Fin m) (j : Fin n) : i.val * n + j.val < m * n := by
  have hNext := Nat.mul_le_mul_right n i.isLt
  change (i.val + 1) * n ≤ m * n at hNext
  rw [Nat.add_mul, Nat.one_mul] at hNext
  omega

theorem hintTranscriptCell_eq_iff {m n : ℕ} (base : ℕ)
    (j j' : Fin m) (s s' : Fin n) :
    hintTranscriptCell base m j.val s.val = hintTranscriptCell base m j'.val s'.val ↔ j = j' ∧ s = s' := by
  constructor
  · intro h
    unfold hintTranscriptCell at h
    have hEq : m * s.val + j.val = m * s'.val + j'.val := by
      rw [Nat.mul_comm m s.val, Nat.mul_comm m s'.val]
      omega
    have hm : 0 < m := Nat.zero_lt_of_lt j.isLt
    have hMod := congrArg (fun x => x % m) hEq
    have hDiv := congrArg (fun x => x / m) hEq
    rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt j'.isLt] at hMod
    rw [Nat.mul_add_div hm, Nat.mul_add_div hm, Nat.div_eq_of_lt j.isLt,
      Nat.div_eq_of_lt j'.isLt, Nat.add_zero, Nat.add_zero] at hDiv
    exact ⟨Fin.ext hMod, Fin.ext hDiv⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem hintDirectBit_pre {CR : CRFamily} (E : RAMEnv) (T : RowScheme)
    (t word transcript : ℕ) (j : Fin T.m) (s : Fin T.ℓ)
    (hW : 0 < E.W) (hWord : 2 < 2 ^ E.W)
    (hInputBits : word * E.W + synLen CR (.direct T t) ≤ 2 ^ E.W)
    (hInputBefore : (word * E.W + synLen CR (.direct T t)) / E.W < transcript)
    (hTranscript : transcript + T.m * T.ℓ ≤ 2 ^ E.W) :
    HintUnpackPre E (hintTranscriptCell transcript T.m j.val s.val)
      (word * E.W + j.val * T.ℓ + s.val) 1 := by
  have hWire := hintPairOffset_lt j s
  have hTranscriptCell := hintPairOffset_lt s j
  rw [Nat.mul_comm T.ℓ T.m] at hTranscriptCell
  have hLen : T.m * T.ℓ ≤ synLen CR (.direct T t) := by
    change T.m * T.ℓ ≤ T.m * T.ℓ + CR.rows T.N t
    omega
  have hOff : word * E.W + j.val * T.ℓ + s.val + 1 ≤ word * E.W + synLen CR (.direct T t) := by omega
  refine ⟨hW, by omega, by omega, ?_, hOff.trans hInputBits, ?_⟩
  · unfold hintTranscriptCell
    omega
  · exact (Nat.div_le_div_right hOff).trans_lt (hInputBefore.trans_le (by unfold hintTranscriptCell; omega))

def HintTranscriptCorrect (sch : RowScheme) (r : sch.LocalSeed) (x : Finset ℕ)
    (transcript : ℕ) (read : Fin sch.m → Fin sch.ℓ → Prop) (mem : ℕ → ℕ) : Prop :=
  ∀ (j : Fin sch.m) (s : Fin sch.ℓ), read j s →
    mem (hintTranscriptCell transcript sch.m j.val s.val) = (sch.code j (r.2 j) (sch.rowOf r x j) s).val

theorem hintTranscript_write (sch : RowScheme) (r : sch.LocalSeed) (x : Finset ℕ)
    (transcript : ℕ) (read : Fin sch.m → Fin sch.ℓ → Prop)
    (before after : ℕ → ℕ) (j : Fin sch.m) (s : Fin sch.ℓ)
    (hPrev : HintTranscriptCorrect sch r x transcript read before)
    (hNew : after (hintTranscriptCell transcript sch.m j.val s.val) =
      (sch.code j (r.2 j) (sch.rowOf r x j) s).val)
    (hFrame : CRMemFrame (hintTranscriptCell transcript sch.m j.val s.val)
      (hintTranscriptCell transcript sch.m j.val s.val + 1) before after) :
    HintTranscriptCorrect sch r x transcript (fun j' s' => read j' s' ∨ (j' = j ∧ s' = s)) after := by
  intro j' s' hRead
  by_cases hCell : hintTranscriptCell transcript sch.m j'.val s'.val =
      hintTranscriptCell transcript sch.m j.val s.val
  · obtain ⟨rfl, rfl⟩ := (hintTranscriptCell_eq_iff transcript j' j s' s).mp hCell
    exact hNew
  · have hOld : read j' s' := by
      rcases hRead with h | ⟨rfl, rfl⟩
      · exact h
      · exact (hCell rfl).elim
    rw [hFrame _ (by omega)]
    exact hPrev j' s' hOld

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectBit_pre
#print axioms LinearSetReconciliation327.Main.hintTranscript_write
end S_HintTranscriptTrace20261120
section S_HintRecoverColumnPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintTranscriptCell_beforeColumn (sch : RowScheme) (start : ℕ)
    (j : Fin sch.m) (s : Fin sch.ℓ) (col : ℕ) (hs : s.val < col) :
    hintTranscriptCell start sch.m j.val s.val < start + col * sch.m := by
  have hNext := Nat.mul_le_mul_right sch.m hs
  change (s.val + 1) * sch.m ≤ col * sch.m at hNext
  rw [Nat.add_mul, Nat.one_mul] at hNext
  have hj := j.isLt
  unfold hintTranscriptCell
  omega

theorem hintTranscript_afterColumn (sch : RowScheme) (lr : sch.LocalSeed) (x : Finset ℕ)
    (start : ℕ) (col : Fin sch.ℓ) (before after : ℕ → ℕ)
    (hBefore : HintTranscriptCorrect sch lr x start (fun _ s => s.val < col.val) before)
    (hColumn : HintBitmap after (start + col.val * sch.m) sch.m (sch.column lr x col))
    (hFrame : CRMemFrame (start + col.val * sch.m) (start + col.val * sch.m + sch.m) before after) :
    HintTranscriptCorrect sch lr x start (fun _ s => s.val < col.val + 1) after := by
  intro j s hs
  by_cases he : s = col
  · subst s
    rw [show hintTranscriptCell start sch.m j.val col.val = start + col.val * sch.m + j.val from rfl,
      hColumn j.val j.isLt, hintTruth, HintCanonicalDecode.mem_column_iff sch lr x col j]
    split
    · rename_i hp
      rw [hp]
      rfl
    · rename_i hp
      have hzero : sch.code j (lr.2 j) (sch.rowOf lr x j) col = 0 :=
        (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) _ |>.resolve_right hp
      rw [hzero]
      rfl
  · have hne : s.val ≠ col.val := fun h => he (Fin.ext h)
    have hlt : s.val < col.val := by omega
    rw [hFrame _ (Or.inl (hintTranscriptCell_beforeColumn sch start j s col.val hlt))]
    exact hBefore j s hlt

noncomputable def hintRecoverColumn_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node child first N X Y : ℕ) (lr : (H.scheme N X Y).LocalSeed)
    (x J : Finset ℕ) (col : Fin (H.scheme N X Y).ℓ) (keep : (ℕ → ℕ) → Prop)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hEvent : D.events[first]? = some (.recoverColumn node col.val child)) :
    let L := D.placement
    let sch := H.scheme N X Y
    let transcript := (L.arena node).transcript
    let dest := transcript + col.val * sch.m
    let source := (L.arena child).result
    1 < 2 ^ E.W →
    D.control + 2 < transcript →
    D.control + 2 < source →
    dest < 2 ^ E.W →
    source < 2 ^ E.W →
    sch.m < 2 ^ E.W →
    dest + sch.m ≤ 2 ^ E.W →
    source + sch.m ≤ 2 ^ E.W →
    (dest + sch.m ≤ source ∨ source + sch.m ≤ dest) →
    (∀ pos : Fin D.events.length, pos.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 2 < 2 ^ E.W) →
    (∀ m m', CRMemFrame dest (dest + sch.m) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      (fun m => HintTranscriptCorrect sch lr x transcript (fun _ s => s.val < col.val) m ∧
        HintBitmap m dest sch.m (sch.exactP lr x J col) ∧
        HintBitmap m source sch.m (sch.exactChildInput lr x J col) ∧ keep m)
      (fun m => HintTranscriptCorrect sch lr x transcript (fun _ s => s.val < col.val + 1) m ∧ keep m) := by
  let L := D.placement
  let sch := H.scheme N X Y
  let transcript := (L.arena node).transcript
  let dest := transcript + col.val * sch.m
  let source := (L.arena child).result
  dsimp only
  intro hWord hCtrl hCtrlSrc hDest hSource hSize hDestEnd hSourceEnd hSep hDescriptor hKeep hCursor
  change D.control + 2 < transcript at hCtrl
  have hCtrlDest : D.control + 2 < dest := by dsimp only [dest]; omega
  have hCursorTranscript (cols : ℕ) (m : ℕ → ℕ) (v : ℕ)
      (hm : HintTranscriptCorrect sch lr x transcript (fun _ s => s.val < cols) m) :
      HintTranscriptCorrect sch lr x transcript (fun _ s => s.val < cols) (Function.update m (D.control + 2) v) := by
    intro j s hs
    rw [Function.update_of_ne (by unfold hintTranscriptCell; omega :
      hintTranscriptCell transcript sch.m j.val s.val ≠ D.control + 2)]
    exact hm j s hs
  apply HintDecoderPhase.single (time := 11 * sch.m + 11)
  · rintro m v ⟨ht, hp, hx, hk⟩
    exact ⟨hCursorTranscript _ _ _ ht, hp.update_below _ _ hCtrlDest, hx.update_below _ _ hCtrlSrc, hCursor _ _ hk⟩
  · rintro m v ⟨ht, hk⟩
    exact ⟨hCursorTranscript _ _ _ ht, hCursor _ _ hk⟩
  · intro pos hPos act base state
    dsimp only
    intro hSelect _ hAt hPc hArg hCtx _ hInv hRecord
    have hEvent' : D.events[pos.val]? = some (.recoverColumn node col.val child) := by
      rw [hPos]
      exact hEvent
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans hEvent')
    have hTag : D.events[pos.val].tag = 5 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintColumnAddAction := (Option.some.inj hSelect).symm
    subst act
    rw [hEq] at hRecord
    obtain ⟨hT, hP, hX, hK⟩ := hInv
    let desc := hintEventDescriptor header D.events (hintEventRecord S H L) pos.val
    have hBlock : (hintColumnAddBlock dest source sch.m).At E desc := by
      simp only [hintEventRecord, hInfoXY, Option.getD_some] at hRecord
      exact hRecord
    let table := HintColumnAddTable.of_block E desc dest source sch.m hBlock hWord
      (hDescriptor pos hPos) hDest hSource hDestEnd hSourceEnd hSize
    have hRun := hintAddBitmaps_sem (hintNativeProgram S) E state desc dest source sch.m base
      (sch.exactP lr x J col) (sch.exactChildInput lr x J col) table hArg hP hX hSep hAt hPc
    change Sem (hintNativeProgram S) E base (base + 20) state _
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hb, hf⟩
    rw [hintColumnRecovered] at hb
    exact ⟨hk, ⟨hintTranscript_afterColumn sch lr x transcript col state.mem out.mem hT hb hf, hKeep _ _ hf hK⟩,
      hc.trans hCtx, fun a _ ha => hf a (Or.inl (ha.trans_lt hCtrlDest))⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRecoverColumn_phase
end S_HintRecoverColumnPhase20261120
section S_HintResidualPrefixPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintResidualCopy_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first t offset : ℕ) (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hWord : 2 < 2 ^ E.W)
    (hx : x ⊆ Finset.range sch.N)
    (hEvent : D.events[first]? = some (.residualCopy node offset (S.data sch.N t).R)) :
    let L := D.placement
    let A := L.arena node
    let count := (S.data sch.N t).R
    let words := wordsOf E.W count
    let est := sch.exactEstimate lr x J
    D.control + 2 < A.result →
    A.result + sch.N ≤ A.residual →
    A.residual < 2 ^ E.W →
    HintStagePre E E.W count offset A.residual →
    (∀ pos : Fin D.events.length, pos.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ E.W) →
    (∀ m, keep m → ∀ q : Fin count, bitAt m E.W 0 (offset + q.val) =
      hintTruth (q.val ∈ (crFamily S).sketch sch.N t x)) →
    (∀ m m', CRMemFrame A.residual (A.residual + words) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      (fun m => HintBitmap m A.result sch.N est ∧ HintFreshWords A.residual words m ∧ keep m)
      (fun m => HintBitmap m A.result sch.N est ∧
        HintMemoryWords E.W A.residual (hintSketchVector (crFamily S) (.cr sch.N t) () x) m ∧ keep m) := by
  let L := D.placement
  let A := L.arena node
  let count := (S.data sch.N t).R
  let words := wordsOf E.W count
  let est := sch.exactEstimate lr x J
  dsimp only
  intro hControl hSeparate hAddress hPre hDescriptor hRead hKeep hCursor
  change D.control + 2 < A.result at hControl
  change A.result + sch.N ≤ A.residual at hSeparate
  have hCtrl : D.control + 2 < A.residual := by omega
  apply HintDecoderPhase.single (time := 17 * count + 13)
  · rintro m v ⟨he, hf, hk⟩
    exact ⟨he.update_below _ _ hControl, hf.update_below _ _ hCtrl, hCursor _ _ hk⟩
  · rintro m v ⟨he, hp, hk⟩
    exact ⟨he.update_below _ _ hControl, hp.update_below _ _ hCtrl, hCursor _ _ hk⟩
  · intro pos hPos act base state
    dsimp only
    intro hSelect _ hAt hPc hArg hCtx _ hInv hRecord
    have hEvent' : D.events[pos.val]? = some (.residualCopy node offset count) := by
      rw [hPos]
      exact hEvent
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans hEvent')
    have hTag : D.events[pos.val].tag = 1 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintStageAction := (Option.some.inj hSelect).symm
    subst act
    rw [hEq] at hRecord
    obtain ⟨hEst, hFresh, hK⟩ := hInv
    let desc := hintEventDescriptor header D.events (hintEventRecord S H L) pos.val
    have hSlot : (hintUnpackDetBlock A.residual offset E.W count).At E desc := by
      rw [hWidth]
      exact hRecord
    have hRun := hintCRStage_exact S (hintNativeProgram S) E state sch.N t desc A.residual offset base
      x hx hWord (hDescriptor pos hPos) hAddress hSlot hPre (hRead _ hK) hFresh hArg hAt hPc
    change Sem (hintNativeProgram S) E base (base + 28) state _
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hp, hf⟩
    have hFrame : CRMemFrame A.residual (A.residual + words) state.mem out.mem := hf
    refine ⟨hk, ⟨?_, ?_, hKeep _ _ hFrame hK⟩, hc.trans hCtx, ?_⟩
    · intro q hq
      rw [hFrame (A.result + q) (Or.inl (by omega))]
      exact hEst q hq
    · intro q hq
      rw [hintCRSketchVector_native S sch.N t () x hx]
      exact hp q hq
    · intro a _ ha
      exact hFrame a (Or.inl (ha.trans_lt hCtrl))

noncomputable def hintResidualToggle_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first t Bc : ℕ) (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hControl : D.placement.control = D.control)
    (hEvent : ∀ q < sch.N, D.events[first + q]? = some (.residualToggle node q))
    (hWord : 16 < 2 ^ E.W) (hSize : sch.N ≤ 2 ^ E.W) :
    let L := D.placement
    let A := L.arena node
    let CR := crFamily S
    let leaf := Node.cr sch.N t
    let words := wordsOf E.W (synLen CR leaf)
    let colBase := hintSubtreeColBase Bc leaf
    let items := hintChildUpdateSchedule CR Bc colBase leaf 0 words
    let detBase := L.residualTable node
    let est := sch.exactEstimate lr x J
    let initial := hintSketchVector CR leaf () x
    D.control + 2 < A.result →
    A.result + sch.N ≤ A.residual →
    A.residual + (words + 2) ≤ 2 ^ E.W →
    detBase + 3 < 2 ^ E.W →
    E.det (detBase + 3) = D.control →
    UpSavedLayout E detBase items →
    E.det (detBase % 2 ^ E.W) % 2 ^ E.W = items.length →
    (∀ i < sch.N, UpLocalTree CR (upShiftDetEnv E detBase) i Bc colBase leaf () 0 0 0) →
    (∀ p : Fin D.events.length, first ≤ p.val → p.val < first + sch.N →
      hintEventDescriptor header D.events (hintEventRecord S H L) p.val + 3 < 2 ^ E.W) →
    (∀ m m', CRMemFrame A.residual (A.residual + words + 2) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first sch.N
      (fun m => HintBitmap m A.result sch.N est ∧ HintMemoryWords E.W A.residual initial m ∧ keep m)
      (fun m => HintBitmap m A.result sch.N est ∧
        HintMemoryWords E.W A.residual (hintResidualSyndrome S sch.N t x est) m ∧ keep m) := by
  let L := D.placement
  let A := L.arena node
  let CR := crFamily S
  let leaf := Node.cr sch.N t
  let words := wordsOf E.W (synLen CR leaf)
  let colBase := hintSubtreeColBase Bc leaf
  let items := hintChildUpdateSchedule CR Bc colBase leaf 0 words
  let detBase := L.residualTable node
  let est := sch.exactEstimate lr x J
  let initial := hintSketchVector CR leaf () x
  let inv := fun i m => HintBitmap m A.result sch.N est ∧
    HintMemoryWords E.W A.residual (initial + hintSketchVector CR leaf () (est ∩ Finset.range i)) m ∧ keep m
  dsimp only
  intro hCtrl hBefore hPay hDet hReturn hLayout hCount hLocal hDescriptor hKeep hCursor
  change D.control + 2 < A.result at hCtrl
  change A.result + sch.N ≤ A.residual at hBefore
  change A.residual + (words + 2) ≤ 2 ^ E.W at hPay
  have hPayFit : A.residual < 2 ^ E.W := by omega
  have hCtrlWord : D.control < 2 ^ E.W := by omega
  have hCtrlPay : D.control + 2 < A.residual := by omega
  refine ⟨fun _ => 147 * items.length + 24, inv, ?_, ?_, ?_, ?_⟩
  · intro m
    have hZero := hintSketchVector_empty CR leaf (() : leaf.Seed)
    simp only [inv, Finset.range_zero, Finset.inter_empty, hZero, add_zero]
    rfl
  · intro m
    change (HintBitmap m A.result sch.N est ∧
      HintMemoryWords E.W A.residual (initial + hintSketchVector CR leaf () (est ∩ Finset.range sch.N)) m ∧ keep m) ↔ _
    rw [Finset.inter_eq_left.mpr (hintExactEstimate_subset sch lr x J)]
    rfl
  · rintro i m v ⟨he, hp, hk⟩
    exact ⟨he.update_below _ _ hCtrl, hp.update_below _ _ hCtrlPay, hCursor _ _ hk⟩
  · intro i hi pos hPos act base state
    dsimp only
    intro hSelect _ hAt hPc hArg _ hWState hInv hRec
    have hEvent' : D.events[pos.val]? = some (.residualToggle node i) := by
      rw [hPos]
      exact hEvent i hi
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans hEvent')
    have hTag : D.events[pos.val].tag = 4 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintToggleGateAction := (Option.some.inj hSelect).symm
    subst act
    rw [hEq] at hRec
    obtain ⟨hEst, hPacked, hK⟩ := hInv
    let coord : Fin leaf.N := ⟨i, hi⟩
    let desc := hintEventDescriptor header D.events (hintEventRecord S H L) pos.val
    have hOrd : A.result + i < 2 ^ E.W := by omega
    have hCoord : i < 2 ^ E.W := hi.trans_le hSize
    have hTable := HintToggleGateTable.of_block E desc (A.result + i) i detBase A.residual D.control
      hRec (by omega) (hDescriptor pos (by omega) (by omega)) hDet hOrd hCoord hPayFit hCtrlWord hReturn
    have hRoom : UpSaveRoom words words leaf := by
      change words + 2 * 0 ≤ words
      simp
    have hRun := hintUpdate_prefix_step CR leaf () est initial coord (hintNativeProgram S) E state
      0 base desc (A.result + i) detBase A.residual D.control Bc colBase words words hTable hArg hWState hAt hPc
      (hEst i hi) hPay le_rfl hWord hSize hPacked (hLocal i hi) hRoom hLayout hCount
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hp, hf⟩
    have frame : CRMemFrame A.residual (A.residual + words + 2) state.mem out.mem := by
      intro a ha
      apply hf a
      intro h
      unfold UpTwoRegion at h
      rcases h with h | h <;> omega
    refine ⟨hk, ⟨?_, hp, hKeep _ _ frame hK⟩, hc, ?_⟩
    · intro q hq
      rw [frame (A.result + q) (Or.inl (by omega))]
      exact hEst q hq
    · intro a _ ha
      exact frame a (Or.inl (ha.trans_lt hCtrlPay))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintResidualCopy_phase
#print axioms LinearSetReconciliation327.Main.hintResidualToggle_phase
end S_HintResidualPrefixPhase20261120


