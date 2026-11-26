-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_12
-- name    : LinearSetReconciliation327_Main_B65_12
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T14:37:56.698723+00:00
-- url     : https://prove2.me/theorems/46b83c55-a49a-5ea2-a7f6-002d473c8e00
-- title:
--   Theorem 6.5 supporting machine proof B65_12
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_12Part1
set_option autoImplicit false

section S_HintPrepareChildPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintPrepareChild_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node seed first word N X Y t Bc : ℕ)
    (Xs Ys : Fin (H.scheme N X Y).ℓ → ℕ) (children : Fin (H.scheme N X Y).ℓ → Node)
    (r : (Node.recursive (H.scheme N X Y) t Xs Ys children).Seed)
    (x J : Finset ℕ) (col : Fin (H.scheme N X Y).ℓ)
    (payloadOffset : ℕ → ℕ) (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hW : 0 < E.W) (hWord : 16 < 2 ^ E.W)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hChildSize : (children col).N = (H.scheme N X Y).m)
    (hSlice : HintEventSlice D first (hintRecursiveColumnEvents (crFamily S) payloadOffset
      (H.scheme N X Y) children node seed (word * E.W) col)) :
    let sch := H.scheme N X Y
    let CR := crFamily S
    let L := D.placement
    let child := children col
    let childNode := hintChildPhysicalIndex children node col
    let childSeed := hintChildSchemeIndex children seed col
    let B := L.arena childNode
    let dest := B.payload
    let gate := (L.arena node).transcript + col.val * sch.m
    let words := wordsOf E.W (synLen CR child)
    let table := L.updateTable childNode
    let colBase := hintSubtreeColBase Bc child
    let items := hintChildUpdateSchedule CR Bc colBase child childSeed B.saveOffset
    let selected := sch.exactP r.1 x J col
    let predicts := fun m => HintBitmap m gate sch.m selected
    let fresh := HintFreshWords dest words
    let input := HintMemoryWords E.W dest (hintSketchVector CR child (r.2 col) (sch.exactChildInput r.1 x J col))
    D.control + 2 < gate →
    gate + sch.m ≤ dest →
    dest + (B.saveOffset + 2) ≤ 2 ^ E.W →
    words ≤ B.workStart →
    UpSaveRoom B.workStart B.saveOffset child →
    word * E.W + synLen CR (.recursive sch t Xs Ys children) < 2 ^ E.W →
    (word * E.W + synLen CR (.recursive sch t Xs Ys children)) / E.W < dest →
    table + 3 < 2 ^ E.W →
    E.det (table + 3) = D.control →
    UpSavedLayout E table items →
    E.det (table % 2 ^ E.W) % 2 ^ E.W = items.length →
    (∀ i < child.N, UpLocalTree CR (upShiftDetEnv E table) i Bc colBase child (r.2 col) childSeed 0 0) →
    (∀ pos : Fin D.events.length, first + sch.m ≤ pos.val → pos.val < first + sch.m + 1 + sch.m →
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ E.W) →
    (∀ m, keep m → HintMemoryWords E.W word (hintSketchVector CR (.recursive sch t Xs Ys children) r x) m) →
    (∀ m m', CRMemFrame dest (dest + B.saveOffset + 2) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header (first + sch.m) (1 + sch.m)
      (fun m => predicts m ∧ fresh m ∧ keep m) (fun m => predicts m ∧ input m ∧ keep m) := by
  let sch := H.scheme N X Y
  let CR := crFamily S
  let L := D.placement
  let child := children col
  let childNode := hintChildPhysicalIndex children node col
  let childSeed := hintChildSchemeIndex children seed col
  let B := L.arena childNode
  let dest := B.payload
  let gate := (L.arena node).transcript + col.val * sch.m
  let words := wordsOf E.W (synLen CR child)
  let table := L.updateTable childNode
  let colBase := hintSubtreeColBase Bc child
  let items := hintChildUpdateSchedule CR Bc colBase child childSeed B.saveOffset
  let selected := sch.exactP r.1 x J col
  let predicts := fun m => HintBitmap m gate sch.m selected
  let fresh := HintFreshWords dest words
  let raw := HintMemoryWords E.W dest (hintSketchVector CR child (r.2 col) (sch.column r.1 x col))
  let input := HintMemoryWords E.W dest (hintSketchVector CR child (r.2 col) (sch.exactChildInput r.1 x J col))
  dsimp only
  intro hCtrl hGateEnd hDestEnd hGap hRoom hInputFit hInputSep hTable hReturn hLayout hCount hLocal hDesc hPacked hKeep hCursor
  change D.control + 2 < gate at hCtrl
  change gate + sch.m ≤ dest at hGateEnd
  change dest + (B.saveOffset + 2) ≤ 2 ^ E.W at hDestEnd
  change words ≤ B.workStart at hGap
  change (∀ p : Fin D.events.length, first + sch.m ≤ p.val →
    p.val < first + sch.m + 1 + sch.m →
    hintEventDescriptor header D.events (hintEventRecord S H L) p.val + 3 < 2 ^ E.W) at hDesc
  change (∀ m m', CRMemFrame dest (dest + B.saveOffset + 2) m m' → keep m → keep m') at hKeep
  change child.N = sch.m at hChildSize
  have hWord2 : 2 < 2 ^ E.W := by omega
  have hDest : dest < 2 ^ E.W := by omega
  have hDestCtrl : D.control + 2 < dest := by omega
  have hSizeFit : child.N ≤ 2 ^ E.W := by omega
  have hWork : B.workStart ≤ B.saveOffset := (Nat.le_add_right _ _).trans hRoom
  have hWordsEnd : dest + words ≤ 2 ^ E.W := by omega
  obtain ⟨_, hCopy, hToggle, _, _⟩ := hintRecursiveColumn_slice CR D payloadOffset sch children node seed
    (word * E.W) first col hSlice
  have hCopyPos : D.events[first + sch.m]? = some (.childCopy node col.val childNode
      (word * E.W + ((List.ofFn fun i => synLen CR (children i)).take col.val).sum) (synLen CR child)) := hCopy
  have hTogglePos (q : ℕ) (hq : q < child.N) :
      D.events[first + sch.m + 1 + q]? = some (.childToggle node col.val childNode childSeed q) :=
    hToggle q (hChildSize ▸ hq)
  let copy := hintChildCopy_phase S H D E header node childNode (first + sch.m) word sch t Xs Ys children r x col
    (fun m => predicts m ∧ keep m) hWidth hWord2 hW hCopyPos hDestCtrl hDest hInputFit hWordsEnd hInputSep
    (by
      intro pos hp
      change pos.val = first + sch.m at hp
      exact hDesc pos hp.ge (by omega)) (fun m hk => hPacked m hk.2)
    (by
      intro m m' hf hk
      have frame : CRMemFrame dest (dest + words) m m' := hf
      refine ⟨hk.1.frame (fun q hq => frame _ (Or.inl (by omega))), hKeep m m' ?_ hk.2⟩
      intro a ha
      rcases ha with h | h
      · exact frame a (Or.inl h)
      · exact frame a (Or.inr (by omega)))
    (fun m v hk => ⟨hk.1.update_below _ _ hCtrl, hCursor m v hk.2⟩)
  have hSelected : selected ⊆ Finset.range child.N := by
    rw [hChildSize]
    exact HintCanonicalDecode.rowsWhere_subset_range sch _
  have updated := hintChildToggle_phase S H D E header node childNode childSeed col.val (first + sch.m + 1)
    X Y Bc B.workStart B.saveOffset child (r.2 col) (sch.column r.1 x col) selected keep
    hInfoXY hSelected hTogglePos hWord hSizeFit
    hCtrl (by change gate + child.N ≤ dest; rwa [hChildSize]) hDestEnd hGap hRoom
    hTable hReturn hLayout hCount hLocal
    (by
      intro pos hp hb
      change first + sch.m + 1 ≤ pos.val at hp
      change pos.val < first + sch.m + 1 + child.N at hb
      exact hDesc pos (by omega) (by omega))
    hKeep hCursor
  have hCountEq : 1 + sch.m = 1 + child.N := congrArg (fun a => 1 + a) hChildSize.symm
  change HintDecoderPhase S H D E header (first + sch.m) (1 + sch.m)
    (fun m => predicts m ∧ fresh m ∧ keep m) (fun m => predicts m ∧ input m ∧ keep m)
  rw [hCountEq]
  exact (copy.relabel
    (fun m => show (fresh m ∧ predicts m ∧ keep m) ↔ (predicts m ∧ fresh m ∧ keep m) by tauto)
    (fun m => show (raw m ∧ predicts m ∧ keep m) ↔
      (HintBitmap m gate child.N selected ∧ raw m ∧ keep m) by rw [hChildSize]; unfold predicts; tauto)).append
    (updated.relabel (fun _ => Iff.rfl)
      (fun m => show (HintBitmap m gate child.N selected ∧ input m ∧ keep m) ↔
        (predicts m ∧ input m ∧ keep m) by rw [hChildSize]))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPrepareChild_phase
end S_HintPrepareChildPhase20261120
section S_HintRecursiveColumnPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintRecursiveColumn_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node seed first N X Y t Bc : ℕ)
    (Xs Ys : Fin (H.scheme N X Y).ℓ → ℕ) (children : Fin (H.scheme N X Y).ℓ → Node)
    (r : (Node.recursive (H.scheme N X Y) t Xs Ys children).Seed)
    (x J : Finset ℕ) (col : Fin (H.scheme N X Y).ℓ)
    (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hW : 0 < E.W) (hWord : 30 < 2 ^ E.W)
    (hControl : D.placement.control = D.control)
    (hInfoN : (D.placement.info node).universeSize = N)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hChild : (D.placement.info node).children[col.val]? =
      some (hintChildPhysicalIndex children node col))
    (hm : H.rows X Y ≤ N)
    (hSize : (children col).N = (H.scheme N X Y).m)
    (hSteps : 0 < H.ell N X Y)
    (hSeedFit : seed < 2 ^ E.W) (hKFit : H.Nmax N X Y < 2 ^ E.W)
    (hStepsFit : H.ell N X Y < 2 ^ E.W) (hBXFit : H.BX N X Y < 2 ^ E.W)
    (hBYFit : H.BY N X Y + 1 < 2 ^ E.W)
    (hCoeffSpace : H.rows X Y * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ E.W)
    (hCoeff : ∀ (j : Fin (H.rows X Y)) (q : Fin (H.Nmax N X Y)) (s : Fin (H.ell N X Y)),
      E.coeff seed (j.val * H.ell N X Y * H.Nmax N X Y + q.val + s.val * H.Nmax N X Y) =
        (r.1.2 j s q).val)
    (hPerm : ∀ i : Fin N, E.permInv seed i.val = (r.1.1.symm i).val) :
    let sch := H.scheme N X Y
    let CR := crFamily S
    let L := D.placement
    let A := L.arena node
    let child := children col
    let cn := hintChildPhysicalIndex children node col
    let cs := hintChildSchemeIndex children seed col
    let B := L.arena cn
    let lo := hintArenaStart D.heap D.stride cn
    let hi := hintArenaStart D.heap D.stride (cn + child.nodeCount)
    let word := L.inputWord node
    let offsets := fun i => L.inputWord i * E.W
    let gate := A.transcript + col.val * sch.m
    let words := wordsOf E.W (synLen CR child)
    let scratchEnd := hintPredictScratchEnd H L.rowScratch N X Y col.val
    let table := L.updateTable cn
    let colBase := hintSubtreeColBase Bc child
    let items := hintChildUpdateSchedule CR Bc colBase child cs B.saveOffset
    let events := hintRecursiveColumnEvents CR offsets sch children node seed (word * E.W) col
    let run := hintTreeEvents CR offsets child cn cs (offsets cn)
    let packed := HintMemoryWords E.W word (hintSketchVector CR (.recursive sch t Xs Ys children) r x)
    let parentHints := fun m => HintBitmap m A.hints sch.N J
    let transcript := HintTranscriptCorrect sch r.1 x A.transcript (fun _ s => s.val < col.val)
    let next := HintTranscriptCorrect sch r.1 x A.transcript (fun _ s => s.val < col.val + 1)
    let ready := fun m => parentHints m ∧ transcript m ∧ keep m
    let childFresh := HintFreshWords B.payload words
    let tail := HintNodeFreshTail D cn child.nodeCount
    HintEventSlice D first events →
    D.control + 2 < L.rowScratch →
    L.rowScratch ≤ D.listBase →
    D.listBase ≤ A.transcript →
    scratchEnd ≤ D.listBase →
    A.transcript + sch.ℓ * sch.m ≤ A.hints →
    A.hints + N ≤ B.payload →
    B.payload = lo → L.inputWord cn = B.payload →
    B.payload + B.saveOffset + 2 ≤ B.hints →
    B.hints + sch.m ≤ B.result →
    B.result + sch.m ≤ hi → hi < 2 ^ E.W →
    words ≤ B.workStart → UpSaveRoom B.workStart B.saveOffset child →
    word * E.W + synLen CR (.recursive sch t Xs Ys children) < 2 ^ E.W →
    (word * E.W + synLen CR (.recursive sch t Xs Ys children)) / E.W < B.payload →
    table + 3 < 2 ^ E.W → E.det (table + 3) = D.control →
    UpSavedLayout E table items → E.det (table % 2 ^ E.W) % 2 ^ E.W = items.length →
    (∀ i < child.N, UpLocalTree CR (upShiftDetEnv E table) i Bc colBase child (r.2 col) cs 0 0) →
    (∀ j : Fin (H.rows X Y),
      let threshold := L.threshold node j.val
      let block := hintWaitDetBlock (H.Nmax N X Y) (rowLen N (H.rows X Y) j.val)
        (H.BY N X Y) (H.ell N X Y) (H.c N X Y)
      block.At E threshold ∧ threshold + block.length ≤ 2 ^ E.W) →
    (∀ p : Fin D.events.length, hintEventDescriptor header D.events (hintEventRecord S H L) p.val +
      (D.events[p.val]).recordLength < 2 ^ E.W) →
    (∀ m, keep m → packed m) →
    (∀ m m', (∀ a, (a < L.rowScratch ∨ D.listBase ≤ a) →
      (a < gate ∨ gate + sch.m ≤ a) → (a < lo ∨ hi ≤ a) → m' a = m a) → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintSubtreePhase S H D E header cn cs (first + sch.m + 1 + sch.m) child (r.2 col)
      (sch.exactChildInput r.1 x J col) (sch.exactHint r.1 x J col) →
    HintDecoderPhase S H D E header first events.length
      (fun m => ready m ∧ childFresh m ∧ tail m)
      (fun m => parentHints m ∧ next m ∧ keep m) := by
  let sch := H.scheme N X Y
  let CR := crFamily S
  let L := D.placement
  let A := L.arena node
  let child := children col
  let cn := hintChildPhysicalIndex children node col
  let cs := hintChildSchemeIndex children seed col
  let B := L.arena cn
  let lo := hintArenaStart D.heap D.stride cn
  let hi := hintArenaStart D.heap D.stride (cn + child.nodeCount)
  let word := L.inputWord node
  let offsets := fun i => L.inputWord i * E.W
  let gate := A.transcript + col.val * sch.m
  let words := wordsOf E.W (synLen CR child)
  let scratchEnd := hintPredictScratchEnd H L.rowScratch N X Y col.val
  let events := hintRecursiveColumnEvents CR offsets sch children node seed (word * E.W) col
  let run := hintTreeEvents CR offsets child cn cs (offsets cn)
  let parentHints := fun m => HintBitmap m A.hints sch.N J
  let transcript := HintTranscriptCorrect sch r.1 x A.transcript (fun _ s => s.val < col.val)
  let next := HintTranscriptCorrect sch r.1 x A.transcript (fun _ s => s.val < col.val + 1)
  let ready := fun m => parentHints m ∧ transcript m ∧ keep m
  let childFresh := HintFreshWords B.payload words
  let tail := HintNodeFreshTail D cn child.nodeCount
  let pred := fun m => HintBitmap m gate sch.m (sch.exactP r.1 x J col)
  let abstain := fun m => HintBitmap m B.hints sch.m (sch.exactHint r.1 x J col)
  let input := sch.exactChildInput r.1 x J col
  let childWords := HintMemoryWords E.W B.payload (hintSketchVector CR child (r.2 col) input)
  let result := fun m => HintBitmap m B.result sch.m input
  dsimp only
  intro hSlice hCtrl hScratch hTran hWork hTranEnd hParent hPayload hChildInput hChildWork hHints hResult hEnd
  intro hRoom1 hRoom2 hInputFit hInputSep hTable hReturn hLayout hCount hLocal hThreshold hDesc hPacked hKeep hCursor call
  change D.control + 2 < L.rowScratch at hCtrl
  change L.rowScratch ≤ D.listBase at hScratch
  change D.listBase ≤ A.transcript at hTran
  change scratchEnd ≤ D.listBase at hWork
  change A.transcript + sch.ℓ * sch.m ≤ A.hints at hTranEnd
  change A.hints + sch.N ≤ B.payload at hParent
  change B.payload = lo at hPayload
  change L.inputWord cn = B.payload at hChildInput
  change B.payload + B.saveOffset + 2 ≤ B.hints at hChildWork
  change B.hints + sch.m ≤ B.result at hHints
  change B.result + sch.m ≤ hi at hResult
  change hi < 2 ^ E.W at hEnd
  change words ≤ B.workStart at hRoom1
  change UpSaveRoom B.workStart B.saveOffset child at hRoom2
  change child.N = sch.m at hSize
  change ∀ m m', (∀ a, (a < L.rowScratch ∨ D.listBase ≤ a) →
    (a < gate ∨ gate + sch.m ≤ a) → (a < lo ∨ hi ≤ a) → m' a = m a) → keep m → keep m' at hKeep
  have hControlTran : D.control + 2 < A.transcript := by omega
  have hColumn : col.val * sch.m + sch.m ≤ sch.ℓ * sch.m := by
    have h := Nat.mul_le_mul_right sch.m col.isLt
    rwa [Nat.succ_mul] at h
  have hGate : A.transcript ≤ gate := by dsimp only [gate]; omega
  have hGateEnd : gate + sch.m ≤ A.hints := by dsimp only [gate]; omega
  have hRoom : B.workStart ≤ B.saveOffset := (Nat.le_add_right _ _).trans hRoom2
  have hChildFreshEnd : B.payload + words ≤ B.hints := by omega
  have hGCtrl : D.control + 2 < gate := hControlTran.trans_le hGate
  have hPCtrl : D.control + 2 < A.hints := by omega
  have hBCtrl : D.control + 2 < B.payload := by omega
  have hHCtrl : D.control + 2 < B.hints := by omega
  have hRCtrl : D.control + 2 < B.result := by omega
  have hScratchFit : scratchEnd < 2 ^ E.W := by omega
  have hScratchTran : scratchEnd ≤ A.transcript := by omega
  have hParentBeforeHints : A.hints + N ≤ B.hints := by change A.hints + sch.N ≤ B.hints; omega
  have hChildHintFit : B.hints + sch.m ≤ 2 ^ E.W := by omega
  obtain ⟨hPredict, _, _, _, hRecover⟩ := hintRecursiveColumn_slice CR D offsets sch children node seed
    (word * E.W) first col hSlice
  have hDescriptor {pos : Fin D.events.length} {e : HintTreeEvent}
      (he : D.events[pos.val]? = some e) (len : ℕ) (hlen : len ≤ e.recordLength) :
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + len < 2 ^ E.W := by
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans he)
    have hb : len ≤ D.events[pos.val].recordLength := by rw [hEq]; exact hlen
    exact (Nat.add_le_add_left hb _).trans_lt (hDesc pos)
  have hPredictDesc (pos : Fin D.events.length) (hLo : first ≤ pos.val) (hHi : pos.val < first + sch.m) :
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 31 ≤ 2 ^ E.W := by
    have he : D.events[pos.val]? = some (.predict node seed col.val (pos.val - first)) := by
      nth_rw 1 [show pos.val = first + (pos.val - first) by omega]
      exact hPredict _ (by omega)
    exact (hDescriptor he 31 (by simp [HintTreeEvent.recordLength])).le
  have hPrepareDesc (pos : Fin D.events.length) :
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ E.W := by
    apply lt_of_le_of_lt (Nat.add_le_add_left ?_ _) (hDesc pos)
    cases D.events[pos.val] <;> simp [HintTreeEvent.recordLength]
  have hCursorTranscript (m : ℕ → ℕ) (v : ℕ) (h : transcript m) :
      transcript (Function.update m (D.control + 2) v) := by
    apply h.frame
    intro j s _
    have ha : A.transcript ≤ hintTranscriptCell A.transcript sch.m j.val s.val := by
      unfold hintTranscriptCell
      omega
    rw [Function.update_of_ne (Nat.ne_of_gt (hControlTran.trans_le ha))]
  let predict := hintPredictRows_phase S H D E header N X Y node cn seed first r.1 x J col
    (fun m => keep m ∧ childFresh m ∧ tail m) hInfoN hInfoXY hChild hControl hPredict hm hSteps
    hWord hSeedFit hKFit hStepsFit hBXFit hBYFit hCoeffSpace hCoeff hPerm hCtrl hControlTran
    hScratchFit hScratchTran hTranEnd hParentBeforeHints hChildHintFit hThreshold hPredictDesc
    (by
      intro m m' hf hk
      have hf' : ∀ a, (a < L.rowScratch ∨ scratchEnd ≤ a) →
          (a < gate ∨ gate + sch.m ≤ a) → (a < B.hints ∨ B.hints + sch.m ≤ a) → m' a = m a := hf
      refine ⟨hKeep m m' (fun a ha hg hc => hf' a
        (ha.imp id (hWork.trans ·)) hg (hc.imp (by omega) (by omega))) hk.1, ?_, ?_⟩
      · exact hk.2.1.frame (fun q hq => hf' _
          (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)))
      · apply hk.2.2.frame
        intro a ha _
        change B.result ≤ a at ha
        exact hf' a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)))
    (fun m v hk => ⟨hCursor m v hk.1, hk.2.1.update_below _ _ hBCtrl, hk.2.2.update_below v hRCtrl⟩)
  let prepare := hintPrepareChild_phase S H D E header node seed first word N X Y t Bc Xs Ys children
    r x J col offsets (fun m => ready m ∧ abstain m ∧ tail m) hWidth hW (by omega : 16 < 2 ^ E.W)
    hInfoXY hSize hSlice hGCtrl (by omega : gate + sch.m ≤ B.payload)
    (by omega : B.payload + (B.saveOffset + 2) ≤ 2 ^ E.W) hRoom1 hRoom2 hInputFit hInputSep
    hTable hReturn hLayout hCount hLocal (fun p _ _ => hPrepareDesc p)
    (fun m hk => hPacked m hk.1.2.2)
    (by
      intro m m' hf hk
      have frame : CRMemFrame B.payload (B.payload + B.saveOffset + 2) m m' := hf
      obtain ⟨⟨hh, ht, hk⟩, hb, hfresh⟩ := hk
      refine ⟨⟨hh.frame (fun q hq => frame _ (Or.inl (by omega))), ht.frame ?_,
        hKeep m m' (fun a _ _ hc => frame a (hc.imp (by omega) (by omega))) hk⟩,
        hb.frame (fun q _ => frame _ (Or.inr (by omega))), hfresh.frame ?_⟩
      · intro j s hs
        have hb := hintTranscriptCell_beforeColumn sch A.transcript j s col.val hs
        change hintTranscriptCell A.transcript sch.m j.val s.val < gate at hb
        exact frame _ (Or.inl (by omega))
      · intro a ha _
        change B.result ≤ a at ha
        exact frame a (Or.inr (by omega)))
    (fun m v hk => ⟨⟨hk.1.1.update_below _ _ hPCtrl, hCursorTranscript m v hk.1.2.1,
      hCursor m v hk.1.2.2⟩, hk.2.1.update_below _ _ hHCtrl, hk.2.2.update_below v hRCtrl⟩)
  let called := call (fun m => ready m ∧ pred m)
    (by
      intro m m' hf hk
      obtain ⟨hh, ht, hp⟩ := hintColumnFrame_afterChild col hTran hTranEnd
        (show A.hints + sch.N ≤ lo by omega) hf hk.1.1 hk.1.2.1 hk.2
      exact ⟨⟨hh, ht, hKeep m m' (fun a hs _ hb => hf a hs hb) hk.1.2.2⟩, hp⟩)
    (fun m v hk => ⟨⟨hk.1.1.update_below _ _ hPCtrl, hCursorTranscript m v hk.1.2.1,
      hCursor m v hk.1.2.2⟩, hk.2.update_below _ _ hGCtrl⟩)
  let recovered := hintRecoverColumn_phase S H D E header node cn (first + sch.m + 1 + sch.m + run.length)
    N X Y r.1 x J col (fun m => parentHints m ∧ keep m) hInfoXY hRecover
    (by omega : 1 < 2 ^ E.W) hControlTran hRCtrl
    (by omega : gate < 2 ^ E.W) (by omega : B.result < 2 ^ E.W) (by omega : sch.m < 2 ^ E.W)
    (by omega : gate + sch.m ≤ 2 ^ E.W) (by omega : B.result + sch.m ≤ 2 ^ E.W)
    (Or.inl (by omega : gate + sch.m ≤ B.result))
    (fun pos hp => hDescriptor (show D.events[pos.val]? = some (.recoverColumn node col.val cn) by
      rw [hp]; exact hRecover) 2 (by simp [HintTreeEvent.recordLength]))
    (by
      intro m m' hf hk
      have frame : CRMemFrame gate (gate + sch.m) m m' := hf
      exact ⟨hk.1.frame (fun q _ => frame _ (Or.inr (by omega))),
        hKeep m m' (fun a _ hg _ => frame a hg) hk.2⟩)
    (fun m v hk => ⟨hk.1.update_below _ _ hPCtrl, hCursor m v hk.2⟩)
  have hLen : events.length = sch.m + (1 + sch.m) + run.length + 1 := by
    simp only [events, hintRecursiveColumnEvents, List.length_append, List.length_map, List.length_range,
      List.length_cons, List.length_nil, Nat.zero_add]
    change sch.m + 1 + sch.m + run.length + 1 = _
    omega
  let prepared := (predict.relabel
      (fun m => show (parentHints m ∧ transcript m ∧ keep m ∧ childFresh m ∧ tail m) ↔
        (ready m ∧ childFresh m ∧ tail m) by unfold ready; tauto)
      (fun _ => Iff.rfl)).append
    (prepare.relabel
      (fun m => show (pred m ∧ childFresh m ∧ ready m ∧ abstain m ∧ tail m) ↔
        ((parentHints m ∧ transcript m ∧ keep m ∧ childFresh m ∧ tail m) ∧ pred m ∧ abstain m) by
        unfold ready; tauto)
      (fun _ => Iff.rfl))
  let decoded := prepared.append_at (called.relabel
    (fun m => show (HintSubtreeReady S D E.W cn child (r.2 col) input (sch.exactHint r.1 x J col) m ∧
        ready m ∧ pred m) ↔ (pred m ∧ childWords m ∧ ready m ∧ abstain m ∧ tail m) by
      unfold HintSubtreeReady
      rw [hChildInput, hSize]
      tauto)
    (fun m => show (HintBitmap m B.result child.N input ∧ ready m ∧ pred m) ↔
        (transcript m ∧ pred m ∧ result m ∧ parentHints m ∧ keep m) by
      unfold ready result
      rw [hSize]
      tauto))
    (by omega : first + sch.m + 1 + sch.m = first + (sch.m + (1 + sch.m)))
  change HintDecoderPhase S H D E header first events.length
    (fun m => ready m ∧ childFresh m ∧ tail m) (fun m => parentHints m ∧ next m ∧ keep m)
  rw [hLen]
  exact decoded.append_at (recovered.relabel (fun _ => Iff.rfl) (fun _ => by tauto))
    (by change first + sch.m + 1 + sch.m + run.length = first + (sch.m + (1 + sch.m) + run.length); omega)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRecursiveColumn_phase
end S_HintRecursiveColumnPhase20261120
section S_HintDirectReadAtPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintDirectReadAt_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node first word N X Y t : ℕ)
    (lr : (H.scheme N X Y).LocalSeed) (x : Finset ℕ) (keep : (ℕ → ℕ) → Prop)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hWidth : E.W = D.placement.width) (hWord : 2 < 2 ^ E.W) (hW : 0 < E.W)
    (hSlice : HintEventSlice D first (hintDirectReads (H.scheme N X Y) node (word * E.W))) :
    let sch := H.scheme N X Y
    let A := D.placement.arena node
    let M := synLen (crFamily S) (.direct sch t)
    let packed := HintMemoryWords E.W word (hintSketchVector (crFamily S) (.direct sch t) lr x)
    A.transcript + sch.m * sch.ℓ ≤ 2 ^ E.W →
    D.control + 2 < A.transcript →
    word + wordsOf E.W M ≤ A.transcript →
    (word * E.W + M) / E.W < A.transcript →
    (D.control + 2 < word ∨ word + wordsOf E.W M ≤ D.control + 2) →
    (∀ pos : Fin D.events.length, first ≤ pos.val → pos.val < first + sch.m * sch.ℓ →
      hintEventDescriptor header D.events (hintEventRecord S H D.placement) pos.val + 3 < 2 ^ E.W) →
    (∀ m m', CRMemFrame A.transcript (A.transcript + sch.m * sch.ℓ) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    word * E.W + M ≤ 2 ^ E.W →
    HintDecoderPhase S H D E header first (sch.m * sch.ℓ)
      (fun m => packed m ∧ keep m)
      (fun m => packed m ∧ HintTranscriptCorrect sch lr x A.transcript (fun _ _ => True) m ∧ keep m) := by
  let sch := H.scheme N X Y
  let CR := crFamily S
  let A := D.placement.arena node
  let M := synLen CR (.direct sch t)
  let packed := HintMemoryWords E.W word (hintSketchVector CR (.direct sch t) lr x)
  let inv := fun i m =>
    packed m ∧ HintTranscriptCorrect sch lr x A.transcript (fun j s => j.val * sch.ℓ + s.val < i) m ∧ keep m
  dsimp only
  intro hFit hControlHigh hSep hInputBefore hControlOutside hDescriptors hKeep hKeepCursor hInput
  change (D.control + 2 < word ∨ word + wordsOf E.W M ≤ D.control + 2) at hControlOutside
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
      change a < wordsOf E.W M at ha
      rw [Function.update_of_ne (by rcases hControlOutside with h | h <;> omega : word + a ≠ D.control + 2)]
      exact hP a ha
    · intro j s hs
      have hAddr : hintTranscriptCell A.transcript sch.m j.val s.val ≠ D.control + 2 := by
        unfold hintTranscriptCell
        omega
      rw [Function.update_of_ne hAddr]
      exact hT j s hs
  · intro i hi j hj act base state
    dsimp only
    intro hSelect _ hAt hPc hArg hCtx _ hInv hRecord
    let p : Fin (sch.m * sch.ℓ) := ⟨i, hi⟩
    have hIn : i < (hintDirectReads sch node (word * E.W)).length := by
      rw [hintDirectReads_length]
      exact hi
    have hEv : (hintDirectReads sch node (word * E.W))[p.val]? = some D.events[j.val] := by
      have h := (hSlice.read i hIn).symm
      rw [← hj] at h
      exact h.trans (List.getElem?_eq_getElem (l := D.events) j.isLt)
    obtain ⟨row, col, hRC⟩ := hintDirectReads_split p
    have hAtEvent := hintDirectReads_at sch node (word * E.W) row col
    have hAtI : (hintDirectReads sch node (word * E.W))[p.val]? =
        some (.directBit node row.val col.val (word * E.W + row.val * sch.ℓ + col.val)) := by
      rw [hRC]
      exact hAtEvent
    have hEq := Option.some.inj (hEv.symm.trans hAtI)
    have hTag : D.events[j.val].tag = 0 := by rw [hEq]; rfl
    rw [hTag] at hSelect
    have hAct : act = hintUnpackAction := (Option.some.inj hSelect).symm
    subst act
    obtain ⟨hP, hT, hK⟩ := hInv
    let desc := hintEventDescriptor header D.events (hintEventRecord S H D.placement) j.val
    have hTable (row col offset : ℕ) (h : D.events[j.val] = .directBit node row col offset) :
        (hintDirectBitBlock E.W A.transcript sch.m row col offset).At E desc := by
      rw [h] at hRecord
      simp only [hintEventRecord, hInfoXY, Option.getD_some] at hRecord
      rw [hWidth]
      exact hRecord
    have hStep := hintDirectPhase_step (CR := CR) (hintNativeProgram S) E state sch t lr x
      node word A.transcript desc base p D.events[j.val] hEv hTable hP hT hW hWord
      (hDescriptors j (by omega) (by omega)) hInput hSep hInputBefore hFit hArg hAt hPc
    change Sem (hintNativeProgram S) E base (base + 22) state _
    apply Sem.mono hStep
    rintro k out ⟨hk, hc, hP', hT', hf⟩
    refine ⟨hk, ⟨hP', hT', hKeep _ _ hf hK⟩, hc.trans hCtx, ?_⟩
    intro a _ ha
    exact hf a (Or.inl (ha.trans_lt hControlHigh))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectReadAt_phase
end S_HintDirectReadAtPhase20261120
section S_HintNodeEventSlices20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem HintEventSlice.root (S : CRSourceBundle) (H : HintParams)
    {T : Node} (hT : IsSchemeTree H T) (W Bc header : ℕ) :
    let D := hintDecoderTables S H hT W Bc header
    let offset := fun node => D.placement.inputWord node * W
    HintEventSlice D 0 (hintTreeEvents (crFamily S) offset T 0 0 0) := by
  dsimp only
  let D := hintDecoderTables S H hT W Bc header
  let offset := fun node => D.placement.inputWord node * W
  refine ⟨[], [], rfl, ?_⟩
  change D.events = [] ++ hintTreeEvents (crFamily S) offset T 0 0 0 ++ []
  simp only [List.nil_append, List.append_nil]
  have hOffsets : offset = (fun node => if node = 0 then 0 else (D.placement.arena node).payload * W) := by
    funext node
    by_cases hn : node = 0 <;> simp [offset, HintDecoderPlacement.inputWord, hn]
  rw [hOffsets]
  rfl

theorem hintNodeEventSlice_rowTail {D : HintDecoderTables} (CR : CRFamily)
    (sch : RowScheme) (node seed t first residualOffset : ℕ) (prelude_ : List HintTreeEvent)
    (hSlice : HintEventSlice D first (prelude_ ++ (List.range sch.m).map (.finishRow node seed) ++
      hintResidualEvents CR node residualOffset sch.N t)) :
    HintEventSlice D first prelude_ ∧
    (∀ q < sch.m, D.events[first + prelude_.length + q]? = some (.finishRow node seed q)) ∧
    HintEventSlice D (first + prelude_.length + sch.m)
      (hintResidualEvents CR node residualOffset sch.N t) := by
  let rows := (List.range sch.m).map (HintTreeEvent.finishRow node seed)
  let tail := hintResidualEvents CR node residualOffset sch.N t
  have hs : HintEventSlice D first (prelude_ ++ (rows ++ tail)) := by
    simpa only [List.append_assoc] using hSlice
  have hLen : rows.length = sch.m := by simp [rows]
  refine ⟨hs.left, ?_, ?_⟩
  · intro q hq
    have h := hs.right.left.read q (show q < rows.length by rwa [hLen])
    have hRange : q < (List.range sch.m).length := by simpa using hq
    simpa only [rows, List.getElem?_map, List.getElem?_eq_getElem hRange, List.getElem_range, Option.map_some] using h
  · simpa only [hLen] using hs.right.right

theorem hintRecursiveNodeEventSlices (CR : CRFamily) (D : HintDecoderTables) (payloadOffset : ℕ → ℕ)
    (sch : RowScheme) (t : ℕ) (Xs Ys : Fin sch.ℓ → ℕ) (children : Fin sch.ℓ → Node)
    (node seed offset first : ℕ)
    (hSlice : HintEventSlice D first (hintTreeEvents CR payloadOffset
      (.recursive sch t Xs Ys children) node seed offset)) :
    let columns := List.ofFn (hintRecursiveColumnEvents CR payloadOffset sch children node seed offset)
    (∀ col : Fin sch.ℓ,
      HintEventSlice D (first + ((columns.take col.val).flatten).length)
        (hintRecursiveColumnEvents CR payloadOffset sch children node seed offset col)) ∧
    (∀ q < sch.m, D.events[first + columns.flatten.length + q]? = some (.finishRow node seed q)) ∧
    HintEventSlice D (first + columns.flatten.length + sch.m)
      (hintResidualEvents CR node (offset + ∑ col, synLen CR (children col)) sch.N t) := by
  dsimp only
  let column := hintRecursiveColumnEvents CR payloadOffset sch children node seed offset
  let columns := List.ofFn column
  rw [hintTreeEvents_recursive] at hSlice
  obtain ⟨hp, hRows, hTail⟩ := hintNodeEventSlice_rowTail CR sch node seed t first
    (offset + ∑ col, synLen CR (children col)) columns.flatten hSlice
  refine ⟨?_, hRows, hTail⟩
  intro col
  have hi : col.val < columns.length := by
    change col.val < (List.ofFn column).length
    rw [List.length_ofFn]
    exact col.isLt
  have h := hp.flatten col.val hi
  change HintEventSlice D (first + ((columns.take col.val).flatten).length) ((List.ofFn column)[col.val]'hi) at h
  rw [List.getElem_ofFn] at h
  exact h

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintEventSlice.root
#print axioms LinearSetReconciliation327.Main.hintRecursiveNodeEventSlices
end S_HintNodeEventSlices20261120
section S_HintRecursiveRowsPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintRecursiveRows_phase (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (E : RAMEnv) (header node seed offset first : ℕ)
    (sch : RowScheme) (children : Fin sch.ℓ → Node) (lr : sch.LocalSeed)
    (x J : Finset ℕ) (payloadOffset : ℕ → ℕ) (pending : ℕ → (ℕ → ℕ) → Prop) :
    let A := D.placement.arena node
    let columns := hintRecursiveColumnEvents (crFamily S) payloadOffset sch children node seed offset
    let blocks := List.ofFn columns
    let hints := fun m => HintBitmap m A.hints sch.N J
    let inv := fun i m => hints m ∧
      HintTranscriptCorrect sch lr x A.transcript (fun _ s => s.val < i) m ∧ pending i m
    D.control + 2 < A.hints →
    (∀ m v, pending 0 m → pending 0 (Function.update m (D.control + 2) v)) →
    (∀ col : Fin sch.ℓ, HintDecoderPhase S H D E header
      (first + ((blocks.take col.val).flatten).length) (columns col).length
      (inv col.val) (inv (col.val + 1))) →
    HintDecoderPhase S H D E header first blocks.flatten.length
      (fun m => hints m ∧ pending 0 m)
      (fun m => hints m ∧ HintTranscriptCorrect sch lr x A.transcript (fun _ _ => True) m ∧ pending sch.ℓ m) := by
  let A := D.placement.arena node
  let columns := hintRecursiveColumnEvents (crFamily S) payloadOffset sch children node seed offset
  let blocks := List.ofFn columns
  let hints := fun m => HintBitmap m A.hints sch.N J
  let inv := fun i m => hints m ∧
    HintTranscriptCorrect sch lr x A.transcript (fun _ s => s.val < i) m ∧ pending i m
  dsimp only
  intro hControl hCursor hPhase
  let size := fun i => if hi : i < sch.ℓ then (columns ⟨i, hi⟩).length else 0
  have hSize (i : Fin sch.ℓ) : size i.val = (columns i).length := by
    dsimp only [size]
    rw [dif_pos i.isLt]
  have hPrefix (i : ℕ) (hi : i ≤ sch.ℓ) :
      hintPhasePrefixCount size i = ((blocks.take i).flatten).length :=
    hintPhasePrefixCount_ofFn columns size hSize i hi
  have hAll : hintPhasePrefixCount size sch.ℓ = blocks.flatten.length := by
    rw [hPrefix _ le_rfl, List.take_of_length_le]
    simp only [blocks, List.length_ofFn, le_refl]
  have hRun := HintDecoderPhase.concat (S := S) (H := H) (D := D) (E := E) (header := header)
    (first := first) (m := sch.ℓ) size inv
    (by
      intro m v hm
      obtain ⟨hHint, _, hp⟩ := hm
      exact ⟨hHint.update_below _ _ hControl, fun _ _ h => (Nat.not_lt_zero _ h).elim, hCursor m v hp⟩)
    (by
      intro i hi
      let col : Fin sch.ℓ := ⟨i, hi⟩
      have hStep := hPhase col
      change HintDecoderPhase S H D E header (first + ((blocks.take i).flatten).length)
        (columns col).length (inv i) (inv (i + 1)) at hStep
      rw [hPrefix i hi.le, show size i = (columns col).length from hSize col]
      exact hStep)
  rw [hAll] at hRun
  exact hRun.relabel
    (fun m => show inv 0 m ↔ hints m ∧ pending 0 m from
      ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, fun _ _ hs => (Nat.not_lt_zero _ hs).elim, h.2⟩⟩)
    (fun m => show inv sch.ℓ m ↔ hints m ∧
      HintTranscriptCorrect sch lr x A.transcript (fun _ _ => True) m ∧ pending sch.ℓ m from
      ⟨fun h => ⟨h.1, fun j s _ => h.2.1 j s s.isLt, h.2.2⟩,
        fun h => ⟨h.1, fun j s _ => h.2.1 j s trivial, h.2.2⟩⟩)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRecursiveRows_phase
end S_HintRecursiveRowsPhase20261120
section S_HintRecursiveFold20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

abbrev HintColumnPhase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node seed first t : ℕ) (sch : RowScheme)
    (Xs Ys : Fin sch.ℓ → ℕ) (children : Fin sch.ℓ → Node)
    (r : (Node.recursive sch t Xs Ys children).Seed) (x J : Finset ℕ) (col : Fin sch.ℓ) :=
  let CR := crFamily S
  let L := D.placement
  let A := L.arena node
  let T := Node.recursive sch t Xs Ys children
  let child := children col
  let cn := hintChildPhysicalIndex children node col
  let cs := hintChildSchemeIndex children seed col
  let B := L.arena cn
  let lo := hintArenaStart D.heap D.stride cn
  let hi := hintArenaStart D.heap D.stride (cn + child.nodeCount)
  let word := L.inputWord node
  let offsets := fun i => L.inputWord i * E.W
  let gate := A.transcript + col.val * sch.m
  let events := hintRecursiveColumnEvents CR offsets sch children node seed (word * E.W) col
  ∀ keep : (ℕ → ℕ) → Prop,
    (∀ m, keep m → HintMemoryWords E.W word (hintSketchVector CR T r x) m) →
    (∀ m m', (∀ a, (a < L.rowScratch ∨ D.listBase ≤ a) →
      (a < gate ∨ gate + sch.m ≤ a) → (a < lo ∨ hi ≤ a) → m' a = m a) → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintSubtreePhase S H D E header cn cs (first + sch.m + 1 + sch.m) child (r.2 col)
      (sch.exactChildInput r.1 x J col) (sch.exactHint r.1 x J col) →
    HintDecoderPhase S H D E header first events.length
      (fun m => (HintBitmap m A.hints sch.N J ∧
        HintTranscriptCorrect sch r.1 x A.transcript (fun _ s => s.val < col.val) m ∧ keep m) ∧
        HintFreshWords B.payload (wordsOf E.W (synLen CR child)) m ∧
        HintNodeFreshTail D cn child.nodeCount m)
      (fun m => HintBitmap m A.hints sch.N J ∧
        HintTranscriptCorrect sch r.1 x A.transcript (fun _ s => s.val < col.val + 1) m ∧ keep m)

noncomputable def hintRecursiveFold_phase (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (E : RAMEnv) (header node seed first t : ℕ)
    (sch : RowScheme) (Xs Ys : Fin sch.ℓ → ℕ) (children : Fin sch.ℓ → Node)
    (r : (Node.recursive sch t Xs Ys children).Seed) (x J : Finset ℕ)
    (keep : (ℕ → ℕ) → Prop) :
    let CR := crFamily S
    let A := D.placement.arena node
    let T := Node.recursive sch t Xs Ys children
    let arena := hintArenaStart D.heap D.stride
    let word := D.placement.inputWord node
    let offsets := fun i => D.placement.inputWord i * E.W
    let packed := HintMemoryWords E.W word (hintSketchVector CR T r x)
    let blocks := List.ofFn (hintRecursiveColumnEvents CR offsets sch children node seed (word * E.W))
    let start := fun col : Fin sch.ℓ => first + ((blocks.take col.val).flatten).length
    let ownFresh := fun (mem : ℕ → ℕ) => ∀ a, A.result ≤ a → a < arena (node + 1) → mem a = 0
    D.control + 2 < D.placement.rowScratch →
    D.placement.rowScratch ≤ D.listBase →
    D.listBase ≤ D.heap →
    D.listBase ≤ A.transcript →
    arena node ≤ A.transcript →
    A.transcript + sch.ℓ * sch.m ≤ A.hints →
    A.hints + sch.N ≤ A.result →
    A.result ≤ arena (node + 1) →
    word + wordsOf E.W (synLen CR T) ≤ A.transcript →
    (word + wordsOf E.W (synLen CR T) ≤ D.placement.rowScratch ∨ D.listBase ≤ word) →
    (word + wordsOf E.W (synLen CR T) ≤ D.control + 2 ∨ D.control + 2 < word) →
    (∀ col : Fin sch.ℓ,
      let cn := hintChildPhysicalIndex children node col
      let B := D.placement.arena cn
      B.payload = arena cn ∧ B.payload ≤ B.result ∧
      B.payload + wordsOf E.W (synLen CR (children col)) ≤ arena (cn + (children col).nodeCount)) →
    (∀ m m', HintSubtreeFrame D node T.nodeCount m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    (∀ col : Fin sch.ℓ, HintColumnPhase S H D E header node seed (start col) t sch Xs Ys children r x J col) →
    (∀ col : Fin sch.ℓ, HintSubtreePhase S H D E header
      (hintChildPhysicalIndex children node col) (hintChildSchemeIndex children seed col)
      (start col + sch.m + 1 + sch.m) (children col) (r.2 col)
      (sch.exactChildInput r.1 x J col) (sch.exactHint r.1 x J col)) →
    HintDecoderPhase S H D E header first blocks.flatten.length
      (fun m => HintSubtreeReady S D E.W node T r x J m ∧ keep m)
      (fun m => HintBitmap m A.hints sch.N J ∧
        HintTranscriptCorrect sch r.1 x A.transcript (fun _ _ => True) m ∧
        packed m ∧ ownFresh m ∧ keep m) := by
  let CR := crFamily S
  let A := D.placement.arena node
  let T := Node.recursive sch t Xs Ys children
  let arena := hintArenaStart D.heap D.stride
  let word := D.placement.inputWord node
  let offsets := fun i => D.placement.inputWord i * E.W
  let packed := HintMemoryWords E.W word (hintSketchVector CR T r x)
  let blocks := List.ofFn (hintRecursiveColumnEvents CR offsets sch children node seed (word * E.W))
  let start := fun col : Fin sch.ℓ => first + ((blocks.take col.val).flatten).length
  let ownFresh := fun (mem : ℕ → ℕ) => ∀ a, A.result ≤ a → a < arena (node + 1) → mem a = 0
  let childIndex := fun i : ℕ => node + 1 + ((List.ofFn fun s => (children s).nodeCount).take i).sum
  let endAddr := arena (node + T.nodeCount)
  let future := fun (i : ℕ) (mem : ℕ → ℕ) => ∀ a, arena (childIndex i) ≤ a → a < endAddr → mem a = 0
  let pending := fun i m => packed m ∧ ownFresh m ∧ future i m ∧ keep m
  let hints := fun m => HintBitmap m A.hints sch.N J
  dsimp only
  intro hControl hScratch hHeap hTran hTranLo hTranEnd hOwnLo hHead hPackedEnd hPackedScratch hPackedCursor
  intro hChildren hKeep hCursor columns calls
  change D.listBase ≤ A.transcript at hTran
  change arena node ≤ A.transcript at hTranLo
  change A.transcript + sch.ℓ * sch.m ≤ A.hints at hTranEnd
  change A.hints + sch.N ≤ A.result at hOwnLo
  change A.result ≤ arena (node + 1) at hHead
  change word + wordsOf E.W (synLen CR T) ≤ A.transcript at hPackedEnd
  change (word + wordsOf E.W (synLen CR T) ≤ D.placement.rowScratch ∨ D.listBase ≤ word) at hPackedScratch
  change (word + wordsOf E.W (synLen CR T) ≤ D.control + 2 ∨ D.control + 2 < word) at hPackedCursor
  change ∀ m m', HintSubtreeFrame D node T.nodeCount m m' → keep m → keep m' at hKeep
  have hCursorTran : D.control + 2 < A.transcript := by omega
  have hCursorHints : D.control + 2 < A.hints := by omega
  have hCursorOwn : D.control + 2 < A.result := by omega
  have hCursorFuture (i : ℕ) : D.control + 2 < arena (childIndex i) := by
    exact hControl.trans_le (hScratch.trans (hHeap.trans (Nat.le_add_right _ _)))
  have hPendingCursor (i : ℕ) (m : ℕ → ℕ) (v : ℕ) (hm : pending i m) :
      pending i (Function.update m (D.control + 2) v) := by
    obtain ⟨hp, ho, hf, hk⟩ := hm
    refine ⟨?_, ?_, ?_, hCursor m v hk⟩
    · intro q hq
      change q < wordsOf E.W (synLen CR T) at hq
      rw [Function.update_of_ne (by rcases hPackedCursor with h | h <;> omega)]
      exact hp q hq
    · intro a ha hb
      rw [Function.update_of_ne (Nat.ne_of_gt (hCursorOwn.trans_le ha))]
      exact ho a ha hb
    · intro a ha hb
      rw [Function.update_of_ne (Nat.ne_of_gt ((hCursorFuture i).trans_le ha))]
      exact hf a ha hb
  have hFirst : childIndex 0 = node + 1 := by simp [childIndex]
  have hLast : arena (childIndex sch.ℓ) = endAddr := by
    change arena (node + 1 + ((List.ofFn fun s => (children s).nodeCount).take sch.ℓ).sum) =
      arena (node + T.nodeCount)
    rw [List.take_of_length_le (by simp), List.sum_ofFn]
    change arena (node + 1 + ∑ s, (children s).nodeCount) = arena (node + (1 + ∑ s, (children s).nodeCount))
    rw [Nat.add_assoc]
  have hRun := hintRecursiveRows_phase S H D E header node seed (word * E.W) first sch children r.1 x J
    offsets pending hCursorHints (hPendingCursor 0) (by
      intro col
      let cn := hintChildPhysicalIndex children node col
      let B := D.placement.arena cn
      let last := cn + (children col).nodeCount
      let gate := A.transcript + col.val * sch.m
      let prev := HintTranscriptCorrect sch r.1 x A.transcript (fun _ s => s.val < col.val)
      let next := HintTranscriptCorrect sch r.1 x A.transcript (fun _ s => s.val < col.val + 1)
      have hNext : childIndex (col.val + 1) = last := hintChildIndexAt_succ children node col
      have hAt : childIndex col.val = cn := rfl
      have hPart : last ≤ node + T.nodeCount := by
        have h := hintChildPhysicalIndex_end children node col
        change last ≤ node + (1 + ∑ s, (children s).nodeCount)
        simpa only [Nat.add_assoc] using h
      have hHeadChild : node + 1 ≤ cn := by unfold cn hintChildPhysicalIndex; omega
      have hHeadLo : arena (node + 1) ≤ arena cn := hintArenaStart_mono D.heap D.stride hHeadChild
      have hChildLo : arena node ≤ arena cn := hintArenaStart_mono D.heap D.stride (by omega)
      have hChildHi : arena last ≤ endAddr := hintArenaStart_mono D.heap D.stride hPart
      have hGate : A.transcript ≤ gate := by dsimp only [gate]; omega
      have hGateEnd : gate + sch.m ≤ A.hints := by
        have h := Nat.mul_le_mul_right sch.m col.isLt
        rw [Nat.succ_mul] at h
        dsimp only [gate]
        omega
      have hLoHi : arena cn ≤ arena last := hintArenaStart_mono D.heap D.stride (Nat.le_add_right _ _)
      have hlayout : B.payload = arena cn ∧ B.payload ≤ B.result ∧
          B.payload + wordsOf E.W (synLen CR (children col)) ≤ arena last := hChildren col
      let p := columns col (pending (col.val + 1)) (fun _ h => h.1)
        (by
          intro m m' hf hm
          obtain ⟨hp, ho, hu, hk⟩ := hm
          have frame : ∀ a, (a < D.placement.rowScratch ∨ D.listBase ≤ a) →
              (a < gate ∨ gate + sch.m ≤ a) → (a < arena cn ∨ arena last ≤ a) → m' a = m a := hf
          refine ⟨hp.frame ?_, ?_, ?_, hKeep m m' ?_ hk⟩
          · intro q hq
            have hBefore : word + q < gate := by omega
            exact frame _ (hPackedScratch.imp (fun h => by omega) (fun h => by omega))
              (Or.inl hBefore) (Or.inl (by omega))
          · intro a ha hb
            rw [frame a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (hb.trans_le hHeadLo))]
            exact ho a ha hb
          · intro a ha hb
            rw [hNext] at ha
            have hBase : D.heap ≤ a := (Nat.le_add_right _ _).trans ha
            rw [frame a (Or.inr (hHeap.trans hBase)) (Or.inr (by omega)) (Or.inr ha)]
            exact hu a (by rwa [hNext]) hb
          · intro a hs hOutside
            have hOut : a < arena node ∨ endAddr ≤ a := hOutside
            exact frame a hs (hOut.imp (fun h => h.trans_le (hTranLo.trans hGate)) (by omega))
              (hOut.imp (fun h => h.trans_le hChildLo) (fun h => hChildHi.trans h)))
        (hPendingCursor (col.val + 1)) (calls col)
      have hPos : 0 < (hintRecursiveColumnEvents CR offsets sch children node seed (word * E.W) col).length := by
        simp only [hintRecursiveColumnEvents, List.length_append, List.length_cons, List.length_nil]
        omega
      change HintDecoderPhase S H D E header (start col)
        (hintRecursiveColumnEvents CR offsets sch children node seed (word * E.W) col).length
        (fun m => hints m ∧ prev m ∧ pending col.val m)
        (fun m => hints m ∧ next m ∧ pending (col.val + 1) m)
      refine p.adapt hPos ?_ (fun _ h => h) ?_ ?_
      · rintro m ⟨hh, ht, hp, ho, hf, hk⟩
        refine ⟨⟨hh, ht, hp, ho, ?_, hk⟩, ?_, ?_⟩
        · intro a ha hb
          rw [hNext] at ha
          exact hf a (by rw [hAt]; exact hLoHi.trans ha) hb
        · intro q hq
          change q < wordsOf E.W (synLen CR (children col)) at hq
          exact hf (B.payload + q) (by rw [hAt, ← hlayout.1]; omega)
            (lt_of_lt_of_le (by omega : B.payload + q < arena last) hChildHi)
        · intro a ha hb
          change B.result ≤ a at ha
          exact hf a (by rw [hAt, ← hlayout.1]; exact hlayout.2.1.trans ha) (hb.trans_le hChildHi)
      · rintro m v ⟨hh, ht, hp⟩
        refine ⟨hh.update_below _ _ hCursorHints, ?_, hPendingCursor col.val m v hp⟩
        apply ht.frame
        intro j s _
        have hAddr := hCursorTran.trans_le (show A.transcript ≤ hintTranscriptCell A.transcript sch.m j.val s.val by
          unfold hintTranscriptCell
          omega)
        rw [Function.update_of_ne (Nat.ne_of_gt hAddr)]
      · rintro m v ⟨hh, ht, hp⟩
        refine ⟨hh.update_below _ _ hCursorHints, ?_, hPendingCursor (col.val + 1) m v hp⟩
        apply ht.frame
        intro j s _
        have hAddr := hCursorTran.trans_le (show A.transcript ≤ hintTranscriptCell A.transcript sch.m j.val s.val by
          unfold hintTranscriptCell
          omega)
        rw [Function.update_of_ne (Nat.ne_of_gt hAddr)])
  refine hRun.relabel ?_ ?_
  · intro m
    change (hints m ∧ pending 0 m) ↔ (HintSubtreeReady S D E.W node T r x J m ∧ keep m)
    constructor
    · rintro ⟨hh, hp, ho, hf, hk⟩
      refine ⟨⟨hp, hh, ?_⟩, hk⟩
      intro a ha hb
      by_cases h : a < arena (node + 1)
      · exact ho a ha h
      · exact hf a (by rw [hFirst]; omega) hb
    · rintro ⟨⟨hp, hh, hf⟩, hk⟩
      have hN := hintNodeCount_pos T
      have hHeadEnd : arena (node + 1) ≤ endAddr := hintArenaStart_mono D.heap D.stride (by omega)
      refine ⟨hh, hp, (fun a ha hb => hf a ha (hb.trans_le hHeadEnd)), ?_, hk⟩
      intro a ha hb
      rw [hFirst] at ha
      exact hf a (hHead.trans ha) hb
  · intro m
    change (hints m ∧ HintTranscriptCorrect sch r.1 x A.transcript (fun _ _ => True) m ∧ pending sch.ℓ m) ↔ _
    constructor
    · rintro ⟨hh, ht, hp, ho, _, hk⟩
      exact ⟨hh, ht, hp, ho, hk⟩
    · rintro ⟨hh, ht, hp, ho, hk⟩
      refine ⟨hh, ht, hp, ho, ?_, hk⟩
      intro a ha hb
      rw [hLast] at ha
      exact (Nat.not_lt_of_ge ha hb).elim

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRecursiveFold_phase
end S_HintRecursiveFold20261120
section S_HintPlacedMemory20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintArenaFor_ioOrder (S : CRSourceBundle) (H : HintParams) (W : ℕ)
    (info : HintNodeInfo) (start : ℕ) :
    let A := hintArenaFor S H W info start
    A.payload ≤ A.transcript ∧ A.transcript ≤ A.hints ∧
      A.hints + info.universeSize < A.result ∧ A.result + info.universeSize < A.limit := by
  have order (rows steps R width time : ℕ) :
      let A := hintNodeArena start W info.payloadBits info.schemes rows steps info.universeSize R width time
      A.payload ≤ A.transcript ∧ A.transcript ≤ A.hints ∧
        A.hints + info.universeSize < A.result ∧ A.result + info.universeSize < A.limit := by
    dsimp only [hintNodeArena]
    refine ⟨by omega, by omega, by omega, ?_⟩
    apply (Nat.lt_succ_self _).trans_le
    repeat' first | exact le_rfl | apply Nat.le_trans ?_ (Nat.le_add_right _ _)
  unfold hintArenaFor
  cases info.rowParams with
  | none => exact order _ _ _ _ _
  | some p => cases p; exact order _ _ _ _ _

structure HintPlacedMemory (D : HintDecoderTables) (W node count N M : ℕ) : Prop where
  payload : (D.placement.arena node).payload = hintArenaStart D.heap D.stride node
  scratch : D.control + 2 < D.placement.rowScratch
  list : D.placement.rowScratch ≤ D.listBase
  heap : D.listBase ≤ D.heap
  transcript : (D.placement.arena node).payload ≤ (D.placement.arena node).transcript
  hints : (D.placement.arena node).transcript ≤ (D.placement.arena node).hints
  result : (D.placement.arena node).hints + N < (D.placement.arena node).result
  limit : (D.placement.arena node).result + N < (D.placement.arena node).limit
  own : (D.placement.arena node).limit ≤ hintArenaStart D.heap D.stride (node + 1)
  finish : hintArenaStart D.heap D.stride (node + 1) ≤ hintArenaStart D.heap D.stride (node + count)
  packed : D.placement.inputWord node + wordsOf W M ≤ (D.placement.arena node).transcript
  readable : 0 < W → (D.placement.inputWord node * W + M) / W <
    (D.placement.arena node).transcript
  outsideScratch : D.placement.inputWord node + wordsOf W M ≤ D.placement.rowScratch ∨
    D.listBase ≤ D.placement.inputWord node
  outsideCursor : D.placement.inputWord node + wordsOf W M ≤ D.control + 2 ∨
    D.control + 2 < D.placement.inputWord node

theorem hintDecoderTables_placedMemory (S : CRSourceBundle) (H : HintParams)
    {R T : Node} (hR : IsSchemeTree H R) (hT : IsSchemeTree H T)
    (W Bc header node seed : ℕ)
    (hp : HintPlacedSubtree (crFamily S) H (hintDecoderTables S H hR W Bc header) hT node seed)
    (hRootBits : node = 0 → synLen (crFamily S) T ≤ synLen (crFamily S) R) :
    HintPlacedMemory (hintDecoderTables S H hR W Bc header) W node T.nodeCount T.N (synLen (crFamily S) T) := by
  let D := hintDecoderTables S H hR W Bc header
  let A := D.placement.arena node
  let arena := hintArenaStart D.heap D.stride
  let word := D.placement.inputWord node
  let M := synLen (crFamily S) T
  have hPayload : A.payload = arena node := hintDecoderTables_payload S H hR W Bc header node
  have hControl : D.placement.rowScratch = D.control + 3 := rfl
  have hScratch : D.control + 2 < D.placement.rowScratch := by omega
  have hList : D.placement.rowScratch ≤ D.listBase := Nat.le_add_right _ _
  have hHeap : D.listBase ≤ D.heap := Nat.le_add_right _ _
  have hInfo : D.placement.info node = hintNodeInfo (crFamily S) hT node seed :=
    HintPlacedSubtree.info S H hR hT W Bc header node seed hp
  have hN : (D.placement.info node).universeSize = T.N := by
    rw [hInfo]
    exact (hintNodeInfo_sizes (crFamily S) H hT node seed).1
  have hShape := hintArenaFor_ioOrder S H W (D.placement.info node) (arena node)
  change A.payload ≤ A.transcript ∧ A.transcript ≤ A.hints ∧ A.hints + (D.placement.info node).universeSize <
    A.result ∧ A.result + (D.placement.info node).universeSize < A.limit at hShape
  rw [hN] at hShape
  obtain ⟨hTran, hHints, hResult, hLimit⟩ := hShape
  have hCount := hintNodeCount_pos T
  have hSpan : node + T.nodeCount ≤ D.infos.length := hp.span
  have hNode : node < D.infos.length := by omega
  have hOwn : A.limit ≤ arena (node + 1) := by
    have h := hintDecoderTables_arena_fits S H hR W Bc header ⟨node, hNode⟩
    change A.limit ≤ arena node + D.stride at h
    exact h.trans (by unfold arena hintArenaStart; rw [Nat.mul_succ, Nat.add_assoc])
  have hFinish : arena (node + 1) ≤ arena (node + T.nodeCount) :=
    hintArenaStart_mono D.heap D.stride (by omega)
  obtain ⟨_, _, _, hWords, hRead⟩ := hintDecoderTables_localInput S H hR hT W Bc header node seed hp
  have hStart : D.heap ≤ A.payload := hPayload ▸ Nat.le_add_right _ _
  have hRoot (hn : node = 0) : word + wordsOf W M ≤ D.control := by
    have hw : word = 0 := by simp [word, HintDecoderPlacement.inputWord, hn]
    have hM : M ≤ synLen (crFamily S) R := hRootBits hn
    have hb : wordsOf W M ≤ wordsOf W (synLen (crFamily S) R) := by
      unfold wordsOf
      apply Nat.div_le_div_right
      omega
    rw [hw, Nat.zero_add]
    exact hb.trans (Nat.le_add_right _ _)
  refine ⟨hPayload, hScratch, hList, hHeap, hTran, hHints, hResult, hLimit, hOwn, hFinish, hWords, hRead, ?_, ?_⟩
  · change word + wordsOf W M ≤ D.placement.rowScratch ∨ D.listBase ≤ word
    by_cases hn : node = 0
    · exact Or.inl ((hRoot hn).trans (by omega))
    · have hw : word = A.payload := by simp [word, A, HintDecoderPlacement.inputWord, hn]
      exact Or.inr (by rw [hw]; exact hHeap.trans hStart)
  · change word + wordsOf W M ≤ D.control + 2 ∨ D.control + 2 < word
    by_cases hn : node = 0
    · exact Or.inl ((hRoot hn).trans (Nat.le_add_right _ _))
    · have hw : word = A.payload := by simp [word, A, HintDecoderPlacement.inputWord, hn]
      exact Or.inr (by rw [hw]; exact hScratch.trans_le (hList.trans (hHeap.trans hStart)))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_placedMemory
end S_HintPlacedMemory20261120
section S_HintPublicRow20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintPermInv_env (R : Node) (r : (hintSpec R).Seed) (W : ℕ) (det : ℕ → ℕ)
    (k N : ℕ) (h : k < (hintSpec R).permSizes.length)
    (hLen : (hintSpec R).permSizes.get ⟨k, h⟩ = N) :
    ∀ p : Fin N, ((hintSpec R).env W det r).permInv k p.val = ((permNode R r k N).symm p).val := by
  subst N
  intro p
  simp only [TableSpec.env, permNode, dif_pos h, dif_pos trivial, dif_pos p.isLt]

theorem hintRowPublic_of_head (H : HintParams) (R T : Node)
    (r : (hintSpec R).Seed) (W : ℕ) (det : ℕ → ℕ) (k N X Y : ℕ)
    (hHead : (schemeNodes R)[k]? = some T) (hN : T.N = N) :
    let E := (hintSpec R).env W det r
    let β := coinsNode H R r N X Y k
    let π := permNode R r k N
    (∀ p : Fin N, E.permInv k p.val = (π.symm p).val) ∧
    (∀ j : Fin (H.rows X Y), ∀ s : Fin (H.ell N X Y), ∀ q : Fin (H.Nmax N X Y),
      E.coeff k (j.val * H.ell N X Y * H.Nmax N X Y + q.val + s.val * H.Nmax N X Y) = (β j s q).val) ∧
    CoefAl H E k N X Y β := by
  let E := (hintSpec R).env W det r
  obtain ⟨hp, hs⟩ := permSizes_get_of_block hHead
  have hCoeff := (upAlignment_of_head H R T r W det k N X Y hHead hN).2
  refine ⟨hintPermInv_env R r W det k N hp (hs.trans hN), ?_, hCoeff⟩
  intro j s q
  have hAddress : j.val * H.ell N X Y * H.Nmax N X Y + q.val + s.val * H.Nmax N X Y =
      (j.val * H.ell N X Y + s.val) * H.Nmax N X Y + q.val := by
    rw [Nat.add_mul, Nat.add_right_comm]
  rw [hAddress]
  exact hCoeff j s q

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowPublic_of_head
end S_HintPublicRow20261120


