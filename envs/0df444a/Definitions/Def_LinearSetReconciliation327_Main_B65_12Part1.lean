-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_B65_12Part1
-- name    : LinearSetReconciliation327_Main_B65_12Part1
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-26T14:35:19.454847+00:00
-- url     : https://prove2.me/theorems/fc972903-074f-5ce1-8992-d0ff7ebb494a
-- title:
--   Theorem 6.5 supporting machine proof B65_12Part1
-- statement:
--   Definitions and verified machine facts used in the row-column set reconciliation construction.
-- source:
--   Linear Set Reconciliation with O(d) Additive Redundancy, Sections 5, 6.2 and 9.2

import Definitions.Def_LinearSetReconciliation327_Main_B65_12Support
import Definitions.Def_LinearSetReconciliation327_Main_B65_09
import Definitions.Def_LinearSetReconciliation327_Main_B65_10
import Definitions.Def_LinearSetReconciliation327_Main_B65_11
set_option autoImplicit false

section S_HintRunPlacedPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintDecoderPhase.relabel {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header first count : ℕ} {A B A' B' : (ℕ → ℕ) → Prop}
    (p : HintDecoderPhase S H D E header first count A B)
    (before : ∀ m, A m ↔ A' m) (after : ∀ m, B m ↔ B' m) :
    HintDecoderPhase S H D E header first count A' B' :=
  ⟨p.budget, p.inv, fun m => (p.start m).trans (before m),
    fun m => (p.stop m).trans (after m), p.cursor, p.step⟩

noncomputable def hintPhaseRunBudget (S : CRSourceBundle) (count N : ℕ) (budget : ℕ → ℕ) : ℕ :=
  hintDispatchBudget (hintNativeActions S) count budget + 29 * N + 67

theorem hintRunPlacedPhase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header N : ℕ) (up previous : ℕ → ℕ)
    {M : ℕ} (y : Fin M → ZMod 2) (x : Fin N → ZMod 2) (hints : List ℕ)
    (before after : (ℕ → ℕ) → Prop)
    (phase : HintDecoderPhase S H D E header 0 D.events.length before after)
    (hHeader : 3 < header) (hDet : E.det = D.det S H up previous header N)
    (hWord : 15 < 2 ^ E.W) (hW : 0 < E.W)
    (hDetSpace : hintDecoderDetEnd S H D header < 2 ^ E.W)
    (hHints : hints.Nodup) (hInside : ∀ a ∈ hints, a < N)
    (hSize : N < 2 ^ E.W) (hWords : wordsOf E.W M < 2 ^ E.W) :
    let A := D.placement.arena 0
    let start := decoderStart E.W y hints
    (wordsOf E.W M + N ≤ A.hints) →
    D.control + 2 < A.hints → A.hints + N < 2 ^ E.W →
    D.listBase + N ≤ A.result → A.result < 2 ^ E.W → A.result + N ≤ 2 ^ E.W →
    (∀ m, HintBitmap m A.hints N hints.toFinset →
       (∀ a, (a < A.hints ∨ A.hints + N < a) → a ≠ D.control → a ≠ D.control + 1 →
         m a = start.mem a) → before m) →
    (∀ m, after m → HintBitmap m A.result N (support x)) →
    ∃ out, HaltsWithin (hintNativeProgram S) E
      (hintPhaseRunBudget S D.events.length N phase.budget) start out ∧
      OutputsSupport out x := by
  let A := D.placement.arena 0
  let start := decoderStart E.W y hints
  let events := hintTreeEntries header D.events (hintEventRecord S H D.placement)
  let accept := fun q => decide (q ∈ support x)
  dsimp only
  intro hSep hCtrl hHintSpan hOutputSep hResFit hOutputSpan hInit hFinish
  change wordsOf E.W M + N ≤ A.hints at hSep
  change D.control + 2 < A.hints at hCtrl
  change A.hints + N < 2 ^ E.W at hHintSpan
  change D.listBase + N ≤ A.result at hOutputSep
  change A.result + N ≤ 2 ^ E.W at hOutputSpan
  have hLen := hintTreeEntries_length header D.events (hintEventRecord S H D.placement)
  have hJ := hintLength_le_of_valid hints N hHints hInside
  have hState := hintDecoderStart_word E y hints hW hWords (hJ.trans_lt hSize)
    (fun a ha => (hInside a ha).trans hSize)
  have hDetEnd : header + 16 + 2 * D.events.length + (D.events.map HintTreeEvent.recordLength).sum < 2 ^ E.W := by
    have hLE := Nat.le_add_right
      (hintEventDescriptor header D.events (hintEventRecord S H D.placement) D.events.length)
      (D.aux.map HintDetBlock.length).sum
    have hlt := hLE.trans_lt hDetSpace
    rwa [hintEventRecords_end] at hlt
  change A.result < 2 ^ E.W at hResFit
  have hListFit : D.listBase < 2 ^ E.W := lt_of_le_of_lt (by omega : D.listBase ≤ A.result) hResFit
  obtain ⟨hdr, tbl⟩ := hintDecoderTables_header S H D E up previous header N hHeader hDet hWord hDetEnd
    (by omega) hHintSpan hResFit hListFit
  have hHdr : HintRootHeader E header D.control A.hints A.result D.listBase (header + 16) events.length N := by
    rw [hLen]
    exact hdr
  have hTags (j : Fin events.length) : events[j.val].1 < (hintNativeActions S).length := by
    have hAt : events[j.val] = ((D.events[j.val]'(by simpa only [events, hintTreeEntries_length] using j.isLt)).tag,
        hintEventDescriptor header D.events (hintEventRecord S H D.placement) j.val) := by
      simp [events, hintTreeEntries]
    rw [hAt, hintNativeActions_count]
    generalize D.events[j.val]'(by simpa only [events, hintTreeEntries_length] using j.isLt) = ev
    cases ev <;> simp [HintTreeEvent.tag]
  have hRoot := hintNativeRoot_sem S E start header D.control A.hints A.result D.listBase (header + 16) N
    events phase.budget phase.inv accept hHdr rfl hState (hState.1 1) (hState.1 2)
    (by change wordsOf E.W M + min hints.length N ≤ 2 ^ E.W; omega)
    (Or.inl (by change wordsOf E.W M + min hints.length N ≤ A.hints; omega))
    (Or.inl (by omega)) hOutputSep hOutputSpan tbl hTags
    (by
      intro m hStamp hFrame
      apply (phase.start m).mpr
      apply hInit m _ hFrame
      intro q hq
      exact (hStamp q hq).trans (hintDecoderStart_stamp_bits E y hints N q hSize hHints hInside))
    phase.cursor (phase.actions up previous N hHeader hDet)
    (by
      intro m hi q hq
      have hEnd : after m := (phase.stop m).mp (by simpa only [events, hintTreeEntries_length] using hi)
      have hb := hFinish m hEnd q hq
      by_cases h : q ∈ support x <;> simpa [hintTruth, accept, h] using hb)
  obtain ⟨_, k, out, hExec, hPc, hTime, hList⟩ := hRoot
  refine ⟨out, ⟨k, ?_, hExec, hintNativeRoot_halt S out hPc⟩, ?_⟩
  · have hTime' : k ≤ hintPhaseRunBudget S D.events.length N phase.budget := by
      simpa only [hintPhaseRunBudget, events, hintTreeEntries_length] using hTime
    exact_mod_cast hTime'
  · apply hintEmitResult_support out x accept _ hList
    intro i
    change decide (i.val ∈ support x) = true ↔ x i = 1
    rw [decide_eq_true_iff]
    unfold support
    constructor
    · rintro h
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp h
      have e : j = i := Fin.ext he
      subst j
      exact (Finset.mem_filter.mp hj).2
    · intro hx
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRunPlacedPhase
end S_HintRunPlacedPhase20261120
section S_HintRecursiveColumnSlice20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintRecursiveColumn_slice (CR : CRFamily) (D : HintDecoderTables) (payloadOffset : ℕ → ℕ)
    (sch : RowScheme) (children : Fin sch.ℓ → Node) (node seed offset first : ℕ) (col : Fin sch.ℓ)
    (hSlice : HintEventSlice D first (hintRecursiveColumnEvents CR payloadOffset sch children node seed offset col)) :
    let child := hintChildPhysicalIndex children node col
    let childSeed := hintChildSchemeIndex children seed col
    let childOffset := offset + ((List.ofFn fun i => synLen CR (children i)).take col.val).sum
    let run := hintTreeEvents CR payloadOffset (children col) child childSeed (payloadOffset child)
    (∀ j < sch.m, D.events[first + j]? = some (.predict node seed col.val j)) ∧
    D.events[first + sch.m]? = some (.childCopy node col.val child childOffset (synLen CR (children col))) ∧
    (∀ i < sch.m, D.events[first + sch.m + 1 + i]? = some (.childToggle node col.val child childSeed i)) ∧
    HintEventSlice D (first + sch.m + 1 + sch.m) run ∧
    D.events[first + sch.m + 1 + sch.m + run.length]? = some (.recoverColumn node col.val child) := by
  dsimp only
  let child := hintChildPhysicalIndex children node col
  let childSeed := hintChildSchemeIndex children seed col
  let childOffset := offset + ((List.ofFn fun i => synLen CR (children i)).take col.val).sum
  let predict := (List.range sch.m).map (HintTreeEvent.predict node seed col.val)
  let copy := [HintTreeEvent.childCopy node col.val child childOffset (synLen CR (children col))]
  let toggle := (List.range sch.m).map (HintTreeEvent.childToggle node col.val child childSeed)
  let run := hintTreeEvents CR payloadOffset (children col) child childSeed (payloadOffset child)
  let recover := [HintTreeEvent.recoverColumn node col.val child]
  have hs0 : HintEventSlice D first (predict ++ copy ++ toggle ++ run ++ recover) := hSlice
  have hs : HintEventSlice D first (predict ++ (copy ++ (toggle ++ (run ++ recover)))) := by
    simpa only [List.append_assoc] using hs0
  have hPredLen : predict.length = sch.m := by simp [predict]
  have hCopyLen : copy.length = 1 := rfl
  have hToggleLen : toggle.length = sch.m := by simp [toggle]
  have hPred : HintEventSlice D first predict := hs.left
  have hCopy : HintEventSlice D (first + sch.m) copy := by
    simpa only [hPredLen] using hs.right.left
  have hToggle : HintEventSlice D (first + sch.m + 1) toggle := by
    simpa only [hPredLen, hCopyLen] using hs.right.right.left
  have hRun : HintEventSlice D (first + sch.m + 1 + sch.m) run := by
    simpa only [hPredLen, hCopyLen, hToggleLen] using hs.right.right.right.left
  have hRecover : HintEventSlice D (first + sch.m + 1 + sch.m + run.length) recover := by
    simpa only [hPredLen, hCopyLen, hToggleLen] using hs.right.right.right.right
  refine ⟨?_, ?_, ?_, hRun, ?_⟩
  · intro j hj
    have h := hPred.read j (by rwa [hPredLen])
    have hRange : j < (List.range sch.m).length := by simpa using hj
    simpa only [predict, List.getElem?_map, List.getElem?_eq_getElem hRange,
      List.getElem_range, Option.map_some] using h
  · have h := hCopy.read 0 Nat.zero_lt_one
    rw [Nat.add_zero] at h
    exact h
  · intro i hi
    have h := hToggle.read i (by rwa [hToggleLen])
    have hRange : i < (List.range sch.m).length := by simpa using hi
    simpa only [toggle, List.getElem?_map, List.getElem?_eq_getElem hRange,
      List.getElem_range, Option.map_some] using h
  · have h := hRecover.read 0 Nat.zero_lt_one
    rw [Nat.add_zero] at h
    exact h

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRecursiveColumn_slice
end S_HintRecursiveColumnSlice20261120
section S_HintRecursiveColumnAssemble20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintRecursiveColumn_assemble (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (E : RAMEnv) (header node seed offset first t : ℕ)
    (sch : RowScheme) (Xs Ys : Fin sch.ℓ → ℕ) (children : Fin sch.ℓ → Node)
    (r : (Node.recursive sch t Xs Ys children).Seed) (x J : Finset ℕ) (col : Fin sch.ℓ)
    (payloadOffset : ℕ → ℕ) (keep : (ℕ → ℕ) → Prop) :
    let CR := crFamily S
    let A := D.placement.arena node
    let child := children col
    let childNode := hintChildPhysicalIndex children node col
    let childSeed := hintChildSchemeIndex children seed col
    let B := D.placement.arena childNode
    let childEvents := hintTreeEvents CR payloadOffset child childNode childSeed (payloadOffset childNode)
    let dest := A.transcript + col.val * sch.m
    let parentHints := fun m => HintBitmap m A.hints sch.N J
    let transcript := HintTranscriptCorrect sch r.1 x A.transcript (fun _ s => s.val < col.val)
    let next := HintTranscriptCorrect sch r.1 x A.transcript (fun _ s => s.val < col.val + 1)
    let ready := fun m => parentHints m ∧ transcript m ∧ keep m
    let pred := fun m => HintBitmap m dest sch.m (sch.exactP r.1 x J col)
    let abstain := fun m => HintBitmap m B.hints sch.m (sch.exactHint r.1 x J col)
    let fresh := HintFreshWords B.payload (wordsOf E.W (synLen CR child))
    let raw := HintMemoryWords E.W B.payload (hintSketchVector CR child (r.2 col) (sch.column r.1 x col))
    let input := sch.exactChildInput r.1 x J col
    let packed := HintMemoryWords E.W B.payload (hintSketchVector CR child (r.2 col) input)
    let result := fun m => HintBitmap m B.result sch.m input
    HintDecoderPhase S H D E header first sch.m
      (fun m => ready m ∧ fresh m) (fun m => (ready m ∧ fresh m) ∧ pred m ∧ abstain m) →
    HintDecoderPhase S H D E header (first + sch.m) 1
      (fun m => fresh m ∧ ready m ∧ pred m ∧ abstain m)
      (fun m => raw m ∧ ready m ∧ pred m ∧ abstain m) →
    HintDecoderPhase S H D E header (first + sch.m + 1) sch.m
      (fun m => pred m ∧ raw m ∧ ready m ∧ abstain m)
      (fun m => pred m ∧ packed m ∧ ready m ∧ abstain m) →
    HintDecoderPhase S H D E header (first + sch.m + 1 + sch.m) childEvents.length
      (fun m => packed m ∧ abstain m ∧ pred m ∧ ready m)
      (fun m => result m ∧ pred m ∧ ready m) →
    HintDecoderPhase S H D E header (first + sch.m + 1 + sch.m + childEvents.length) 1
      (fun m => transcript m ∧ pred m ∧ result m ∧ parentHints m ∧ keep m)
      (fun m => next m ∧ parentHints m ∧ keep m) →
    HintDecoderPhase S H D E header first
      (hintRecursiveColumnEvents CR payloadOffset sch children node seed offset col).length
      (fun m => ready m ∧ fresh m) (fun m => parentHints m ∧ next m ∧ keep m) := by
  let CR := crFamily S
  let child := children col
  let childNode := hintChildPhysicalIndex children node col
  let childSeed := hintChildSchemeIndex children seed col
  let run := hintTreeEvents CR payloadOffset child childNode childSeed (payloadOffset childNode)
  dsimp only
  intro predict copy toggle call recover
  have hLen : (hintRecursiveColumnEvents CR payloadOffset sch children node seed offset col).length =
      sch.m + 1 + sch.m + run.length + 1 := by
    simp only [hintRecursiveColumnEvents, List.length_append, List.length_map, List.length_range,
      List.length_cons, List.length_nil, Nat.zero_add]
    rfl
  rw [hLen]
  let copied := predict.append (copy.relabel (fun _ => by tauto) (fun _ => Iff.rfl))
  let toggled := copied.append_at (toggle.relabel (fun _ => by tauto) (fun _ => Iff.rfl))
    (by omega : first + sch.m + 1 = first + (sch.m + 1))
  let decoded := toggled.append_at (call.relabel (fun _ => by tauto) (fun _ => Iff.rfl))
    (by omega : first + sch.m + 1 + sch.m = first + (sch.m + 1 + sch.m))
  exact decoded.append_at (recover.relabel (fun _ => by tauto) (fun _ => by tauto))
    (by change first + sch.m + 1 + sch.m + run.length = first + (sch.m + 1 + sch.m + run.length); omega)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRecursiveColumn_assemble
end S_HintRecursiveColumnAssemble20261120
section S_HintSubtreeArena20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintDecoderTables_payload (S : CRSourceBundle) (H : HintParams)
    {T : Node} (hT : IsSchemeTree H T) (W Bc header node : ℕ) :
    let D := hintDecoderTables S H hT W Bc header
    (D.placement.arena node).payload = hintArenaStart D.heap D.stride node := by
  dsimp only
  let D := hintDecoderTables S H hT W Bc header
  change (hintArenaFor S H W (D.placement.info node) (hintArenaStart D.heap D.stride node)).payload = _
  unfold hintArenaFor
  cases (D.placement.info node).rowParams with
  | none => cases (D.placement.info node).isCR <;> rfl
  | some p => cases p; cases (D.placement.info node).isCR <;> rfl

theorem hintDecoderTables_nodeRange (S : CRSourceBundle) (H : HintParams)
    {T : Node} (hT : IsSchemeTree H T) (W Bc header first count : ℕ) :
    let D := hintDecoderTables S H hT W Bc header
    first + count ≤ D.infos.length →
    ∀ i, first ≤ i → i < first + count →
      hintArenaStart D.heap D.stride first ≤ (D.placement.arena i).payload ∧
        (D.placement.arena i).limit ≤ hintArenaStart D.heap D.stride (first + count) := by
  dsimp only
  let D := hintDecoderTables S H hT W Bc header
  intro hRange i hi hj
  change first + count ≤ D.infos.length at hRange
  let index : Fin D.infos.length := ⟨i, hj.trans_le hRange⟩
  refine ⟨?_, ?_⟩
  · rw [hintDecoderTables_payload S H hT W Bc header i]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left D.stride hi) D.heap
  · exact (hintDecoderTables_arena_fits S H hT W Bc header index).trans
      (hintArenaStart_disjoint D.heap D.stride i (first + count) hj)

theorem hintDecoderTables_rowScratch (S : CRSourceBundle) (H : HintParams)
    {T : Node} (hT : IsSchemeTree H T) (W Bc header N X Y a seed row h : ℕ)
    (ha : a ≤ H.ell N X Y) :
    let D := hintDecoderTables S H hT W Bc header
    ∀ node : Fin D.infos.length,
      D.infos[node.val].universeSize = N →
      D.infos[node.val].rowParams = some (X, Y) →
      (hintRowWorkspace D.placement.rowScratch a (H.Nmax N X Y) (H.BY N X Y) seed row
        (H.ell N X Y) h).gauss.pivotRow + a ≤ D.listBase := by
  dsimp only
  let D := hintDecoderTables S H hT W Bc header
  intro node hN hXY
  change D.infos[node.val].universeSize = N at hN
  change D.infos[node.val].rowParams = some (X, Y) at hXY
  have hIn : hintRowScratchSize H D.infos[node.val] ∈ D.infos.map (hintRowScratchSize H) :=
    List.mem_map.mpr ⟨_, List.getElem_mem node.isLt, rfl⟩
  have hSpace := hintFoldMax_ge (D.infos.map (hintRowScratchSize H)) 0 _ (Or.inl hIn)
  have hStart : D.listBase = D.placement.rowScratch + (D.infos.map (hintRowScratchSize H)).foldl max 0 :=
    rfl
  have hSize : hintRowScratchSize H D.infos[node.val] =
      (hintRowWorkspace 0 (H.ell N X Y) (H.Nmax N X Y) (H.BY N X Y) 0 0
        (H.ell N X Y) (H.Nmax N X Y)).gauss.pivotRow + H.ell N X Y := by
    simp only [hintRowScratchSize, hXY, hN]
  have hLimit := hintRowWorkspace_pivot_bound D.placement.rowScratch a (H.Nmax N X Y)
    (H.BY N X Y) seed row (H.ell N X Y) h ha
  exact hLimit.trans (by rw [hStart, ← hSize]; exact Nat.add_le_add_left hSpace _)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_nodeRange
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_rowScratch
end S_HintSubtreeArena20261120
section S_HintColumnFrames20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem HintBitmap.frame {before after : ℕ → ℕ} {base count : ℕ} {x : Finset ℕ}
    (h : HintBitmap before base count x) (frame : ∀ a < count, after (base + a) = before (base + a)) :
    HintBitmap after base count x :=
  fun i hi => (frame i hi).trans (h i hi)

theorem HintMemoryWords.frame {before after : ℕ → ℕ} {M W base : ℕ} {y : Fin M → ZMod 2}
    (h : HintMemoryWords W base y before)
    (frame : ∀ a < wordsOf W M, after (base + a) = before (base + a)) :
    HintMemoryWords W base y after :=
  fun i hi => (frame i hi).trans (h i hi)

theorem HintFreshWords.frame {before after : ℕ → ℕ} {base count : ℕ}
    (h : HintFreshWords base count before)
    (frame : ∀ a < count, after (base + a) = before (base + a)) :
    HintFreshWords base count after :=
  fun i hi => (frame i hi).trans (h i hi)

theorem HintTranscriptCorrect.frame {sch : RowScheme} {lr : sch.LocalSeed} {x : Finset ℕ}
    {base : ℕ} {read : Fin sch.m → Fin sch.ℓ → Prop} {before after : ℕ → ℕ}
    (h : HintTranscriptCorrect sch lr x base read before)
    (frame : ∀ (j : Fin sch.m) (s : Fin sch.ℓ), read j s →
      after (hintTranscriptCell base sch.m j.val s.val) = before (hintTranscriptCell base sch.m j.val s.val)) :
    HintTranscriptCorrect sch lr x base read after :=
  fun j s hs => (frame j s hs).trans (h j s hs)

theorem hintParentColumn_frame (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (A : HintNodeArena) (col : Fin sch.ℓ) (before after : ℕ → ℕ)
    (scratchStart scratchEnd childStart childEnd : ℕ)
    (hStart : scratchEnd ≤ A.transcript)
    (hTran : A.transcript + sch.ℓ * sch.m ≤ A.hints)
    (hParentEnd : A.hints + sch.N ≤ childStart)
    (hFrame : ∀ a, (a < scratchStart ∨ scratchEnd ≤ a) →
      (a < childStart ∨ childEnd ≤ a) → after a = before a)
    (hHints : HintBitmap before A.hints sch.N J)
    (hTranscript : HintTranscriptCorrect sch lr x A.transcript (fun _ s => s.val < col.val) before)
    (hPred : HintBitmap before (A.transcript + col.val * sch.m) sch.m (sch.exactP lr x J col)) :
    HintBitmap after A.hints sch.N J ∧
      HintTranscriptCorrect sch lr x A.transcript (fun _ s => s.val < col.val) after ∧
      HintBitmap after (A.transcript + col.val * sch.m) sch.m (sch.exactP lr x J col) := by
  have hFrameAt (a : ℕ) (ha : A.transcript ≤ a) (hb : a < A.hints + sch.N) : after a = before a :=
    hFrame a (Or.inr (hStart.trans ha)) (Or.inl (hb.trans_le hParentEnd))
  refine ⟨hHints.frame (fun a ha => hFrameAt _ (by omega) (by omega)), hTranscript.frame ?_, hPred.frame ?_⟩
  · intro j s _
    apply hFrameAt
    · unfold hintTranscriptCell
      omega
    · have ho := hintPairOffset_lt s j
      unfold hintTranscriptCell
      omega
  · intro j hj
    apply hFrameAt
    · omega
    · have ho := hintPairOffset_lt col (⟨j, hj⟩ : Fin sch.m)
      change col.val * sch.m + j < sch.ℓ * sch.m at ho
      omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintParentColumn_frame
end S_HintColumnFrames20261120
section S_HintSubtreeFrame20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintSubtreeFrame (D : HintDecoderTables) (first count : ℕ) (before after : ℕ → ℕ) : Prop :=
  ∀ a, (a < D.placement.rowScratch ∨ D.listBase ≤ a) →
    (a < hintArenaStart D.heap D.stride first ∨ hintArenaStart D.heap D.stride (first + count) ≤ a) →
    after a = before a

def HintSubtreeFresh (D : HintDecoderTables) (first count : ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ a, hintArenaStart D.heap D.stride first ≤ a →
    a < hintArenaStart D.heap D.stride (first + count) → m a = 0

theorem hintArenaStart_mono (start stride : ℕ) : Monotone (hintArenaStart start stride) :=
  fun _ _ h => Nat.add_le_add_left (Nat.mul_le_mul_left stride h) start

theorem HintSubtreeFrame.of_child {D : HintDecoderTables} {first count child childCount : ℕ}
    {before after : ℕ → ℕ} (h : HintSubtreeFrame D child childCount before after)
    (hStart : first ≤ child) (hEnd : child + childCount ≤ first + count) :
    HintSubtreeFrame D first count before after := by
  intro a hScratch hArena
  refine h a hScratch (hArena.imp ?_ ?_)
  · exact fun ha => ha.trans_le (hintArenaStart_mono D.heap D.stride hStart)
  · exact fun ha => (hintArenaStart_mono D.heap D.stride hEnd).trans ha

theorem HintSubtreeFresh.words {D : HintDecoderTables} {first count start words : ℕ} {m : ℕ → ℕ}
    (h : HintSubtreeFresh D first count m)
    (hStart : hintArenaStart D.heap D.stride first ≤ start)
    (hEnd : start + words ≤ hintArenaStart D.heap D.stride (first + count)) :
    HintFreshWords start words m := by
  intro i hi
  exact h (start + i) (hStart.trans (Nat.le_add_right _ _)) (by omega)

theorem HintSubtreeFresh.subrange {D : HintDecoderTables} {first count child childCount : ℕ} {m : ℕ → ℕ}
    (h : HintSubtreeFresh D first count m)
    (hStart : first ≤ child) (hEnd : child + childCount ≤ first + count) :
    HintSubtreeFresh D child childCount m :=
  fun a ha hb => h a ((hintArenaStart_mono D.heap D.stride hStart).trans ha)
    (hb.trans_le (hintArenaStart_mono D.heap D.stride hEnd))

theorem HintSubtreeFresh.after_child {D : HintDecoderTables} {first count child childCount : ℕ}
    {before after : ℕ → ℕ}
    (h : HintSubtreeFresh D first count before) (frame : HintSubtreeFrame D child childCount before after)
    (hScratch : D.listBase ≤ D.heap)
    (hOrder : child + childCount ≤ first) :
    HintSubtreeFresh D first count after := by
  intro a ha hb
  have hAfterScratch : D.listBase ≤ a := hScratch.trans ((Nat.le_add_right _ _).trans ha)
  have hUntouched : hintArenaStart D.heap D.stride (child + childCount) ≤ a :=
    (hintArenaStart_mono D.heap D.stride hOrder).trans ha
  exact (frame a (Or.inr hAfterScratch) (Or.inr hUntouched)).trans (h a ha hb)

theorem HintSubtreeFresh.update_below {D : HintDecoderTables} {first count addr : ℕ} {m : ℕ → ℕ}
    (h : HintSubtreeFresh D first count m) (v : ℕ)
    (hAddr : addr < hintArenaStart D.heap D.stride first) :
    HintSubtreeFresh D first count (Function.update m addr v) := by
  intro a ha hb
  rw [Function.update_of_ne (Nat.ne_of_gt (hAddr.trans_le ha))]
  exact h a ha hb

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintSubtreeFrame.of_child
#print axioms LinearSetReconciliation327.Main.HintSubtreeFresh.after_child
end S_HintSubtreeFrame20261120
section S_HintUpdateAuxBounds20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintNodeInfo_subtree_seed (CR : CRFamily) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (node seed : ℕ) :
    (hintNodeInfo CR hT node seed).subtree = T ∧
      (hintNodeInfo CR hT node seed).seedIndex = seed := by
  cases hT <;> exact ⟨rfl, rfl⟩

theorem hintDecoderTables_updateAux (S : CRSourceBundle) (H : HintParams)
    {R T : Node} (hR : IsSchemeTree H R) (hT : IsSchemeTree H T)
    (E : RAMEnv) (up previous : ℕ → ℕ)
    (W Bc header node seed : ℕ) (hHeader : 3 < header)
    (hDet : E.det = (hintDecoderTables S H hR W Bc header).det S H up previous header R.N) :
    let D := hintDecoderTables S H hR W Bc header
    let A := D.placement.arena node
    let table := D.placement.updateTable node
    let block := hintSubtreeBlock (crFamily S) W D.control Bc T seed A.saveOffset
    HintPlacedSubtree (crFamily S) H D hT node seed →
    block.At E table ∧ table + block.length ≤ hintDecoderDetEnd S H D header := by
  dsimp only
  intro hPlaced
  let D := hintDecoderTables S H hR W Bc header
  let A := D.placement.arena node
  let block := hintSubtreeBlock (crFamily S) W D.control Bc T seed A.saveOffset
  have hIndex : node < D.infos.length := by
    have hs : node + T.nodeCount ≤ D.infos.length := hPlaced.span
    have hp := hintNodeCount_pos T
    omega
  let i : Fin D.infos.length := ⟨node, hIndex⟩
  have hInfo : D.placement.info node = hintNodeInfo (crFamily S) hT node seed :=
    HintPlacedSubtree.info S H hR hT W Bc header node seed hPlaced
  obtain ⟨hSubtree, hSeed⟩ := hintNodeInfo_subtree_seed (crFamily S) H hT node seed
  have hBlocks : D.nodeAux S H Bc node = block :: (D.nodeAux S H Bc node).tail := by
    change hintNodeAuxBlocks S H W D.control Bc (D.placement.info node) A =
      block :: (hintNodeAuxBlocks S H W D.control Bc (D.placement.info node) A).tail
    simp only [hintNodeAuxBlocks, hInfo, hSubtree, hSeed, List.tail_cons]
    rfl
  let j : Fin (D.nodeAux S H Bc i.val).length := ⟨0, by change 0 < (D.nodeAux S H Bc node).length; rw [hBlocks]; simp⟩
  have hb : (D.nodeAux S H Bc i.val)[j.val] = block := by
    have hOpt : (D.nodeAux S H Bc i.val)[j.val]? = some block :=
      congrArg (fun l : List HintDetBlock => l[0]?) hBlocks
    exact Option.some.inj ((List.getElem?_eq_getElem (l := D.nodeAux S H Bc i.val) j.isLt).symm.trans hOpt)
  have hRead := hintDecoderTables_aux_At S H hR E up previous W Bc header hHeader hDet i j
  have hEnd := hintDecoderTables_aux_end S H hR W Bc header i j
  have hAddress : D.placement.updateTable node = D.auxAddress S H Bc header i.val j.val :=
    (hintDecoderTables_aux_addresses S H hR W Bc header node 0).1
  rw [hb] at hRead hEnd
  rw [← hAddress] at hRead hEnd
  exact ⟨hRead, hEnd⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_updateAux
end S_HintUpdateAuxBounds20261120
section S_HintSubtreeReady20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintNodeFreshTail (D : HintDecoderTables) (node count : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ a, (D.placement.arena node).result ≤ a →
    a < hintArenaStart D.heap D.stride (node + count) → mem a = 0

noncomputable def HintSubtreeReady (S : CRSourceBundle) (D : HintDecoderTables)
    (W node : ℕ) (T : Node) (r : T.Seed) (x J : Finset ℕ) (mem : ℕ → ℕ) : Prop :=
  HintMemoryWords W (D.placement.inputWord node) (hintSketchVector (crFamily S) T r x) mem ∧
    HintBitmap mem (D.placement.arena node).hints T.N J ∧ HintNodeFreshTail D node T.nodeCount mem

abbrev HintSubtreePhase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables) (E : RAMEnv)
    (header node seed first : ℕ) (T : Node) (r : T.Seed) (x J : Finset ℕ) :=
  ∀ keep : (ℕ → ℕ) → Prop,
    (∀ m m', HintSubtreeFrame D node T.nodeCount m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first
      (hintTreeEvents (crFamily S) (fun i => D.placement.inputWord i * E.W)
        T node seed (D.placement.inputWord node * E.W)).length
      (fun m => HintSubtreeReady S D E.W node T r x J m ∧ keep m)
      (fun m => HintBitmap m (D.placement.arena node).result T.N x ∧ keep m)

theorem HintNodeFreshTail.frame {D : HintDecoderTables} {node count : ℕ} {m m' : ℕ → ℕ}
    (h : HintNodeFreshTail D node count m)
    (hf : ∀ a, (D.placement.arena node).result ≤ a →
      a < hintArenaStart D.heap D.stride (node + count) → m' a = m a) :
    HintNodeFreshTail D node count m' :=
  fun a hLo hHi => (hf a hLo hHi).trans (h a hLo hHi)

theorem HintNodeFreshTail.update_below {D : HintDecoderTables} {node count addr : ℕ}
    {m : ℕ → ℕ} (h : HintNodeFreshTail D node count m) (v : ℕ)
    (hAddr : addr < (D.placement.arena node).result) :
    HintNodeFreshTail D node count (Function.update m addr v) := by
  apply h.frame
  intro a ha _
  rw [Function.update_of_ne (Nat.ne_of_gt (hAddr.trans_le ha))]

theorem HintNodeFreshTail.words {D : HintDecoderTables} {node count base words : ℕ} {m : ℕ → ℕ}
    (h : HintNodeFreshTail D node count m)
    (hLo : (D.placement.arena node).result ≤ base)
    (hHi : base + words ≤ hintArenaStart D.heap D.stride (node + count)) :
    HintFreshWords base words m :=
  fun i hi => h (base + i) (hLo.trans (Nat.le_add_right _ _)) (by omega)

theorem HintNodeFreshTail.descendants {D : HintDecoderTables} {node count : ℕ} {m : ℕ → ℕ}
    (h : HintNodeFreshTail D node count m)
    (hLo : (D.placement.arena node).result ≤ hintArenaStart D.heap D.stride (node + 1)) :
    HintSubtreeFresh D (node + 1) (count - 1) m := by
  intro a ha hb
  by_cases hc : 0 < count
  · apply h a (hLo.trans ha)
    simpa only [show node + 1 + (count - 1) = node + count by omega] using hb
  · have he : count = 0 := by omega
    simp only [he, Nat.zero_sub, Nat.add_zero] at hb
    exact (Nat.not_lt_of_ge ha hb).elim

theorem hintColumnFrame_afterChild {D : HintDecoderTables}
    {node child count : ℕ} {sch : RowScheme} {lr : sch.LocalSeed} {x J : Finset ℕ}
    (col : Fin sch.ℓ) {before after : ℕ → ℕ}
    (hScratch : D.listBase ≤ (D.placement.arena node).transcript)
    (hTran : (D.placement.arena node).transcript + sch.ℓ * sch.m ≤ (D.placement.arena node).hints)
    (hBefore : (D.placement.arena node).hints + sch.N ≤ hintArenaStart D.heap D.stride child)
    (hf : HintSubtreeFrame D child count before after)
    (hHints : HintBitmap before (D.placement.arena node).hints sch.N J)
    (hTranscript : HintTranscriptCorrect sch lr x (D.placement.arena node).transcript
      (fun _ s => s.val < col.val) before)
    (hPred : HintBitmap before ((D.placement.arena node).transcript + col.val * sch.m)
      sch.m (sch.exactP lr x J col)) :
    HintBitmap after (D.placement.arena node).hints sch.N J ∧
      HintTranscriptCorrect sch lr x (D.placement.arena node).transcript
        (fun _ s => s.val < col.val) after ∧
      HintBitmap after ((D.placement.arena node).transcript + col.val * sch.m)
        sch.m (sch.exactP lr x J col) :=
  hintParentColumn_frame sch lr x J (D.placement.arena node) col before after
    D.placement.rowScratch D.listBase (hintArenaStart D.heap D.stride child)
    (hintArenaStart D.heap D.stride (child + count)) hScratch hTran hBefore hf hHints hTranscript hPred

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintNodeFreshTail.descendants
#print axioms LinearSetReconciliation327.Main.hintColumnFrame_afterChild
end S_HintSubtreeReady20261120
section S_HintPhaseEndpoints20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintDecoderPhase.adapt {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header first count : ℕ} {A B A' B' : (ℕ → ℕ) → Prop}
    (p : HintDecoderPhase S H D E header first count A B) (hCount : 0 < count)
    (pre : ∀ m, A' m → A m) (post : ∀ m, B m → B' m)
    (cursorPre : ∀ m v, A' m → A' (Function.update m (D.control + 2) v))
    (cursorPost : ∀ m v, B' m → B' (Function.update m (D.control + 2) v)) :
    HintDecoderPhase S H D E header first count A' B' := by
  let inv := fun i => if i = 0 then A' else if i = count then B' else p.inv i
  refine ⟨p.budget, inv, ?_, ?_, ?_, ?_⟩
  · intro m
    simp [inv]
  · intro m
    simp [inv, Nat.ne_of_gt hCount]
  · intro i m v h
    by_cases hz : i = 0
    · simpa only [inv, if_pos hz] using cursorPre m v (by simpa only [inv, if_pos hz] using h)
    by_cases hc : i = count
    · simpa only [inv, if_neg hz, if_pos hc] using cursorPost m v
        (by simpa only [inv, if_neg hz, if_pos hc] using h)
    · simpa only [inv, if_neg hz, if_neg hc] using p.cursor i m v
        (by simpa only [inv, if_neg hz, if_neg hc] using h)
  · intro i hi j hj
    apply (p.step i hi j hj).mono le_rfl
    · intro m hm
      by_cases hz : i = 0
      · subst i
        exact (p.start m).2 (pre m (by simpa only [inv, if_pos rfl] using hm))
      · simpa only [inv, if_neg hz, if_neg (Nat.ne_of_lt hi)] using hm
    · intro m hm
      by_cases hc : i + 1 = count
      · have h := post m ((p.stop m).mp (hc ▸ hm))
        simpa only [inv, if_neg (Nat.succ_ne_zero i), if_pos hc] using h
      · simpa only [inv, if_neg (Nat.succ_ne_zero i), if_neg hc] using hm

theorem hintChildIndexAt_succ {arity : ℕ} (children : Fin arity → Node)
    (node : ℕ) (col : Fin arity) :
    node + 1 + ((List.ofFn fun i => (children i).nodeCount).take (col.val + 1)).sum =
      hintChildPhysicalIndex children node col + (children col).nodeCount := by
  let counts := List.ofFn fun i => (children i).nodeCount
  have hc : col.val < counts.length := by simp [counts]
  have hv : counts[col.val] = (children col).nodeCount := by simp [counts]
  change node + 1 + (counts.take (col.val + 1)).sum =
    node + 1 + (counts.take col.val).sum + (children col).nodeCount
  rw [hintTakeSum_succ counts col.val hc, hv] <;> omega

theorem hintTreeEvents_pos (CR : CRFamily) (offsets : ℕ → ℕ) (T : Node)
    (node seed offset : ℕ) : 0 < (hintTreeEvents CR offsets T node seed offset).length := by
  cases T <;> simp [hintTreeEvents, hintResidualEvents] <;> omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintDecoderPhase.adapt
#print axioms LinearSetReconciliation327.Main.hintTreeEvents_pos
end S_HintPhaseEndpoints20261120
section S_HintPhaseExists20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def HintDecoderPhase.existsParam {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header first count : ℕ}
    {α : Type} [Fintype α] [DecidableEq α]
    {A B : α → (ℕ → ℕ) → Prop} (p : ∀ a, HintDecoderPhase S H D E header first count (A a) (B a)) :
    HintDecoderPhase S H D E header first count (fun m => ∃ a, A a m) (fun m => ∃ a, B a m) := by
  let budget := fun i => (Finset.univ : Finset α).sup (fun a => (p a).budget i)
  let inv := fun i m => ∃ a, (p a).inv i m
  refine ⟨budget, inv, ?_, ?_, ?_, ?_⟩
  · intro m
    exact exists_congr (fun a => (p a).start m)
  · intro m
    exact exists_congr (fun a => (p a).stop m)
  · rintro i m v ⟨a, h⟩
    exact ⟨a, (p a).cursor i m v h⟩
  · intro i hi j hj act base state
    dsimp only
    intro hSelect hEntry hAt hPc hArg hCtx hWord hInv hRecord
    obtain ⟨a, ha⟩ := hInv
    have h := (p a).step i hi j hj act base state hSelect hEntry hAt hPc hArg hCtx hWord ha hRecord
    apply Sem.mono h
    rintro k out ⟨hk, ho, hc, hf⟩
    exact ⟨hk.trans (Finset.le_sup (f := fun b => (p b).budget i) (Finset.mem_univ a)), ⟨a, ho⟩, hc, hf⟩

theorem HintDecoderPhase.existsParam_budget_le {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header first count : ℕ}
    {α : Type} [Fintype α] [DecidableEq α]
    {A B : α → (ℕ → ℕ) → Prop}
    (p : ∀ a, HintDecoderPhase S H D E header first count (A a) (B a))
    (i limit : ℕ) (h : ∀ a, (p a).budget i ≤ limit) :
    (HintDecoderPhase.existsParam p).budget i ≤ limit :=
  Finset.sup_le fun a _ => h a

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintDecoderPhase.existsParam
end S_HintPhaseExists20261120


