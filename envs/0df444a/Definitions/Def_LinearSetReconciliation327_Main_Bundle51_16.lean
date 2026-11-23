-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_16
-- name    : LinearSetReconciliation327_Main_Bundle51_16
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T09:13:07.701151+00:00
-- url     : https://prove2.me/theorems/0776c9f8-f064-4ef3-a624-b616be8ddff5
-- title:
--   LinearSetReconciliation327 鈥?Bundle51_16
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_16` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintRowSizeBounds20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintUpdatePrepared20261120
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_08
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_12
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_13
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_14
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_15

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_16
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintBinaryRun20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedBinaryRoot20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedTreeBudget20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintTreeCountActual20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDecoderTableCap20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintArenaCap20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintTreeResourceCaps20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintNodeResources20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintNodeAuxCap20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPolynomialWord20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintNodeWordCaps20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintWidthResources20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintActualNodeInfo20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintCRNodeCostCap20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintActualWidthResources20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintScalarResources20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintActualDecoderLimits20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRowCostExp20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintActualRowCost20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintCombinedTime20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintScheduledCost20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintTimeScalars20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintTreeTimeCaps20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- inlined Definitions.Def_LinearSetReconciliation327_Main_HintPlacedBinaryTree20261120
-- inlined copy of Definitions.Def_LinearSetReconciliation327_Main_HintPlacedBinaryTree20261120 (declaration text unchanged)
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

private theorem hintPlaced_cursorBounds {D : HintDecoderTables} {W node count N M : ℕ}
    (g : HintPlacedMemory D W node count N M) :
    D.control + 2 < (D.placement.arena node).hints ∧ D.control + 2 < (D.placement.arena node).result := by
  let A := D.placement.arena node
  have hHeap : D.heap ≤ A.payload := g.payload ▸ Nat.le_add_right _ _
  have hHints : D.control + 2 < A.hints :=
    g.scratch.trans_le (g.list.trans (g.heap.trans (hHeap.trans (g.transcript.trans g.hints))))
  exact ⟨hHints, hHints.trans_le ((Nat.le_add_right _ _).trans g.result.le)⟩

private noncomputable def hintBinarySubtree_ofBitmaps {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header node seed first : ℕ} {T : Node}
    (g : HintPlacedMemory D E.W node T.nodeCount T.N (synLen (crFamily S) T))
    (p : ∀ (J : Finset ℕ) (keep : (ℕ → ℕ) → Prop),
      (∀ m m', HintSubtreeFrame D node T.nodeCount m m' → keep m → keep m') →
      (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
      HintDecoderPhase S H D E header first
        (hintTreeEvents (crFamily S) (fun a => D.placement.inputWord a * E.W)
          T node seed (D.placement.inputWord node * E.W)).length
        (fun m => (HintBitmap m (D.placement.arena node).hints T.N J ∧ HintNodeFreshTail D node T.nodeCount m) ∧ keep m)
        (fun m => HintBinaryMemory m (D.placement.arena node).result T.N ∧ keep m)) :
    HintBinarySubtreePhase S H D E header node seed first T := by
  intro keep hKeep hCursor
  let A := D.placement.arena node
  let offsets := fun a => D.placement.inputWord a * E.W
  let count := (hintTreeEvents (crFamily S) offsets T node seed (offsets node)).length
  let tail := HintNodeFreshTail D node T.nodeCount
  let post := fun m => HintBinaryMemory m A.result T.N ∧ keep m
  let q (J : Finset ℕ) : HintDecoderPhase S H D E header first count
      (fun m => HintBitmap m A.hints T.N J ∧ tail m ∧ keep m) post :=
    (p J keep hKeep hCursor).relabel (fun _ => by tauto) (fun _ => Iff.rfl)
  obtain ⟨hHints, hResult⟩ := hintPlaced_cursorBounds g
  let run := HintDecoderPhase.binaryHintParam q (hintTreeEvents_pos (crFamily S) offsets T node seed (offsets node))
    hHints (fun m v h => ⟨h.1.update_below v hResult, hCursor m v h.2⟩)
    (fun m v h => ⟨h.1.update_below v hResult, hCursor m v h.2⟩)
  exact run.relabel (fun _ => by unfold HintBinarySubtreeReady; tauto) (fun _ => Iff.rfl)

noncomputable def hintDecodePlacedTree_total (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (seedData : (hintSpec R).Seed)
    (up previous : ℕ → ℕ) (W Bc header : ℕ)
    (hHeader : 3 < header) (hW : 0 < W) (hWord : 30 < 2 ^ W) (hBc : Bc + 1 < 2 ^ W)
    (hFit : (hintSpec R).Fits W) (hSeeds : (schemeNodes R).length < 2 ^ W)
    (T : Node) (hT : IsSchemeTree H T) :
    let CR := crFamily S
    let D := hintDecoderTables S H hR W Bc header
    let E := (hintSpec R).env W (D.det S H up previous header R.N) seedData
    let offsets := fun i => D.placement.inputWord i * W
    hintArenaStart D.heap D.stride D.infos.length * W < 2 ^ W →
    hintDecoderDetEnd S H D header < 2 ^ W →
    HintTreeLimits S H W Bc hT →
    ∀ (node seed first X Y : ℕ),
      0 < T.N → Node.WF T X Y →
      BlockOf R seed (schemeNodes T) → seed + (schemeNodes T).length ≤ (schemeNodes R).length →
      HintPlacedSubtree CR H D hT node seed →
      (node = 0 → synLen CR T ≤ synLen CR R) →
      HintEventSlice D first (hintTreeEvents CR offsets T node seed (offsets node)) →
      HintBinarySubtreePhase S H D E header node seed first T := by
  let CR := crFamily S
  let D := hintDecoderTables S H hR W Bc header
  let E := (hintSpec R).env W (D.det S H up previous header R.N) seedData
  let offsets := fun i => D.placement.inputWord i * W
  dsimp only
  intro hMem hDet
  induction hT with
  | store N =>
    intro _ node seed first _ _ _ _ _ _ hp hRoot hs keep hKeep hCursor
    let g := hintDecoderTables_placedMemory S H hR (.store N) W Bc header node seed hp hRoot
    obtain ⟨hHints, hResult⟩ := hintPlaced_cursorBounds g
    let p := hintPlacedStore_total S H hR E W Bc header node seed first N rfl hW
      (by omega) hp hRoot hMem hDet hs keep hKeep hCursor
    refine p.adapt Nat.zero_lt_one (fun _ h => h.2) (fun _ h => h) ?_ ?_
    · rintro m v ⟨⟨hh, hf⟩, hk⟩
      exact ⟨⟨hh.update_below v hHints, hf.update_below v hResult⟩, hCursor m v hk⟩
    · rintro m v ⟨hb, hk⟩
      exact ⟨hb.update_below v hResult, hCursor m v hk⟩
  | cr N t =>
    intro hSmall node seed first X Y hN hWF _ _ hp hRoot hs keep hKeep hCursor
    have hw : t ≤ N ∧ min N (X + Y) ≤ t := hWF
    let g := hintDecoderTables_placedMemory S H hR (.cr N t) W Bc header node seed hp hRoot
    obtain ⟨hHints, hResult⟩ := hintPlaced_cursorBounds g
    let p := hintPlacedCR_total S H hR E up previous W Bc header node seed first N t hHeader rfl hW
      (by omega) hSmall hN hw.1 rfl hp hRoot hMem hDet hs keep hKeep hCursor
    refine p.adapt Nat.zero_lt_one (fun _ h => ⟨h.1.2, h.2⟩) (fun _ h => h) ?_ ?_
    · rintro m v ⟨⟨hh, hf⟩, hk⟩
      exact ⟨⟨hh.update_below v hHints, hf.update_below v hResult⟩, hCursor m v hk⟩
    · rintro m v ⟨hb, hk⟩
      exact ⟨hb.update_below v hResult, hCursor m v hk⟩
  | direct N X Y t =>
    intro h node seed first _ _ _ hWF hBlock hSeed hp hRoot hs
    have h : HintRowLimits S H W Bc N X Y t := h
    have hSeed' : seed < 2 ^ W := by omega
    let g := hintDecoderTables_placedMemory S H hR (.direct N X Y t) W Bc header node seed hp hRoot
    exact hintBinarySubtree_ofBitmaps g (fun J =>
      hintPlacedDirect_total S H hR seedData up previous W Bc header node seed first N X Y t J
        hHeader hW hWord hBc hFit hSeed' h.keys h.cols h.hx h.hy h.rows_pos h.rows_size h.cols_pos
        hWF h.cr h.cr_columns hBlock hp hRoot hMem hDet hs)
  | recursive N X Y t Xs Ys children hc ih =>
    intro h node seed first _ _ _ hWF hBlock hSeed hp hRoot hs
    let sch := H.scheme N X Y
    let T := Node.recursive sch t Xs Ys children
    let hT : IsSchemeTree H T := .recursive N X Y t Xs Ys children hc
    change HintRowLimits S H W Bc N X Y t ∧ ∀ c,
      UpDimsBound (2 ^ W - 1) (children c) ∧
      UpTreeStatic CR Bc (children c).N (children c) ∧ HintTreeLimits S H W Bc (hc c) at h
    change t ≤ N ∧ ∀ c, (children c).N = sch.m ∧ Node.WF (children c) (Xs c) (Ys c) at hWF
    have hSeed' : seed < 2 ^ W := by omega
    have hKidSeed (col : Fin sch.ℓ) :
        hintChildSchemeIndex children seed col + (schemeNodes (children col)).length ≤ (schemeNodes R).length :=
      (hintChildSchemeIndex_end children Xs Ys t seed col).trans hSeed
    let g := hintDecoderTables_placedMemory S H hR hT W Bc header node seed hp hRoot
    refine hintBinarySubtree_ofBitmaps g (fun J =>
      hintPlacedRecursive_total S H hR seedData up previous W Bc header node seed first N X Y t Xs Ys children hc
        J hHeader hW hWord hBc hFit hSeed' h.1.keys h.1.cols h.1.hx h.1.hy
        h.1.rows_pos h.1.rows_size h.1.cols_pos hWF.1 (fun c => (hWF.2 c).1)
        (fun c => (h.2 c).1) (fun c => (h.2 c).2.1) (fun c => (hKidSeed c).trans_lt hSeeds)
        h.1.cr h.1.cr_columns hBlock hp hRoot hMem hDet hs ?_)
    intro col start
    dsimp only
    intro hChildSlice
    let cn := hintChildPhysicalIndex children node col
    let cs := hintChildSchemeIndex children seed col
    have hCN : 0 < (children col).N := (hWF.2 col).1.symm ▸ h.1.rows_pos
    have hCBlock : BlockOf R cs (schemeNodes (children col)) := BlockOf_child hBlock col
    have hCPlaced := HintPlacedSubtree.child hp col
    have hNZ : cn ≠ 0 := by unfold cn hintChildPhysicalIndex; omega
    exact ih col (h.2 col).2.2 cn cs start (Xs col) (Ys col) hCN (hWF.2 col).2
      hCBlock (hKidSeed col) hCPlaced (fun hz => (hNZ hz).elim) hChildSlice

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecodePlacedTree_total
end -- inlined LinearSetReconciliation327_Main_HintPlacedBinaryTree20261120

section -- Def_LinearSetReconciliation327_Main_HintBinaryRun20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintNativeRoot_total (S : CRSourceBundle) (E : RAMEnv) (state : RAMState)
    (header control hintMap resultMap listBase table N : ℕ) (events : List (ℕ × ℕ))
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop)
    (hdr : HintRootHeader E header control hintMap resultMap listBase table events.length N)
    (hPc : state.pc = 0) (hWordState : UpWordState E state)
    (hSource : state.regs 1 < 2 ^ E.W) (hLength : state.regs 2 < 2 ^ E.W)
    (hSpan : state.regs 1 + min (state.regs 2) N ≤ 2 ^ E.W)
    (hSeparate : state.regs 1 + min (state.regs 2) N ≤ hintMap ∨ hintMap + N < state.regs 1)
    (hControl : control + 2 ≤ hintMap ∨ hintMap + N < control)
    (hOut : listBase + N ≤ resultMap) (hOutSpan : resultMap + N ≤ 2 ^ E.W)
    (hTable : HintDispatchTable E table events)
    (hTags : ∀ j : Fin events.length, events[j.val].1 < (hintNativeActions S).length)
    (hInit : ∀ mem,
      (∀ q < N, mem (hintMap + q) = hintStampValue E (state.regs 1) (min (state.regs 2) N) state.mem q) →
      (∀ address, (address < hintMap ∨ hintMap + N < address) →
        address ≠ control → address ≠ control + 1 → mem address = state.mem address) → I 0 mem)
    (hCursor : ∀ n mem cursor, I n mem → I n (Function.update mem (control + 2) cursor))
    (hActions : HintLocatedActions (hintNativeProgram S) E control table 75 (hintNativeActions S) events budget I)
    (hFinal : ∀ mem, I events.length mem → ∃ accept : ℕ → Bool, ∀ q < N, mem (resultMap + q) = if accept q then 1 else 0) :
    Sem (hintNativeProgram S) E 0 (hintNativeRoot S).len state (fun k out =>
      k ≤ hintDispatchBudget (hintNativeActions S) events.length budget + 29 * N + 67 ∧
      ∃ accept : ℕ → Bool, outList out = hintGatherList accept N) := by
  let P := hintNativeProgram S
  let actions := hintNativeActions S
  let dispatch := hintDispatchStmt actions
  obtain ⟨hEnterAt, hRestAt⟩ := At.seqStmt (hintNativeRoot_at S)
  change At P 0 (hintRootEnter.compile 0) at hEnterAt
  change At P 56 ((Stmt.seq dispatch hintRootExit).compile 56) at hRestAt
  obtain ⟨hDispatchAt, hExitAt⟩ := At.seqStmt hRestAt
  change At P 56 (dispatch.compile 56) at hDispatchAt
  change At P (56 + dispatch.len) (hintRootExit.compile (56 + dispatch.len)) at hExitAt
  obtain ⟨_, ke, first, hRunFirst, hFirstPc, hFirstCost, hData, hHints, hFrame⟩ :=
    hintRootEnter_sem P E state header control hintMap resultMap listBase table events.length N 0
      hdr hSource hLength hSpan hSeparate hControl hEnterAt hPc
  have hWord := hdr.word
  have hWordFirst : UpWordState E first := hRunFirst ▸ upIterate_word_bound P E state ke hWordState
  obtain ⟨_, kd, middle, hRunDispatch, hMiddlePc, hDispatchCost, hInv, _⟩ :=
    hintLocatedDispatch_sem P E first control table 56 (first.mem (control + 2))
      actions events budget I (by omega) hdr.control_span hdr.count_fit hTable hTags hData
      (hInit _ hHints hFrame) hWordFirst hCursor hActions hDispatchAt hFirstPc
  obtain ⟨accept, hm⟩ := hFinal _ hInv
  obtain ⟨_, ko, out, hRunExit, hEnd, hExitCost, hList, _⟩ :=
    hintRootExit_sem P E middle header control hintMap resultMap listBase table events.length N
      (56 + dispatch.len) hdr hOut hOutSpan accept hm hExitAt hMiddlePc
  refine ⟨hPc, ko + (kd + ke), out, hintIterate_then (step P E)
    (hintIterate_then (step P E) hRunFirst hRunDispatch) hRunExit, ?_, ?_, accept, hList⟩
  · change out.pc = 56 + (dispatch.len + 25)
    omega
  · change ko + (kd + ke) ≤ hintDispatchBudget actions events.length budget + 29 * N + 67
    omega

theorem hintRunPlacedPhase_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header N : ℕ) (up previous : ℕ → ℕ)
    {M : ℕ} (y : Fin M → ZMod 2) (hints : List ℕ)
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
    (∀ m, after m → ∃ accept : ℕ → Bool, ∀ q < N, m (A.result + q) = if accept q then 1 else 0) →
    ∃ out, HaltsWithin (hintNativeProgram S) E
      (hintPhaseRunBudget S D.events.length N phase.budget) start out := by
  let A := D.placement.arena 0
  let start := decoderStart E.W y hints
  let events := hintTreeEntries header D.events (hintEventRecord S H D.placement)
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
  have hRoot := hintNativeRoot_total S E start header D.control A.hints A.result D.listBase (header + 16) N
    events phase.budget phase.inv hHdr rfl hState (hState.1 1) (hState.1 2)
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
      intro m hi
      have hEnd : after m := (phase.stop m).mp (by simpa only [events, hintTreeEntries_length] using hi)
      exact hFinish m hEnd)
  obtain ⟨_, k, out, hExec, hPc, hTime, _⟩ := hRoot
  refine ⟨out, k, ?_, hExec, hintNativeRoot_halt S out hPc⟩
  have hTime' : k ≤ hintPhaseRunBudget S D.events.length N phase.budget := by
    simpa only [hintPhaseRunBudget, events, hintTreeEntries_length] using hTime
  exact_mod_cast hTime'

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintNativeRoot_total
#print axioms LinearSetReconciliation327.Main.hintRunPlacedPhase_total
end -- Def_LinearSetReconciliation327_Main_HintBinaryRun20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedBinaryRoot20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintPlacedTreeRoot_total (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (seedData : (hintSpec T).Seed) (up previous : ℕ → ℕ)
    (W Bc header X Y : ℕ) (hLimits : HintDecoderLimits S H hT W Bc header)
    (hN : 0 < T.N) (hWF : Node.WF T X Y) :
    let D := hintDecoderTables S H hT W Bc header
    let E := (hintSpec T).env W (D.det S H up previous header T.N) seedData
    HintDecoderPhase S H D E header 0 D.events.length
      (HintBinarySubtreeReady D 0 T.nodeCount T.N)
      (fun m => HintBinaryMemory m (D.placement.arena 0).result T.N) := by
  let D := hintDecoderTables S H hT W Bc header
  let E := (hintSpec T).env W (D.det S H up previous header T.N) seedData
  have hs : HintEventSlice D 0 (hintTreeEvents (crFamily S) (fun i => D.placement.inputWord i * W) T 0 0
      (D.placement.inputWord 0 * W)) := by
    rw [show D.placement.inputWord 0 = 0 from rfl, Nat.zero_mul]
    exact HintEventSlice.root S H hT W Bc header
  let p := hintDecodePlacedTree_total S H hT seedData up previous W Bc header hLimits.anchor hLimits.width
    hLimits.word hLimits.bc hLimits.fits hLimits.seeds T hT hLimits.memory hLimits.table hLimits.nodes
    0 0 0 X Y hN hWF (blockOf_self T) (by simp)
    (HintPlacedSubtree.root S H hT W Bc header) (fun _ => le_rfl) hs
    (fun _ => True) (by simp) (by simp)
  change HintDecoderPhase S H D E header 0 D.events.length _ _
  have he : D.events = hintTreeEvents (crFamily S) (fun i => D.placement.inputWord i * W) T 0 0
      (D.placement.inputWord 0 * W) := by
    rw [show D.placement.inputWord 0 = 0 from rfl, Nat.zero_mul]
    exact hintDecoderTables_events S H hT W Bc header
  rw [he]
  exact p.relabel (fun _ => ⟨And.left, fun h => ⟨h, trivial⟩⟩) (fun _ => ⟨And.left, fun h => ⟨h, trivial⟩⟩)

theorem hintPlacedTree_start_total (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (seedData : (hintSpec T).Seed) (up previous : ℕ → ℕ)
    (W Bc header X Y : ℕ) (y : Fin (synLen (crFamily S) T) → ZMod 2) (J : List ℕ) (hLimits : HintDecoderLimits S H hT W Bc header)
    (hN : 0 < T.N) (hWF : Node.WF T X Y)
    (hDistinct : J.Nodup) (hHints : ∀ j ∈ J, j < T.N) :
    let D := hintDecoderTables S H hT W Bc header
    let E := (hintSpec T).env W (D.det S H up previous header T.N) seedData
    let phase := hintPlacedTreeRoot_total S H hT seedData up previous W Bc header X Y hLimits
      hN hWF
    ∃ out, HaltsWithin (hintNativeProgram S) E (hintPhaseRunBudget S D.events.length T.N phase.budget)
      (decoderStart W y J) out := by
  let D := hintDecoderTables S H hT W Bc header
  let A := D.placement.arena 0
  let arena := hintArenaStart D.heap D.stride
  let E := (hintSpec T).env W (D.det S H up previous header T.N) seedData
  let M := synLen (crFamily S) T
  let phase := hintPlacedTreeRoot_total S H hT seedData up previous W Bc header X Y hLimits
    hN hWF
  have hP := HintPlacedSubtree.root S H hT W Bc header
  have g := hintDecoderTables_placedMemory S H hT hT W Bc header 0 0 hP (fun _ => le_rfl)
  have hCtrl : D.control = wordsOf W M + T.N := rfl
  have hOut : A.hints + T.N < A.result := g.result
  have hAEnd : A.result + T.N < A.limit := g.limit
  have hAWord : A.limit < 2 ^ W := by
    have hMem : arena D.infos.length * W < 2 ^ W := hLimits.memory
    have hSpan : 0 + T.nodeCount ≤ D.infos.length := hP.span
    have hh := Nat.mul_le_mul_left (arena D.infos.length) (show 1 ≤ W from hLimits.width)
    rw [Nat.mul_one] at hh
    exact (g.own.trans (g.finish.trans ((hintArenaStart_mono D.heap D.stride hSpan).trans hh))).trans_lt hMem
  have hHeap : D.listBase + T.N = D.heap := rfl
  have hStart : D.heap ≤ A.payload := g.payload ▸ Nat.le_add_right _ _
  have hBase : D.listBase + T.N ≤ A.result :=
    hHeap ▸ hStart.trans (g.transcript.trans (g.hints.trans ((Nat.le_add_right _ _).trans hOut.le)))
  have hSep : D.control + 2 < A.hints :=
    g.scratch.trans_le (g.list.trans (g.heap.trans (hStart.trans (g.transcript.trans g.hints))))
  have hNFit : T.N < 2 ^ W := by omega
  have hWords : wordsOf W M < 2 ^ W := by omega
  have hJ := hintLength_le_of_valid J T.N hDistinct hHints
  exact hintRunPlacedPhase_total S H D E header T.N up previous y J _ _ phase
    hLimits.anchor rfl (show 15 < 2 ^ W by have := hLimits.word; omega) hLimits.width hLimits.table
    hDistinct hHints hNFit hWords (show wordsOf W M + T.N ≤ A.hints by omega) hSep
    (show A.hints + T.N < 2 ^ W by omega) hBase (show A.result < 2 ^ W by omega)
    (show A.result + T.N ≤ 2 ^ W by omega)
    (by
      intro m hHintsMap hFrame
      have frame (a : ℕ) (ha : a < A.hints ∨ A.hints + T.N < a)
          (h0 : a ≠ D.control) (h1 : a ≠ D.control + 1) : m a = (decoderStart W y J).mem a :=
        hFrame a ha h0 h1
      change HintBinarySubtreeReady D 0 T.nodeCount T.N m
      refine ⟨HintBinaryMemory.of_bitmap hHintsMap, ?_⟩
      intro a ha _
      change A.result ≤ a at ha
      rw [frame a (Or.inr (by omega)) (by omega) (by omega)]
      exact hintDecoderStart_fresh W y J _ (by change wordsOf W M + J.length ≤ a; omega))
    (by
      intro m hBinary
      refine ⟨fun q => decide (m (A.result + q) = 1), ?_⟩
      intro q hq
      change m (A.result + q) = if decide (m (A.result + q) = 1) then 1 else 0
      have hb := hBinary q hq
      change m (A.result + q) < 2 at hb
      by_cases h : m (A.result + q) = 1
      · simp [h]
      · have hz : m (A.result + q) = 0 := by omega
        simp [hz])

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedTree_start_total
end -- Def_LinearSetReconciliation327_Main_HintPlacedBinaryRoot20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedTreeBudget20261120
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearSetReconciliation327.Main

def HintTreeTimeBounds (S : CRSourceBundle) (H : HintParams) (Bc U radius base extra : ℕ) :
    {T : Node} → IsSchemeTree H T → Prop
  | _, .store N => 12 * N + 12 ≤ extra
  | _, .cr N t => hintCRNodeBudget S N t ≤ extra
  | _, .direct N X Y t => HintRowTimeBounds S H N X Y t Bc U radius base extra
  | _, .recursive N X Y t _ _ children hc =>
    HintRowTimeBounds S H N X Y t Bc U radius base extra ∧
    11 * (H.scheme N X Y).m + 11 ≤ extra ∧
    ∀ col, (17 * synLen (crFamily S) (children col) + 13 ≤ extra) ∧
      (147 * (1 + upRest Bc (children col)) + 24 ≤ base) ∧ HintTreeTimeBounds S H Bc U radius base extra (hc col)



private theorem hintBinarySubtreeFromBitmaps_budget_follows {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header node seed first : ℕ} {T : Node}
    (g : HintPlacedMemory D E.W node T.nodeCount T.N (synLen (crFamily S) T))
    (p : ∀ (J : Finset ℕ) (keep : (ℕ → ℕ) → Prop),
      (∀ m m', HintSubtreeFrame D node T.nodeCount m m' → keep m → keep m') →
      (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
      HintDecoderPhase S H D E header first
        (hintTreeEvents (crFamily S) (fun a => D.placement.inputWord a * E.W)
          T node seed (D.placement.inputWord node * E.W)).length
        (fun m => (HintBitmap m (D.placement.arena node).hints T.N J ∧ HintNodeFreshTail D node T.nodeCount m) ∧ keep m)
        (fun m => HintBinaryMemory m (D.placement.arena node).result T.N ∧ keep m)) (cap : HintTreeEvent → ℕ)
    (hp : ∀ J keep hKeep hCursor, HintBudgetFollows D.events first
      (hintTreeEvents (crFamily S) (fun a => D.placement.inputWord a * E.W)
        T node seed (D.placement.inputWord node * E.W)).length (p J keep hKeep hCursor).budget cap) :
    (hintBinarySubtree_ofBitmaps g p).BudgetFollows cap := by
  intro keep hKeep hCursor
  unfold hintBinarySubtree_ofBitmaps
  with_unfolding_all simp only [HintDecoderPhase.binaryHintParam, id, hintAndRec_value, HintDecoderPhase.adapt_budget_eq, HintDecoderPhase.relabel_budget_eq]
  apply HintDecoderPhase.existsParam_budget_follows
  intro J
  with_unfolding_all simp only [HintDecoderPhase.relabel_budget_eq]
  exact hp _ keep hKeep hCursor

theorem hintDecodePlacedTree_total_budget_follows (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (seedData : (hintSpec R).Seed)
    (up previous : ℕ → ℕ) (W Bc header : ℕ)
    (hHeader : 3 < header) (hW : 0 < W) (hWord : 30 < 2 ^ W) (hBc : Bc + 1 < 2 ^ W)
    (hFit : (hintSpec R).Fits W) (hSeeds : (schemeNodes R).length < 2 ^ W)
    (T : Node) (hT : IsSchemeTree H T) (U radius base extra : ℕ) (hRead : 24 ≤ base) :
    let CR := crFamily S
    let D := hintDecoderTables S H hR W Bc header
    let offsets := fun i => D.placement.inputWord i * W
    ∀ (hMem : hintArenaStart D.heap D.stride D.infos.length * W < 2 ^ W)
      (hDet : hintDecoderDetEnd S H D header < 2 ^ W)
      (hLimits : HintTreeLimits S H W Bc hT)
      (node seed first X Y : ℕ)
      (hN : 0 < T.N) (hWF : Node.WF T X Y)
      (hBlock : BlockOf R seed (schemeNodes T)) (hSeed : seed + (schemeNodes T).length ≤ (schemeNodes R).length)
      (hp : HintPlacedSubtree CR H D hT node seed)
      (hRoot : node = 0 → synLen CR T ≤ synLen CR R)
      (hSlice : HintEventSlice D first (hintTreeEvents CR offsets T node seed (offsets node))),
      HintTreeTimeBounds S H Bc U radius base extra hT →
      (hintDecodePlacedTree_total S H hR seedData up previous W Bc header hHeader hW hWord hBc hFit hSeeds
        T hT hMem hDet hLimits node seed first X Y hN hWF hBlock hSeed hp hRoot hSlice).BudgetFollows
        (fun e => base + (if e.linearWork then extra else 0)) := by
  let CR := crFamily S
  let D := hintDecoderTables S H hR W Bc header
  let offsets := fun i => D.placement.inputWord i * W
  dsimp only
  intro hMem hDet
  induction hT with
  | store N =>
    intro hLimits node seed first X Y hN hWF hBlock hSeed hp hRoot hs hCost keep hKeep hCursor i hi e he
    change i < 1 at hi
    have hz : i = 0 := by omega
    subst i
    have hSlot := hs.read 0 (by simp [hintTreeEvents])
    have hEvent : D.events[first + 0]? = some (.store node (offsets node) N) := hSlot
    have hEq := Option.some.inj (he.symm.trans hEvent)
    subst e
    with_unfolding_all simp only [hintDecodePlacedTree_total, hintAndRec_value, id, HintDecoderPhase.adapt_budget_eq]
    change 12 * N + 12 ≤ base + extra
    exact (show 12 * N + 12 ≤ extra from hCost).trans (Nat.le_add_left _ _)
  | cr N t =>
    intro hLimits node seed first X Y hN hWF hBlock hSeed hp hRoot hs hCost keep hKeep hCursor i hi e he
    change i < 1 at hi
    have hz : i = 0 := by omega
    subst i
    have hSlot := hs.read 0 (by simp [hintTreeEvents])
    have hEvent : D.events[first + 0]? = some (.decodeLeaf node (offsets node) N t) := hSlot
    have hEq := Option.some.inj (he.symm.trans hEvent)
    subst e
    with_unfolding_all simp only [hintDecodePlacedTree_total, hintAndRec_value, id, HintDecoderPhase.adapt_budget_eq]
    change hintCRNodeBudget S N t ≤ base + extra
    exact (show hintCRNodeBudget S N t ≤ extra from hCost).trans (Nat.le_add_left _ _)
  | direct N X Y t =>
    intro hLimits node seed first X' Y' hN hWF hBlock hSeed hp hRoot hs hCost
    with_unfolding_all simp only [hintDecodePlacedTree_total, id]
    apply hintBinarySubtreeFromBitmaps_budget_follows
    intro J keep hKeep hCursor
    apply hintPlacedDirect_total_budget_follows
    · exact hRead
    · exact hCost
  | recursive N X Y t Xs Ys children hc ih =>
    intro hLimits node seed first X' Y' hN hWF hBlock hSeed hp hRoot hs hCost
    have hLocal : HintTreeTimeBounds S H Bc U radius base extra (.recursive N X Y t Xs Ys children hc) := hCost
    change HintRowTimeBounds S H N X Y t Bc U radius base extra ∧
      11 * (H.scheme N X Y).m + 11 ≤ extra ∧
      ∀ col, (17 * synLen CR (children col) + 13 ≤ extra) ∧
        (147 * (1 + upRest Bc (children col)) + 24 ≤ base) ∧ HintTreeTimeBounds S H Bc U radius base extra (hc col) at hLocal
    with_unfolding_all simp only [hintDecodePlacedTree_total, id]
    apply hintBinarySubtreeFromBitmaps_budget_follows
    intro J keep hKeep hCursor
    apply hintPlacedRecursive_total_budget_follows
    · exact hLocal.1
    · exact fun col => (hLocal.2.2 col).1
    · exact fun col => (hLocal.2.2 col).2.1
    · exact hLocal.2.1
    · intro col start hSlice
      apply ih
      exact (hLocal.2.2 col).2.2

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecodePlacedTree_total_budget_follows
end -- Def_LinearSetReconciliation327_Main_HintPlacedTreeBudget20261120

section -- Def_LinearSetReconciliation327_Main_HintTreeCountActual20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintEll_le_quadratic {P : HintParams}
    (hn : 2 ≤ P.n) {N X Y : ℕ} (hN1 : 1 ≤ N) (hNn : N ≤ P.n) (hXN : X ≤ N) (hYN : Y ≤ N)
    (hm1 : 1 ≤ P.rows X Y) :
    (P.ell N X Y : ℝ) ≤ P.lgn ^ 3 + (48 * ((P.A : ℝ) + P.C + 2)) * P.lgn ^ 2 := by
  have hL1 : 1 ≤ P.lgn := one_le_lg hn
  have hL0 : 0 < P.lgn := by linarith
  have hA0 : (0 : ℝ) ≤ (P.A : ℝ) := by positivity
  have hC0 : (0 : ℝ) ≤ (P.C : ℝ) := by positivity
  have hL2 : P.lgn ≤ P.lgn ^ 2 := by nlinarith only [hL1]
  have hrowsle : P.rows X Y ≤ N := rows_le_N hL1 hXN hYN
  have hm0 : (0 : ℝ) < (P.rows X Y : ℝ) := by exact_mod_cast hm1
  have hNmax1 : 1 ≤ P.Nmax N X Y := by
    unfold HintParams.Nmax
    have h2 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have h3 : (1 : ℝ) ≤ (N : ℝ) / (P.rows X Y : ℝ) := by
      rw [le_div_iff₀ hm0]
      have h4 : (P.rows X Y : ℝ) ≤ (N : ℝ) := by exact_mod_cast hrowsle
      linarith
    have h5 := Nat.le_ceil ((N : ℝ) / (P.rows X Y : ℝ))
    have h6 : (1 : ℝ) ≤ ((⌈(N : ℝ) / (P.rows X Y : ℝ)⌉₊ : ℕ) : ℝ) := le_trans h3 h5
    exact_mod_cast h6
  have hNmaxN : P.Nmax N X Y ≤ N := Nmax_le_N
  have hlgNmax : lg ((P.Nmax N X Y : ℕ) : ℝ) ≤ P.lgn := by
    have hcast : ((P.Nmax N X Y : ℕ) : ℝ) ≤ ((P.n : ℕ) : ℝ) := by
      exact_mod_cast le_trans hNmaxN hNn
    have hpos : (0 : ℝ) < ((P.Nmax N X Y : ℕ) : ℝ) := by
      have h : (1 : ℝ) ≤ ((P.Nmax N X Y : ℕ) : ℝ) := by exact_mod_cast hNmax1
      linarith
    exact Real.logb_le_logb_of_le (by norm_num) hpos hcast
  have hce : (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) ≤ 4 * P.lgn := by
    have h := ceil_lg_exp_Nmax_le P N X Y hNmax1
    linarith only [h, hlgNmax, hL1]
  have hBX := BX_le_sharp P N X Y
  have hBY := BY_le_sharp P N X Y
  have hBY2 : (P.BY N X Y : ℝ) ≤ 6 * (P.C : ℝ) * P.lgn + 5 := by
    have hlgL2 : lg (P.lgn + 2) ≤ 2 * (P.lgn + 2) := lg_le_two_mul _ (by linarith)
    have h2 : (P.C : ℝ) * lg (P.lgn + 2) ≤ (P.C : ℝ) * (2 * (P.lgn + 2)) :=
      mul_le_mul_of_nonneg_left hlgL2 hC0
    have h4 : (4 : ℝ) * (P.C : ℝ) ≤ 4 * (P.C : ℝ) * P.lgn := by nlinarith only [hC0, hL1]
    nlinarith only [hBY, h2, h4]
  have hBYce : (P.BY N X Y : ℝ) * (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ)
      ≤ (24 * (P.C : ℝ) + 20) * P.lgn ^ 2 := by
    have hpos : (0 : ℝ) ≤ (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) := by positivity
    have hnn : (0 : ℝ) ≤ 6 * (P.C : ℝ) * P.lgn + 5 := by nlinarith only [hC0, hL1]
    have h1 : (P.BY N X Y : ℝ) * (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ)
        ≤ (6 * (P.C : ℝ) * P.lgn + 5) * (4 * P.lgn) := mul_le_mul hBY2 hce hpos hnn
    have h3 : (20 : ℝ) * P.lgn ≤ 20 * P.lgn ^ 2 := by nlinarith only [hL1]
    nlinarith only [h1, h3]
  have h7 : (P.BY N X Y : ℝ) ≤ (6 * (P.C : ℝ) + 5) * P.lgn ^ 2 := by
    have h6 : (P.BY N X Y : ℝ) ≤ (6 * (P.C : ℝ) + 5) * P.lgn := by nlinarith only [hBY2, hL1]
    nlinarith only [h6, hL2]
  have heta := ceil_lg_eta_inv_sq_le (P := P) hn
  have hlgL : lg P.lgn ≤ 2 * P.lgn := lg_le_two_mul P.lgn hL1
  have heta2 : (⌈lg (16 / P.eta ^ 2)⌉₊ : ℝ) ≤ (4 * (P.A : ℝ) + 5) * P.lgn ^ 2 := by
    have h3 : (5 : ℝ) + 2 * (P.A : ℝ) * lg P.lgn ≤ 5 + 4 * (P.A : ℝ) * P.lgn := by
      nlinarith only [hA0, hlgL]
    have h4 : (5 : ℝ) + 4 * (P.A : ℝ) * P.lgn ≤ (4 * (P.A : ℝ) + 5) * P.lgn ^ 2 := by
      nlinarith only [hA0, hL1, hL2]
    linarith only [heta, h3, h4]
  have hell : (P.ell N X Y : ℝ) = (P.BX N X Y : ℝ) +
      (P.BY N X Y : ℝ) * (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) +
      (P.BY N X Y : ℝ) + (⌈lg (16 / P.eta ^ 2)⌉₊ : ℝ) + 10 := by
    unfold HintParams.ell
    push_cast
    ring
  have hE : (31 * (P.C : ℝ) + 4 * (P.A : ℝ) + 41) ≤ (48 * ((P.A : ℝ) + P.C + 2)) := by
    linarith only [hA0, hC0]
  have h1 : (1 : ℝ) ≤ P.lgn ^ 2 := one_le_pow₀ hL1
  have hB : (P.BX N X Y : ℝ) +
      (P.BY N X Y : ℝ) * (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) +
      (P.BY N X Y : ℝ) + (⌈lg (16 / P.eta ^ 2)⌉₊ : ℝ) + 10
      ≤ P.lgn ^ 3 + (48 * ((P.A : ℝ) + P.C + 2)) * P.lgn ^ 2 := by
    have h1' : (P.BX N X Y : ℝ) ≤ P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2 + 1 := hBX
    have h8 : (10 : ℝ) ≤ 10 * P.lgn ^ 2 := by linarith only [h1]
    nlinarith only [h1', hBYce, h7, heta2, h8, hE, h1]
  linarith only [hell, hB]
noncomputable def hintEventColCap (P : HintParams) : ℕ :=
  ⌈(48 * ((P.A : ℝ) + P.C + 2) + 1) * P.lgn ^ 3⌉₊

theorem hintEll_le_colCap {P : HintParams} {N X Y : ℕ}
    (hArgs : P.NodeArgs N X Y) (hm : 1 ≤ P.rows X Y) :
    P.ell N X Y ≤ hintEventColCap P := by
  obtain ⟨hn, _, hN, hNn, hX, hY⟩ := hArgs
  have hEll := hintEll_le_quadratic hn hN hNn hX hY hm
  have hLog : 1 ≤ P.lgn := one_le_lg hn
  have hPower : P.lgn ^ 2 ≤ P.lgn ^ 3 := by
    exact pow_le_pow_right₀ hLog (by decide)
  have hFactor : (0 : ℝ) ≤ 48 * ((P.A : ℝ) + P.C + 2) := by positivity
  have hBound : (P.ell N X Y : ℝ) ≤ (48 * ((P.A : ℝ) + P.C + 2) + 1) * P.lgn ^ 3 := by
    apply hEll.trans
    have h := mul_le_mul_of_nonneg_left hPower hFactor
    nlinarith only [h]
  have hCap : (P.ell N X Y : ℝ) ≤ (hintEventColCap P : ℝ) :=
    hBound.trans (Nat.le_ceil _)
  exact_mod_cast hCap

theorem hintScheduleShape_tree (P : HintParams) (U fuel : ℕ) :
    ∀ N X Y T, N ≤ U → P.NodeArgs N X Y → P.tree fuel N X Y = some T →
      HintScheduleShape U (hintEventColCap P) T := by
  induction fuel with
  | zero =>
      intro N X Y T _ _ ht
      simp [HintParams.tree] at ht
  | succ f ih =>
      intro N X Y T hU hArgs hTree
      have hBase := hArgs
      obtain ⟨hn, hlam, _, hNn, hXN, hYN⟩ := hBase
      have hLog : 1 ≤ P.lgn := one_le_lg hn
      have hm := up_rows_le_N P N X Y hLog hXN hYN
      simp only [HintParams.tree] at hTree
      cases hRule : P.rule N X Y
      · simp only [hRule, Option.some.injEq] at hTree
        subst T
        trivial
      · simp only [hRule, Option.some.injEq] at hTree
        subst T
        trivial
      · simp only [hRule] at hTree
        obtain ⟨child, hSome, hT⟩ := Option.map_eq_some_iff.mp hTree
        subst T
        have hRec := rule_recursive_spec hRule
        have hY := one_le_Y_of_recursive hLog hRec.1 hRec.2.2
        have hm1 : 1 ≤ P.rows X Y := hRec.2.2.symm ▸ hY
        refine ⟨hU, hm.trans hU, hintEll_le_colCap hArgs hm1, ?_⟩
        intro s
        exact ih Y _ _ (child s) (hYN.trans hU)
          ⟨hn, hlam, hY, hYN.trans hNn, min_le_left _ _, min_le_left _ _⟩
          (allSome_spec _ _ hSome s)
      · simp only [hRule, Option.some.injEq] at hTree
        subst T
        exact ⟨hU, hm.trans hU, hintEll_le_colCap hArgs (one_le_rows_of_ne (rule_direct_spec hRule).2.2)⟩

theorem hintTreeEvents_count_actual {P : HintParams} {N X Y : ℕ}
    (CR : CRFamily) (payloadOffset : ℕ → ℕ) (fuel : ℕ) (T : Node)
    (hArgs : P.NodeArgs N X Y) (hTree : P.tree fuel N X Y = some T)
    (node seed offset : ℕ) :
    (hintTreeEvents CR payloadOffset T node seed offset).length ≤
      ((2 * N + 2) * hintEventColCap P + 2 * N + 3) * T.nodeCount :=
  hintTreeEvents_count CR payloadOffset N (hintEventColCap P) T
    (hintScheduleShape_tree P N fuel N X Y T le_rfl hArgs hTree) node seed offset

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintEll_le_quadratic
#print axioms LinearSetReconciliation327.Main.hintTreeEvents_count_actual
end -- Def_LinearSetReconciliation327_Main_HintTreeCountActual20261120

section -- Def_LinearSetReconciliation327_Main_HintDecoderTableCap20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

private theorem hintFoldMax_le (xs : List ℕ) (cap : ℕ) (h : ∀ x ∈ xs, x ≤ cap) :
    ∀ start ≤ cap, xs.foldl max start ≤ cap := by
  induction xs with
  | nil => exact fun _ h => h
  | cons x xs ih =>
    intro a ha
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) (max a x)
      (max_le ha (h x (List.mem_cons_self ..)))

private theorem hintRecordLength_sum_le (events : List HintTreeEvent) :
    (events.map HintTreeEvent.recordLength).sum ≤ 31 * events.length := by
  induction events with
  | nil => simp
  | cons e ee ih =>
    have h : e.recordLength ≤ 31 := by cases e <;> norm_num [HintTreeEvent.recordLength]
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

theorem hintDecoderTables_size_le (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (W Bc header scratchCap arenaCap auxCap : ℕ) :
    let D := hintDecoderTables S H hT W Bc header
    (∀ info ∈ D.infos, hintRowScratchSize H info ≤ scratchCap) →
    (∀ info ∈ D.infos, (hintArenaFor S H W info 0).limit ≤ arenaCap) →
    (∀ i : Fin D.infos.length, ((D.nodeAux S H Bc i.val).map HintDetBlock.length).sum ≤ auxCap) →
    hintArenaStart D.heap D.stride D.infos.length ≤
      wordsOf W (synLen (crFamily S) T) + 2 * T.N + 3 + scratchCap + arenaCap * T.nodeCount ∧
    hintDecoderDetEnd S H D header ≤ header + 16 + 33 * D.events.length + auxCap * T.nodeCount := by
  let D := hintDecoderTables S H hT W Bc header
  dsimp only
  intro hScratch hArena hAux
  have hInfos : D.infos.length = T.nodeCount := hintNodeInfos_length (crFamily S) hT 0 0
  have hScratch' : (D.infos.map (hintRowScratchSize H)).foldl max 0 ≤ scratchCap := by
    apply hintFoldMax_le _ _ _ 0 (Nat.zero_le _)
    intro a ha
    obtain ⟨info, hi, rfl⟩ := List.mem_map.mp ha
    exact hScratch info hi
  have hStride : D.stride ≤ arenaCap := by
    change (D.infos.map fun i => (hintArenaFor S H W i 0).limit).foldl max 0 ≤ arenaCap
    apply hintFoldMax_le _ _ _ 0 (Nat.zero_le _)
    intro a ha
    obtain ⟨info, hi, rfl⟩ := List.mem_map.mp ha
    exact hArena info hi
  have hHeap : D.heap ≤ wordsOf W (synLen (crFamily S) T) + 2 * T.N + 3 + scratchCap := by
    change wordsOf W (synLen (crFamily S) T) + T.N + 3 +
      (D.infos.map (hintRowScratchSize H)).foldl max 0 + T.N ≤ _
    omega
  refine ⟨?_, ?_⟩
  · change D.heap + D.stride * D.infos.length ≤ _
    rw [hInfos]
    exact Nat.add_le_add hHeap (Nat.mul_le_mul_right _ hStride)
  · have hAuxSum : (D.aux.map HintDetBlock.length).sum ≤ auxCap * T.nodeCount := by
      have hList : D.aux = List.ofFn (fun i : Fin D.infos.length => hintJoinDetBlocks (D.nodeAux S H Bc i.val)) := rfl
      rw [hList, List.map_ofFn, List.sum_ofFn]
      calc
        _ ≤ ∑ _ : Fin D.infos.length, auxCap := Finset.sum_le_sum (fun i _ => hAux i)
        _ = auxCap * T.nodeCount := by simp [hInfos, Nat.mul_comm]
    have hRecord := hintRecordLength_sum_le D.events
    change hintEventDescriptor header D.events (hintEventRecord S H D.placement) D.events.length +
      (D.aux.map HintDetBlock.length).sum ≤ header + 16 + 33 * D.events.length + auxCap * T.nodeCount
    rw [hintEventRecords_end]
    omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_size_le
end -- Def_LinearSetReconciliation327_Main_HintDecoderTableCap20261120

section -- Def_LinearSetReconciliation327_Main_HintArenaCap20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintWordsOf_le_bits (W bits : ℕ) (hW : 0 < W) : wordsOf W bits ≤ bits := by
  have hMul : bits ≤ bits * W := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left bits (show 1 ≤ W from hW)
  unfold wordsOf
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hW).mpr
  rw [Nat.succ_mul]
  omega

theorem hintRowScratchSize_le (H : HintParams) (info : HintNodeInfo) (U : ℕ)
    (hCaps : ∀ X Y, info.rowParams = some (X, Y) →
      H.ell info.universeSize X Y ≤ U ∧ H.Nmax info.universeSize X Y ≤ U ∧ H.BY info.universeSize X Y ≤ U) :
    hintRowScratchSize H info ≤ 34 + 9 * U + 2 * U ^ 2 := by
  unfold hintRowScratchSize
  cases h : info.rowParams with
  | none => exact Nat.zero_le _
  | some xy =>
    obtain ⟨X, Y⟩ := xy
    obtain ⟨hA, hK, hB⟩ := hCaps X Y h
    let a := H.ell info.universeSize X Y
    let k := H.Nmax info.universeSize X Y
    let b := H.BY info.universeSize X Y
    change a ≤ U at hA
    change k ≤ U at hK
    change b ≤ U at hB
    change (hintRowWorkspace 0 a k b 0 0 a k).gauss.pivotRow + a ≤ _
    have haa := Nat.mul_le_mul hA hA
    have hka := Nat.mul_le_mul hK hA
    simp only [hintRowWorkspace, hintGaussDenseArea, Nat.zero_add, pow_two]
    omega

theorem hintArenaFor_limit_le (S : CRSourceBundle) (H : HintParams) (W : ℕ)
    (info : HintNodeInfo) (matrixCap residualCap spillCap stepsCap : ℕ)
    (hW : 0 < W)
    (hRows : ∀ X Y, info.rowParams = some (X, Y) →
      H.rows X Y * H.ell info.universeSize X Y ≤ matrixCap)
    (hResidual : (S.data info.universeSize info.residualCapacity).R ≤ residualCap)
    (hSpill : 2 ^ ((S.data info.universeSize info.residualCapacity).W + 1) ≤ spillCap)
    (hEmpty : 2 ≤ spillCap)
    (hSteps : crSourceSteps S info.universeSize info.residualCapacity ≤ stepsCap) :
    (hintArenaFor S H W info 0).limit ≤
      info.payloadBits + 2 * info.schemes + matrixCap + 3 * info.universeSize +
        residualCap + spillCap + stepsCap + 25 := by
  have hLimit (rows cols R w steps : ℕ) (hMat : rows * cols ≤ matrixCap)
      (hR : R ≤ residualCap) (hMem : 2 ^ (w + 1) ≤ spillCap) (hRun : steps ≤ stepsCap) :
      (hintNodeArena 0 W info.payloadBits info.schemes rows cols info.universeSize R w steps).limit ≤
        info.payloadBits + 2 * info.schemes + matrixCap + 3 * info.universeSize +
          residualCap + spillCap + stepsCap + 25 := by
    have hIn := hintWordsOf_le_bits W info.payloadBits hW
    have hOut := (hintWordsOf_le_bits W R hW).trans hR
    simp only [hintNodeArena, Nat.zero_add]
    omega
  unfold hintArenaFor
  cases h : info.rowParams with
  | none =>
    simp only [h, Option.isSome_none, Bool.or_false]
    cases hc : info.isCR with
    | false =>
      exact hLimit 0 0 0 0 0 (Nat.zero_le _) (Nat.zero_le _) hEmpty (Nat.zero_le _)
    | true =>
      exact hLimit 0 0 _ _ _ (Nat.zero_le _) hResidual hSpill hSteps
  | some xy =>
    obtain ⟨X, Y⟩ := xy
    simp only [h, Option.isSome_some, Bool.or_true, if_true]
    exact hLimit _ _ _ _ _ (hRows X Y h) hResidual hSpill hSteps

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintArenaFor_limit_le
end -- Def_LinearSetReconciliation327_Main_HintArenaCap20261120

section -- Def_LinearSetReconciliation327_Main_HintTreeResourceCaps20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintUpRest_le (Bc L : ℕ) (T : Node) (hEll : UpEllOK L T) :
    upRest Bc T + 2 ≤ (Bc + L + 3) * T.nodeCount := by
  induction T with
  | store N =>
    change 1 + 2 ≤ (Bc + L + 3) * 1
    omega
  | cr N t =>
    change Bc + 2 ≤ (Bc + L + 3) * 1
    omega
  | direct sch t =>
    change sch.ℓ ≤ L at hEll
    change sch.ℓ + Bc + 2 ≤ (Bc + L + 3) * 1
    omega
  | recursive sch t Xs Ys child ih =>
    have hc : ∀ s, UpEllOK L (child s) := hEll.2
    have hSum : (∑ s, (2 + upRest Bc (child s))) ≤ (Bc + L + 3) * ∑ s, (child s).nodeCount := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun s _ => by simpa only [Nat.add_comm 2] using ih s (hc s))
    change Bc + (∑ s, (2 + upRest Bc (child s))) + 2 ≤ (Bc + L + 3) * (1 + ∑ s, (child s).nodeCount)
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem hintSubtreeBlock_length_le (CR : CRFamily) (W control Bc L U : ℕ)
    (T : Node) (seed sav : ℕ)
    (hEll : UpEllOK L T) (hStatic : UpTreeStatic CR Bc U T) :
    (hintSubtreeBlock CR W control Bc T seed sav).length ≤
      8 + 16 * ((Bc + L + 3) * T.nodeCount) + T.nodeCount * U * (Bc + 1) := by
  have hRest := hintUpRest_le Bc L T hEll
  have hTab := upTabLen_le_static CR Bc U T hStatic
  change 8 + 16 * (1 + upRest Bc T) + upTabLen Bc T ≤ _
  omega

theorem hintSynLen_le_of_shape (CR : CRFamily) (U L R : ℕ)
    (hCR : ∀ N t, N ≤ U → t ≤ N → CR.rows N t ≤ R) :
    ∀ (T : Node) (X Y : ℕ), T.N ≤ U → Node.WF T X Y → HintScheduleShape U L T →
      synLen CR T ≤ (U * L + U + R) * T.nodeCount := by
  intro T
  induction T with
  | store N =>
    intro X Y hN _ _
    change N ≤ U at hN
    change N ≤ (U * L + U + R) * 1
    omega
  | cr N t =>
    intro X Y hN hWF _
    change N ≤ U at hN
    have hR := hCR N t hN hWF.1
    change CR.rows N t ≤ (U * L + U + R) * 1
    omega
  | direct sch t =>
    intro X Y hN hWF hShape
    have hR := hCR sch.N t hN hWF
    have hProduct := Nat.mul_le_mul hShape.2.1 hShape.2.2
    change sch.m * sch.ℓ + CR.rows sch.N t ≤ (U * L + U + R) * 1
    omega
  | recursive sch t Xs Ys child ih =>
    intro X Y hN hWF hShape
    have hR := hCR sch.N t hN hWF.1
    let cap := U * L + U + R
    have hChild (s : Fin sch.ℓ) : (child s).N ≤ U := (hWF.2 s).1.trans_le hShape.2.1
    have hSum : (∑ s, synLen CR (child s)) ≤ cap * ∑ s, (child s).nodeCount := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun s _ => ih s (Xs s) (Ys s) (hChild s) (hWF.2 s).2 (hShape.2.2.2 s))
    change (∑ s, synLen CR (child s)) + CR.rows sch.N t ≤ cap * (1 + ∑ s, (child s).nodeCount)
    rw [Nat.mul_add, Nat.mul_one]
    dsimp only [cap] at *
    omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintSubtreeBlock_length_le
#print axioms LinearSetReconciliation327.Main.hintSynLen_le_of_shape
end -- Def_LinearSetReconciliation327_Main_HintTreeResourceCaps20261120

section -- Def_LinearSetReconciliation327_Main_HintNodeResources20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintNodeResourceBound (CR : CRFamily) (Bc : ℕ) (T : Node) (info : HintNodeInfo) : Prop where
  bits : info.payloadBits ≤ synLen CR T
  seeds : info.schemes ≤ (schemeNodes T).length
  updateRecords : upRest Bc info.subtree ≤ upRest Bc T
  updateColumns : upTabLen Bc info.subtree ≤ upTabLen Bc T

theorem hintNodeInfos_resources (CR : CRFamily) (H : HintParams) (Bc : ℕ)
    {T : Node} (hT : IsSchemeTree H T) :
    ∀ node seed, ∀ q ∈ hintNodeInfos CR hT node seed, HintNodeResourceBound CR Bc T q := by
  induction hT with
  | store N =>
    intro node seed q h
    simp only [hintNodeInfos, List.mem_singleton] at h
    subst q
    exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  | cr N t =>
    intro node seed q h
    simp only [hintNodeInfos, List.mem_singleton] at h
    subst q
    exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  | direct N X Y t =>
    intro node seed q h
    simp only [hintNodeInfos, List.mem_singleton] at h
    subst q
    exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  | recursive N X Y t Xs Ys child hc ih =>
    intro node seed q h
    let sch := H.scheme N X Y
    let T := Node.recursive sch t Xs Ys child
    rw [hintNodeInfos, List.mem_cons] at h
    rcases h with e | hIn
    · subst q
      exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
    · obtain ⟨block, hb, hq⟩ := List.mem_flatten.mp hIn
      obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hb
      have hs := ih s _ _ q hq
      have hBits : synLen CR (child s) ≤ synLen CR T := by
        have hSum : synLen CR (child s) ≤ ∑ j, synLen CR (child j) :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (synLen CR (child j))) (Finset.mem_univ s)
        exact hSum.trans (Nat.le_add_right _ _)
      have hSeeds : (schemeNodes (child s)).length ≤ (schemeNodes T).length := by
        unfold T
        rw [schemeNodes_length_rec]
        exact (Finset.single_le_sum (fun j _ => Nat.zero_le ((schemeNodes (child j)).length)) (Finset.mem_univ s)).trans
          (Nat.le_add_left _ _)
      have hRecords : upRest Bc (child s) ≤ upRest Bc T := by
        have hSum : 2 + upRest Bc (child s) ≤ ∑ j, (2 + upRest Bc (child j)) :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (2 + upRest Bc (child j))) (Finset.mem_univ s)
        exact (Nat.le_add_left _ _).trans (hSum.trans (Nat.le_add_left _ _))
      have hColumns : upTabLen Bc (child s) ≤ upTabLen Bc T := by
        have hSum : upTabLen Bc (child s) ≤ ∑ j, upTabLen Bc (child j) :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (upTabLen Bc (child j))) (Finset.mem_univ s)
        exact hSum.trans (Nat.le_add_left _ _)
      exact ⟨hs.bits.trans hBits, hs.seeds.trans hSeeds, hs.updateRecords.trans hRecords,
        hs.updateColumns.trans hColumns⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintNodeInfos_resources
end -- Def_LinearSetReconciliation327_Main_HintNodeResources20261120

section -- Def_LinearSetReconciliation327_Main_HintNodeAuxCap20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

private theorem hintNodeWait_sum (H : HintParams) (N X Y : ℕ) :
    (((List.range (H.rows X Y)).map fun j =>
      hintWaitDetBlock (H.Nmax N X Y) (rowLen N (H.rows X Y) j) (H.BY N X Y)
        (H.ell N X Y) (H.c N X Y)).map HintDetBlock.length).sum =
      H.rows X Y * ((H.Nmax N X Y + 1) * (H.BY N X Y + 1)) := by
  simp only [List.map_map, Function.comp_apply, hintWaitDetBlock]
  generalize H.rows X Y = m
  have h (l : List ℕ) : (l.map fun _ => (H.Nmax N X Y + 1) * (H.BY N X Y + 1)).sum =
      l.length * ((H.Nmax N X Y + 1) * (H.BY N X Y + 1)) := by
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.succ_mul l.length]
      omega
  exact (h _).trans (by rw [List.length_range])

theorem hintNodeAux_length_le (S : CRSourceBundle) (H : HintParams) (W control Bc : ℕ)
    (info : HintNodeInfo) (A : HintNodeArena) (U K spill : ℕ)
    (hN : info.universeSize ≤ U)
    (hSpill : 2 ^ ((S.data info.universeSize info.residualCapacity).W + 1) ≤ spill)
    (hRows : ∀ X Y, info.rowParams = some (X, Y) →
      H.rows X Y ≤ U ∧ H.Nmax info.universeSize X Y ≤ K ∧ H.BY info.universeSize X Y ≤ K) :
    ((hintNodeAuxBlocks S H W control Bc info A).map HintDetBlock.length).sum ≤
      (8 + 16 * (1 + upRest Bc info.subtree) + upTabLen Bc info.subtree) +
      (8 + 16 * (1 + Bc) + U * (Bc + 1)) + (spill + 1) + U * (K + 1) ^ 2 := by
  let N := info.universeSize
  let t := info.residualCapacity
  let length := 8 + 16 * (1 + upRest Bc info.subtree) + upTabLen Bc info.subtree
  have hLocalCR : 2 ^ (S.data N t).W + 1 ≤ spill + 1 := by
    change 2 ^ ((S.data N t).W + 1) ≤ spill at hSpill
    have hMon := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
      (Nat.le_add_right (S.data N t).W 1)
    omega
  have hLocalUp : N * (Bc + 1) ≤ U * (Bc + 1) := Nat.mul_le_mul_right _ hN
  change _ ≤ length + (8 + 16 * (1 + Bc) + U * (Bc + 1)) + (spill + 1) + U * (K + 1) ^ 2
  unfold hintNodeAuxBlocks
  cases h : info.rowParams with
  | none =>
    cases hc : info.isCR <;>
      simp only [Option.isSome_none, hc, Bool.false_or, Bool.true_or, Bool.false_eq_true, if_false, if_true,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;>
      first
      | (change length + (0 + (0 + 0)) ≤ _; omega)
      | (change length + (0 + ((2 ^ (S.data N t).W + 1) + 0)) ≤ _; omega)
  | some xy =>
    obtain ⟨X, Y⟩ := xy
    obtain ⟨hm, hK, hB⟩ := hRows X Y h
    simp only [Option.isSome_some, Bool.or_true, if_true, List.map_cons, List.sum_cons, hintNodeWait_sum]
    have hWait := Nat.mul_le_mul hm (Nat.mul_le_mul (Nat.succ_le_succ hK) (Nat.succ_le_succ hB))
    change H.rows X Y * ((H.Nmax N X Y + 1) * (H.BY N X Y + 1)) ≤ U * ((K + 1) * (K + 1)) at hWait
    change length + ((8 + 16 * (1 + Bc) + N * (Bc + 1)) +
      (2 ^ (S.data N t).W + 1 + H.rows X Y * ((H.Nmax N X Y + 1) * (H.BY N X Y + 1)))) ≤ _
    rw [pow_two]
    omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintNodeAux_length_le
end -- Def_LinearSetReconciliation327_Main_HintNodeAuxCap20261120

section -- Def_LinearSetReconciliation327_Main_HintPolynomialWord20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintPolynomial_lt_word (n coefficient degree width : ℕ)
    (hWidth : Nat.clog 2 (coefficient + 1) + Nat.clog 2 (n + 2) * degree ≤ width) :
    coefficient * (n + 2) ^ degree < 2 ^ width := by
  have hCoeff : coefficient < 2 ^ Nat.clog 2 (coefficient + 1) :=
    (Nat.lt_succ_self _).trans_le (Nat.le_pow_clog (by decide) _)
  have hN : n + 2 ≤ 2 ^ Nat.clog 2 (n + 2) := Nat.le_pow_clog (by decide) _
  have hPow : (n + 2) ^ degree ≤ (2 ^ Nat.clog 2 (n + 2)) ^ degree :=
    Nat.pow_le_pow_left hN _
  calc
    _ < 2 ^ Nat.clog 2 (coefficient + 1) * (n + 2) ^ degree :=
      Nat.mul_lt_mul_of_pos_right hCoeff (Nat.pow_pos (by omega : 0 < n + 2))
    _ ≤ 2 ^ Nat.clog 2 (coefficient + 1) * (2 ^ Nat.clog 2 (n + 2)) ^ degree :=
      Nat.mul_le_mul_left _ hPow
    _ = 2 ^ (Nat.clog 2 (coefficient + 1) + Nat.clog 2 (n + 2) * degree) := by rw [pow_add, pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hWidth

theorem hintWideWord_addressSpan (words base : ℕ) (hBase : 0 < base)
    (hSpace : words < 2 ^ (4 * base)) :
    words * upWideWord base < 2 ^ upWideWord base := by
  have hFactor : 8 ≤ 2 ^ (3 * base) := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (show 3 ≤ 3 * base by omega)
  have hWord : 8 * base ≤ 2 ^ (4 * base) := by
    calc
      _ ≤ 2 ^ (3 * base) * 2 ^ base := Nat.mul_le_mul hFactor (Nat.lt_two_pow_self.le)
      _ = _ := by rw [← pow_add]; congr 1; omega
  change words * (8 * base) < 2 ^ (8 * base)
  calc
    _ < 2 ^ (4 * base) * (8 * base) := Nat.mul_lt_mul_of_pos_right hSpace (by omega)
    _ ≤ 2 ^ (4 * base) * 2 ^ (4 * base) := Nat.mul_le_mul_left _ hWord
    _ = _ := by rw [← pow_add]; congr 1; omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPolynomial_lt_word
#print axioms LinearSetReconciliation327.Main.hintWideWord_addressSpan
end -- Def_LinearSetReconciliation327_Main_HintPolynomialWord20261120

section -- Def_LinearSetReconciliation327_Main_HintNodeWordCaps20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintNodeWordCaps (S : CRSourceBundle) (H : HintParams) (W : ℕ) (info : HintNodeInfo) : Prop where
  size : info.universeSize < 2 ^ W
  cr : (S.data info.universeSize info.residualCapacity).W + 1 < W
  row : ∀ X Y, info.rowParams = some (X, Y) →
    H.Nmax info.universeSize X Y < 2 ^ W ∧ H.ell info.universeSize X Y < 2 ^ W ∧
    H.BX info.universeSize X Y < 2 ^ W ∧ H.BY info.universeSize X Y + 1 < 2 ^ W ∧
    H.rows X Y ≤ info.universeSize ∧ 0 < H.ell info.universeSize X Y

private theorem hintUpTreeStatic_mono (CR : CRFamily) (Bc U V : ℕ) (hUV : U ≤ V) :
    ∀ T, UpTreeStatic CR Bc U T → UpTreeStatic CR Bc V T := by
  intro T
  induction T with
  | store N => intro h; exact h.trans hUV
  | cr N t => intro h; exact ⟨h.1.trans hUV, h.2⟩
  | direct sch t => intro h; exact ⟨h.1.trans hUV, h.2⟩
  | recursive sch t Xs Ys child ih =>
    intro h
    exact ⟨h.1.trans hUV, h.2.1, h.2.2.1,
      fun s => ⟨(h.2.2.2 s).1, ih s (h.2.2.2 s).2⟩⟩

theorem hintTreeLimits_of_nodeCaps (S : CRSourceBundle) (H : HintParams)
    (W Bc U : ℕ) {T : Node} (hT : IsSchemeTree H T) :
    ∀ node seed,
      (∀ info ∈ hintNodeInfos (crFamily S) hT node seed, HintNodeWordCaps S H W info) →
      UpTreeStatic (crFamily S) Bc U T →
      UpDimsBound (2 ^ W - 1) T ∧ UpTreeStatic (crFamily S) Bc T.N T ∧ HintTreeLimits S H W Bc hT := by
  let CR := crFamily S
  induction hT with
  | store N =>
    intro node seed hf _
    have h := hf (hintNodeInfo (P := H) CR (IsSchemeTree.store N) node seed)
      (by simp only [hintNodeInfos, List.mem_singleton]; rfl)
    have hN : N < 2 ^ W := h.size
    exact ⟨by change N ≤ 2 ^ W - 1; omega, Nat.le_refl _, trivial⟩
  | cr N t =>
    intro node seed hf hs
    have h := hf (hintNodeInfo (P := H) CR (IsSchemeTree.cr N t) node seed)
      (by simp only [hintNodeInfos, List.mem_singleton]; rfl)
    have hN : N < 2 ^ W := h.size
    exact ⟨by change N ≤ 2 ^ W - 1; omega, ⟨Nat.le_refl _, hs.2⟩, h.cr⟩
  | direct N X Y t =>
    intro node seed hf hs
    have h := hf (hintNodeInfo (P := H) CR (IsSchemeTree.direct N X Y t) node seed)
      (by simp only [hintNodeInfos, List.mem_singleton]; rfl)
    have hN : N < 2 ^ W := h.size
    obtain ⟨hK, hL, hX, hY, hm, hPos⟩ := h.row X Y rfl
    have hRow : HintRowLimits S H W Bc N X Y t :=
      ⟨hK, hL, hX, hY, hs.2.1, hm, hPos, h.cr, hs.2.2⟩
    change H.Nmax N X Y < 2 ^ W at hK
    change H.ell N X Y < 2 ^ W at hL
    change H.rows X Y ≤ N at hm
    refine ⟨?_, ⟨Nat.le_refl _, hs.2⟩, hRow⟩
    change N ≤ 2 ^ W - 1 ∧ H.rows X Y ≤ 2 ^ W - 1 ∧
      H.ell N X Y ≤ 2 ^ W - 1 ∧ H.Nmax N X Y ≤ 2 ^ W - 1
    exact ⟨by omega, by omega, by omega, by omega⟩
  | recursive N X Y t Xs Ys child hc ih =>
    intro node seed hf hs
    let sch := H.scheme N X Y
    let root := hintNodeInfo CR (.recursive N X Y t Xs Ys child hc) node seed
    let children := fun s => hintNodeInfos CR (hc s) (hintChildPhysicalIndex child node s)
      (hintChildSchemeIndex child seed s)
    have hList : hintNodeInfos CR (.recursive N X Y t Xs Ys child hc) node seed =
        root :: (List.ofFn children).flatten := rfl
    have h := hf root (by rw [hList]; exact List.mem_cons_self ..)
    have hN : N < 2 ^ W := h.size
    obtain ⟨hK, hL, hX, hY, hm, hPos⟩ := h.row X Y rfl
    have hRow : HintRowLimits S H W Bc N X Y t :=
      ⟨hK, hL, hX, hY, hs.2.1, hm, hPos, h.cr, hs.2.2.1⟩
    have hChild (s : Fin sch.ℓ) : UpDimsBound (2 ^ W - 1) (child s) ∧
        UpTreeStatic CR Bc (child s).N (child s) ∧ HintTreeLimits S H W Bc (hc s) := by
      apply ih s (hintChildPhysicalIndex child node s) (hintChildSchemeIndex child seed s) ?_ (hs.2.2.2 s).2
      intro info hMem
      apply hf info
      rw [hList]
      exact List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨children s,
        List.mem_ofFn.mpr ⟨s, rfl⟩, hMem⟩)
    change H.Nmax N X Y < 2 ^ W at hK
    change H.ell N X Y < 2 ^ W at hL
    change H.rows X Y ≤ N at hm
    refine ⟨?_, ?_, hRow, fun s => hChild s⟩
    · change N ≤ 2 ^ W - 1 ∧ H.rows X Y ≤ 2 ^ W - 1 ∧
        H.ell N X Y ≤ 2 ^ W - 1 ∧ H.Nmax N X Y ≤ 2 ^ W - 1 ∧ ∀ s, UpDimsBound (2 ^ W - 1) (child s)
      exact ⟨by omega, by omega, by omega, by omega, fun s => (hChild s).1⟩
    · refine ⟨Nat.le_refl _, hs.2.1, hs.2.2.1, fun s => ⟨(hs.2.2.2 s).1, ?_⟩⟩
      have hSize : (child s).N ≤ N := by rw [(hs.2.2.2 s).1]; exact hm
      exact hintUpTreeStatic_mono CR Bc (child s).N N hSize (child s) (hChild s).2.1

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintTreeLimits_of_nodeCaps
end -- Def_LinearSetReconciliation327_Main_HintNodeWordCaps20261120

section -- Def_LinearSetReconciliation327_Main_HintWidthResources20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintWidthResources (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (Bc header Q : ℕ) : Prop where
  headerFit : header ≤ Q
  padding : Bc ≤ Q
  count : T.nodeCount ≤ Q
  input : synLen (crFamily S) T ≤ Q
  seeds : (schemeNodes T).length ≤ Q
  records : upRest Bc T ≤ Q
  columns : upTabLen Bc T ≤ Q
  universeSize : T.N ≤ Q
  info : ∀ i ∈ hintNodeInfos (crFamily S) hT 0 0,
    i.universeSize ≤ Q ∧ (S.data i.universeSize i.residualCapacity).R ≤ Q ∧
    2 ^ ((S.data i.universeSize i.residualCapacity).W + 1) ≤ Q ∧
    crSourceSteps S i.universeSize i.residualCapacity ≤ Q ∧
    (∀ X Y, i.rowParams = some (X, Y) →
      0 < H.ell i.universeSize X Y ∧ H.ell i.universeSize X Y ≤ Q ∧
      H.Nmax i.universeSize X Y ≤ Q ∧ H.BY i.universeSize X Y ≤ Q ∧
      H.rows X Y ≤ i.universeSize)
  schedule : HintScheduleShape Q Q T

theorem hintDecoderLimits_of_resources (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (base Bc header Q U : ℕ)
    (hHeader : 3 < header) (hBase : 1 ≤ base) (hSmall : 2 ≤ Q)
    (hCap : HintWidthResources S H hT Bc header Q)
    (hStatic : UpTreeStatic (crFamily S) Bc U T)
    (hFit : (hintSpec T).Fits (upWideWord base))
    (hWord : 128 * (Q + 1) ^ 4 < 2 ^ (4 * base)) :
    HintDecoderLimits S H hT (upWideWord base) Bc header := by
  let W := upWideWord base
  let D := hintDecoderTables S H hT W Bc header
  let SCap := 34 + 9 * Q + 2 * Q ^ 2
  let ACap := Q + 2 * Q + Q * Q + 3 * Q + Q + Q + Q + 25
  let TCap := (8 + 16 * (1 + Q) + Q) + (8 + 16 * (1 + Q) + Q * (Q + 1)) + (Q + 1) + Q * (Q + 1) ^ 2
  have hW : 0 < W := by unfold W upWideWord; omega
  have hBounds := hintDecoderTables_size_le S H hT W Bc header SCap ACap TCap
    (by
      intro i hi
      have hh := (hCap.info i hi).2.2.2.2
      exact hintRowScratchSize_le H i Q (fun X Y he => ⟨(hh X Y he).2.1, (hh X Y he).2.2.1, (hh X Y he).2.2.2.1⟩))
    (by
      intro i hi
      obtain ⟨hN, hR, hSpill, hTime, hRCap⟩ := hCap.info i hi
      have hn := hintNodeInfos_resources (crFamily S) H Bc hT 0 0 i hi
      have hRow (X Y : ℕ) (he : i.rowParams = some (X, Y)) :
          H.rows X Y * H.ell i.universeSize X Y ≤ Q * Q :=
        Nat.mul_le_mul ((hRCap X Y he).2.2.2.2.trans hN) (hRCap X Y he).2.1
      have hh := hintArenaFor_limit_le S H W i (Q * Q) Q Q Q hW hRow hR hSpill hSmall hTime
      have hBits := hn.bits.trans hCap.input
      have hSeeds := hn.seeds.trans hCap.seeds
      unfold ACap
      omega)
    (by
      intro j
      let i := D.infos[j.val]
      have hi : i ∈ D.infos := List.getElem_mem j.isLt
      have hInfo : D.placement.info j.val = i := by
        change (D.infos[j.val]?).getD _ = i
        rw [List.getElem?_eq_getElem j.isLt, Option.getD_some]
      change ((hintNodeAuxBlocks S H W D.control Bc (D.placement.info j.val) (D.placement.arena j.val)).map
        HintDetBlock.length).sum ≤ TCap
      rw [hInfo]
      obtain ⟨hN, _, hSpill, _, hRCap⟩ := hCap.info i hi
      have hh := hintNodeAux_length_le S H W D.control Bc i (D.placement.arena j.val) Q Q Q hN hSpill
        (fun X Y he => ⟨(hRCap X Y he).2.2.2.2.trans hN, (hRCap X Y he).2.2.1, (hRCap X Y he).2.2.2.1⟩)
      have hn := hintNodeInfos_resources (crFamily S) H Bc hT 0 0 i hi
      have hR := hn.updateRecords.trans hCap.records
      have hC := hn.updateColumns.trans hCap.columns
      have hMul := Nat.mul_le_mul_left Q (Nat.succ_le_succ hCap.padding)
      change Q * (Bc + 1) ≤ Q * (Q + 1) at hMul
      have hb := hCap.padding
      unfold TCap
      omega)
  have hEvents : D.events.length ≤ ((2 * Q + 2) * Q + 2 * Q + 3) * Q := by
    rw [hintDecoderTables_events S H hT W Bc header]
    exact (hintTreeEvents_count (crFamily S) (fun i => D.placement.inputWord i * W) Q Q T hCap.schedule 0 0 0).trans
      (Nat.mul_le_mul_left _ hCap.count)
  have hCount := hCap.count
  have hMem := hBounds.1.trans (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ((hintWordsOf_le_bits _ _ hW).trans hCap.input)
      (Nat.mul_le_mul_left 2 hCap.universeSize)) (le_refl 3)) le_rfl)
    (Nat.mul_le_mul_left ACap hCount))
  have hDet := hBounds.2.trans (Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add_right hCap.headerFit 16) (Nat.mul_le_mul_left 33 hEvents))
    (Nat.mul_le_mul_left TCap hCount))
  have hMemoryCeiling : Q + 2 * Q + 3 + SCap + ACap * Q ≤ 128 * (Q + 1) ^ 4 := by
    unfold SCap ACap
    nlinarith only [show 0 ≤ Q from Nat.zero_le _, show 0 ≤ Q ^ 2 from Nat.zero_le _,
      show 0 ≤ Q ^ 3 from Nat.zero_le _, show 0 ≤ Q ^ 4 from Nat.zero_le _]
  have hDetCeiling : Q + 16 + 33 * (((2 * Q + 2) * Q + 2 * Q + 3) * Q) + TCap * Q ≤
      128 * (Q + 1) ^ 4 := by
    unfold TCap
    nlinarith only [show 0 ≤ Q from Nat.zero_le _, show 0 ≤ Q ^ 2 from Nat.zero_le _,
      show 0 ≤ Q ^ 3 from Nat.zero_le _, show 0 ≤ Q ^ 4 from Nat.zero_le _]
  have hQLarge : Q + 1 ≤ 128 * (Q + 1) ^ 4 := by
    have hOne : 1 ≤ Q + 1 := by omega
    have hp : Q + 1 ≤ (Q + 1) ^ 4 := by
      simpa only [pow_one] using pow_le_pow_right₀ hOne (by decide : 1 ≤ 4)
    exact hp.trans (by omega)
  have hHalf : 2 ^ (4 * base) ≤ 2 ^ W :=
    Nat.pow_le_pow_right (by decide) (by unfold W upWideWord; omega)
  have hQ : Q + 1 < 2 ^ W := (hQLarge.trans_lt hWord).trans_le hHalf
  have hWord30 : 30 < 2 ^ W := by
    have hs : 5 ≤ W := by unfold W upWideWord; omega
    exact lt_of_lt_of_le (by decide : 30 < 2 ^ 5) (Nat.pow_le_pow_right (by decide) hs)
  have hNodes := hintTreeLimits_of_nodeCaps S H W Bc U hT 0 0 (by
    intro i hi
    obtain ⟨hN, _, hSpill, _, hRows⟩ := hCap.info i hi
    have hWidth : (S.data i.universeSize i.residualCapacity).W + 1 < W := by
      by_contra! hbad
      exact (not_le_of_gt (hSpill.trans_lt (lt_of_le_of_lt (Nat.le_add_right _ _) hQ)))
        (Nat.pow_le_pow_right (by decide) hbad)
    refine ⟨hN.trans_lt (lt_of_le_of_lt (Nat.le_add_right _ _) hQ), hWidth, ?_⟩
    intro X Y he
    obtain ⟨hPos, hEll, hK, hBY, hm⟩ := hRows X Y he
    have hX : H.BX i.universeSize X Y ≤ H.Nmax i.universeSize X Y := min_le_left _ _
    omega) hStatic
  exact ⟨hHeader, hW, hWord30, (Nat.succ_le_succ hCap.padding).trans_lt hQ, hFit,
    hCap.seeds.trans_lt ((Nat.le_add_right _ _).trans_lt hQ),
    hintWideWord_addressSpan _ base hBase (hMem.trans_lt (hMemoryCeiling.trans_lt hWord)),
    hDet.trans_lt (hDetCeiling.trans_lt (hWord.trans_le hHalf)), hNodes.2.2⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderLimits_of_resources
end -- Def_LinearSetReconciliation327_Main_HintWidthResources20261120

section -- Def_LinearSetReconciliation327_Main_HintActualNodeInfo20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintActualNodeInput (P : HintParams) (root : ℕ) (info : HintNodeInfo) : Prop where
  positive : 0 < info.universeSize
  size : info.universeSize ≤ root
  capacity : info.residualCapacity ≤ info.universeSize
  row : ∀ X Y, info.rowParams = some (X, Y) →
    P.NodeArgs info.universeSize X Y ∧ P.NonLeaf info.universeSize X Y

theorem hintActualTreeInfo (P : HintParams) (CR : CRFamily) (fuel : ℕ) :
    ∀ N X Y T, P.NodeArgs N X Y → P.tree fuel N X Y = some T →
      ∃ hT : IsSchemeTree P T, T.N = N ∧ Node.WF T X Y ∧
        ∀ node seed, ∀ info ∈ hintNodeInfos CR hT node seed, HintActualNodeInput P N info := by
  induction fuel with
  | zero => intro N X Y T _ hTree; simp [HintParams.tree] at hTree
  | succ f ih =>
    intro N X Y T hArgs hTree
    have hN : 0 < N := hArgs.2.2.1
    have hL : 1 ≤ P.lgn := one_le_lg hArgs.1
    simp only [HintParams.tree] at hTree
    cases hRule : P.rule N X Y
    · simp only [hRule, Option.some.injEq] at hTree
      subst T
      refine ⟨.cr N (HintParams.D N X Y), rfl, ⟨min_le_left _ _, le_rfl⟩, ?_⟩
      intro node seed info hInfo
      simp only [hintNodeInfos, List.mem_singleton] at hInfo
      subst info
      exact ⟨hN, le_rfl, min_le_left _ _, fun _ _ he => by cases he⟩
    · simp only [hRule, Option.some.injEq] at hTree
      subst T
      refine ⟨.cr N (HintParams.D N X Y), rfl, ⟨min_le_left _ _, le_rfl⟩, ?_⟩
      intro node seed info hInfo
      simp only [hintNodeInfos, List.mem_singleton] at hInfo
      subst info
      exact ⟨hN, le_rfl, min_le_left _ _, fun _ _ he => by cases he⟩
    · simp only [hRule] at hTree
      obtain ⟨child, hSome, hTree⟩ := Option.map_eq_some_iff.mp hTree
      subst T
      let sch := P.scheme N X Y
      let Xs := fun s : Fin sch.ℓ => P.capX N X Y s.val
      let Ys := fun s : Fin sch.ℓ => P.capY N X Y s.val
      let t := P.resid N X Y
      have hY : 1 ≤ Y := one_le_Y_of_recursive hL (rule_recursive_spec hRule).1 (rule_recursive_spec hRule).2.2
      have hm : sch.m = Y := (rule_recursive_spec hRule).2.2
      have hYN := hArgs.2.2.2.2.2
      have ready (s : Fin sch.ℓ) :
          ∃ hc : IsSchemeTree P (child s), (child s).N = Y ∧ Node.WF (child s) (Xs s) (Ys s) ∧
            ∀ node seed, ∀ info ∈ hintNodeInfos CR hc node seed, HintActualNodeInput P Y info :=
        ih Y (Xs s) (Ys s) (child s)
          ⟨hArgs.1, hArgs.2.1, hY, hYN.trans hArgs.2.2.2.1, min_le_left _ _, min_le_left _ _⟩
          (allSome_spec _ _ hSome s)
      let hc := fun s => Classical.choose (ready s)
      have ht : t ≤ N := min_le_left _ _
      refine ⟨.recursive N X Y t Xs Ys child hc, rfl,
        ⟨ht, fun s => ⟨(Classical.choose_spec (ready s)).1.trans hm.symm,
          (Classical.choose_spec (ready s)).2.1⟩⟩, ?_⟩
      intro node seed info hMem
      rw [hintNodeInfos, List.mem_cons] at hMem
      rcases hMem with he | hi
      · subst info
        refine ⟨hN, le_rfl, ht, ?_⟩
        intro X' Y' hXY
        have e : (X, Y) = (X', Y') := Option.some.inj hXY
        cases e
        exact ⟨hArgs, Or.inl hRule⟩
      · obtain ⟨block, hb, ha⟩ := List.mem_flatten.mp hi
        obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hb
        have hChild := (Classical.choose_spec (ready s)).2.2 _ _ info ha
        exact ⟨hChild.positive, hChild.size.trans hYN, hChild.capacity, hChild.row⟩
    · simp only [hRule, Option.some.injEq] at hTree
      subst T
      have ht : P.resid N X Y ≤ N := min_le_left _ _
      refine ⟨.direct N X Y (P.resid N X Y), rfl, ht, ?_⟩
      intro node seed info hMem
      simp only [hintNodeInfos, List.mem_singleton] at hMem
      subst info
      refine ⟨hN, le_rfl, ht, ?_⟩
      intro X' Y' hXY
      have e : (X, Y) = (X', Y') := Option.some.inj hXY
      cases e
      exact ⟨hArgs, Or.inr hRule⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintActualTreeInfo
end -- Def_LinearSetReconciliation327_Main_HintActualNodeInfo20261120

section -- Def_LinearSetReconciliation327_Main_HintCRNodeCostCap20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintCRNodeBudget_le (S : CRSourceBundle) {n N t : ℕ}
    (hN : 1 ≤ N) (ht : t ≤ N) (hn : N ≤ n) :
    (hintCRNodeBudget S N t : ℝ) ≤ (33 * S.K + 184) * (N : ℝ) * lg ((n : ℝ) + 2) ^ 2 := by
  let L := lg ((n : ℝ) + 2)
  have hL : 1 ≤ L := by
    have he : lg (2 : ℝ) = 1 := lg_two
    rw [← he]
    exact Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) (by have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith)
  have hL0 : 0 ≤ L := by linarith
  have hlog (m : ℕ) (hm : m ≤ n) : 0 ≤ lg ((m : ℝ) + 2) ∧ lg ((m : ℝ) + 2) ≤ L := by
    have h1 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have h2 : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hm 2
    exact ⟨Real.logb_nonneg (by norm_num) (by norm_cast; omega), Real.logb_le_logb_of_le (b := 2) (by norm_num) h1 h2⟩
  obtain ⟨hN0, hNL⟩ := hlog N hn
  obtain ⟨ht0, htL⟩ := hlog t (ht.trans hn)
  have htR : (t : ℝ) ≤ N := by exact_mod_cast ht
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hNL2 : 1 ≤ (N : ℝ) * L ^ 2 := one_le_mul_of_one_le_of_one_le hNR hL2
  have hUnit : (N : ℝ) ≤ (N : ℝ) * L ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hL2 (Nat.cast_nonneg N)
  have hSyndrome : ((S.data N t).R : ℝ) ≤ S.K * ((N : ℝ) * L ^ 2) := by
    have hK : 0 ≤ S.K := S.K_pos.le
    apply ((S.spec N t hN ht).2.2.1).trans
    gcongr
  have hSteps : (crSourceSteps S N t : ℝ) ≤ S.K * ((N : ℝ) * L ^ 2) + 1 := by
    have hMax : max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2)) ≤ (N : ℝ) * L ^ 2 := by
      apply max_le hNL2
      rw [pow_two, ← mul_assoc]
      gcongr
    have hNonneg : 0 ≤ S.K * max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((N : ℝ) + 2)) :=
      mul_nonneg S.K_pos.le (le_trans (by norm_num) (le_max_left _ _))
    exact (Nat.ceil_lt_add_one hNonneg).le.trans (by
      have hh := mul_le_mul_of_nonneg_left hMax S.K_pos.le
      linarith)
  unfold hintCRNodeBudget
  push_cast
  change _ ≤ (33 * S.K + 184) * (N : ℝ) * L ^ 2
  nlinarith [hSyndrome, hSteps, hNL2, hUnit]

theorem hintCRSpill_le (S : CRSourceBundle) {n N t : ℕ}
    (hN : 1 ≤ N) (ht : t ≤ N) (hn : N ≤ n) :
    2 ^ ((S.data N t).W + 1) ≤ 2 * (n + 2) ^ ⌈S.cW⌉₊ := by
  let w := (S.data N t).W
  let C := ⌈S.cW⌉₊
  have hLogle : lg ((N : ℝ) + 2) ≤ lg ((n : ℝ) + 2) :=
    Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hn 2)
  have hLogpos : 0 ≤ lg ((n : ℝ) + 2) := Real.logb_nonneg (by norm_num) (by norm_cast; omega)
  have hWord : (w : ℝ) ≤ lg ((n : ℝ) + 2) * (C : ℝ) := by
    calc
      _ ≤ S.cW * lg ((N : ℝ) + 2) := (S.spec N t hN ht).1.2.2
      _ ≤ S.cW * lg ((n : ℝ) + 2) := mul_le_mul_of_nonneg_left hLogle S.cW_pos.le
      _ ≤ (C : ℝ) * lg ((n : ℝ) + 2) :=
        mul_le_mul_of_nonneg_right (Nat.le_ceil _) hLogpos
      _ = _ := mul_comm _ _
  have hPow : (2 : ℝ) ^ (w : ℝ) ≤ (2 : ℝ) ^ (lg ((n : ℝ) + 2) * (C : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hWord
  unfold lg at hPow
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_logb (b := 2) (by norm_num) (by norm_num) (by positivity),
    Real.rpow_natCast, Real.rpow_natCast] at hPow
  have hNat : 2 ^ w ≤ (n + 2) ^ C := by exact_mod_cast hPow
  exact (pow_succ' 2 w) ▸ (Nat.mul_le_mul_left 2 hNat)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintCRNodeBudget_le
#print axioms LinearSetReconciliation327.Main.hintCRSpill_le
end -- Def_LinearSetReconciliation327_Main_HintCRNodeCostCap20261120

section -- Def_LinearSetReconciliation327_Main_HintActualWidthResources20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem HintScheduleShape.mono {N N' L L' : ℕ} (hN : N ≤ N') (hL : L ≤ L') :
    ∀ T, HintScheduleShape N L T → HintScheduleShape N' L' T := by
  intro T
  induction T with
  | store N => intro _; trivial
  | cr N t => intro _; trivial
  | direct sch t =>
    intro h
    exact ⟨h.1.trans hN, h.2.1.trans hN, h.2.2.trans hL⟩
  | recursive sch t Xs Ys child ih =>
    intro h
    exact ⟨h.1.trans hN, h.2.1.trans hN, h.2.2.1.trans hL, fun s => ih s (h.2.2.2 s)⟩

theorem HintScheduleShape.ell {N L : ℕ} : ∀ T, HintScheduleShape N L T → UpEllOK L T := by
  intro T
  induction T with
  | store N => intro _; trivial
  | cr N t => intro _; trivial
  | direct sch t => intro h; exact h.2.2
  | recursive sch t Xs Ys child ih => intro h; exact ⟨h.2.2.1, fun s => ih s (h.2.2.2 s)⟩

def hintActualResourceCap (q : ℕ) : ℕ := 128 * (q + 1) ^ 4

theorem hintWidthResources_of_actual (S : CRSourceBundle) (H : HintParams) (fuel N X Y Bc q : ℕ)
    {T : Node} (hT : IsSchemeTree H T)
    (hArgs : H.NodeArgs N X Y) (hTree : H.tree fuel N X Y = some T)
    (hRoot : T.N = N) (hWF : Node.WF T X Y)
    (hInputs : ∀ i ∈ hintNodeInfos (crFamily S) hT 0 0, HintActualNodeInput H N i)
    (hU : H.n ≤ q) (hPad : Bc ≤ q) (hCol : hintEventColCap H ≤ q) (hCount : T.nodeCount ≤ q)
    (hCR : ∀ m t, 1 ≤ m → m ≤ H.n → t ≤ m →
       (S.data m t).R ≤ q ∧ 2 ^ ((S.data m t).W + 1) ≤ q ∧ crSourceSteps S m t ≤ q)
    (hStatic : UpTreeStatic (crFamily S) Bc H.n T) :
    HintWidthResources S H hT Bc (decAfterBase (upRootBase Bc T) (upTabLen Bc T)) (hintActualResourceCap q) := by
  let CR := crFamily S
  let Q := hintActualResourceCap q
  have hNn : N ≤ H.n := hArgs.2.2.2.1
  have hNq : N ≤ q := hNn.trans hU
  have hQ : q ≤ Q := by
    simp only [Q, hintActualResourceCap]
    nlinarith only [show 0 ≤ q from Nat.zero_le _, show 0 ≤ q ^ 2 from Nat.zero_le _,
      show 0 ≤ q ^ 3 from Nat.zero_le _, show 0 ≤ q ^ 4 from Nat.zero_le _]
  have hShape0 := hintScheduleShape_tree H q fuel N X Y T hNq hArgs hTree
  have hShape : HintScheduleShape q q T := HintScheduleShape.mono le_rfl hCol T hShape0
  have hRest := hintUpRest_le Bc q T (HintScheduleShape.ell T hShape)
  have hTab := upTabLen_le_static CR Bc H.n T hStatic
  have hRest' : upRest Bc T + 2 ≤ (q + q + 3) * q :=
    hRest.trans (Nat.mul_le_mul (by omega) hCount)
  have hTab' : upTabLen Bc T ≤ q * q * (q + 1) :=
    hTab.trans (Nat.mul_le_mul (Nat.mul_le_mul hCount hU) (Nat.succ_le_succ hPad))
  have hRows : ∀ m t, m ≤ H.n → t ≤ m → CR.rows m t ≤ q := by
    intro m t hM hT'
    by_cases hm : 1 ≤ m
    · exact (hCR m t hm hM hT').1
    · have hz : ¬ (1 ≤ m ∧ t ≤ m) := fun h => hm h.1
      change (S.data m t).R ≤ q
      rw [S.invalid m t hz]
      exact Nat.zero_le _
  have hShapeN := hintScheduleShape_tree H H.n fuel N X Y T hNn hArgs hTree
  have hShapeN' : HintScheduleShape H.n q T := HintScheduleShape.mono le_rfl hCol T hShapeN
  have hInput := hintSynLen_le_of_shape CR H.n q q hRows T X Y (hRoot ▸ hNn) hWF hShapeN'
  have hInput' : synLen CR T ≤ (q * q + q + q) * q :=
    hInput.trans (Nat.mul_le_mul (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_right q hU) hU) _) hCount)
  have hp0 : 0 ≤ q := Nat.zero_le _
  have hp2 : 0 ≤ q ^ 2 := Nat.zero_le _
  have hp3 : 0 ≤ q ^ 3 := Nat.zero_le _
  have hp4 : 0 ≤ q ^ 4 := Nat.zero_le _
  have hHeader : (8 + 16 * (1 + (q + q + 3) * q)) + q * q * (q + 1) + 8 ≤ Q := by
    simp only [Q, hintActualResourceCap]
    nlinarith only [hp0, hp2, hp3, hp4]
  refine ⟨?_, hPad.trans hQ, hCount.trans hQ, ?_,
    (schemeCount_le_nodeCount T).trans (hCount.trans hQ), ?_, ?_, ?_, ?_,
    HintScheduleShape.mono hQ hQ T hShape⟩
  · change 8 + 16 * (1 + upRest Bc T) + upTabLen Bc T + 8 ≤ Q
    have hp := Nat.mul_le_mul_left 16 (Nat.add_le_add_left (Nat.le_of_lt_succ
      (show upRest Bc T < (q + q + 3) * q + 1 from by omega)) 1)
    omega
  · refine hInput'.trans ?_
    simp only [Q, hintActualResourceCap]
    nlinarith only [hp0, hp2, hp3, hp4]
  · refine (show upRest Bc T ≤ (q + q + 3) * q by omega).trans ?_
    simp only [Q, hintActualResourceCap]
    nlinarith only [hp0, hp2, hp3, hp4]
  · refine hTab'.trans ?_
    simp only [Q, hintActualResourceCap]
    nlinarith only [hp0, hp2, hp3, hp4]
  · rw [hRoot]
    exact hNq.trans hQ
  · intro i hi
    have h := hInputs i hi
    obtain ⟨hR, hSpill, hSteps⟩ := hCR _ _ h.positive (h.size.trans hNn) h.capacity
    refine ⟨h.size.trans (hNq.trans hQ), hR.trans hQ, hSpill.trans hQ, hSteps.trans hQ, ?_⟩
    intro X Y he
    obtain ⟨hA, hr⟩ := h.row X Y he
    have hm : 1 ≤ H.rows X Y := by
      rcases hr with hr | hr
      · have hv := rule_recursive_spec hr
        rw [hv.2.2]
        exact one_le_Y_of_recursive (one_le_lg hArgs.1) hv.1 hv.2.2
      · exact one_le_rows_of_ne (rule_direct_spec hr).2.2
    have hK : H.Nmax i.universeSize X Y ≤ i.universeSize := Nmax_le_N
    have hB : H.BY i.universeSize X Y ≤ H.Nmax i.universeSize X Y := min_le_left _ _
    refine ⟨?_, (hintEll_le_colCap hA hm).trans (hCol.trans hQ), hK.trans (h.size.trans (hNq.trans hQ)),
      (hB.trans hK).trans (h.size.trans (hNq.trans hQ)), ?_⟩
    · unfold HintParams.ell
      omega
    · exact up_rows_le_N H i.universeSize X Y (one_le_lg hArgs.1) hA.2.2.2.2.1 hA.2.2.2.2.2

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintWidthResources_of_actual
end -- Def_LinearSetReconciliation327_Main_HintActualWidthResources20261120

section -- Def_LinearSetReconciliation327_Main_HintScalarResources20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintResourceCoefficient (S : CRSourceBundle) (A C : ℕ) (K : ℝ) : ℕ :=
  (48 * (A + C + 2) + 2) + ⌈S.K⌉₊ + ⌈33 * S.K + 184⌉₊ + ⌈K * (A : ℝ)⌉₊ + 2

noncomputable def hintResourceDegree (S : CRSourceBundle) : ℕ := max 54 ⌈S.cW⌉₊

private theorem hintLogPlusTwo_bound (n : ℕ) :
    0 ≤ lg ((n : ℝ) + 2) ∧ lg ((n : ℝ) + 2) ≤ ((n + 2) ^ 2 : ℕ) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hOne : 1 ≤ (n : ℝ) + 2 := by linarith
  refine ⟨lg_nonneg_of_one_le hOne, ?_⟩
  push_cast
  have h := lg_le_two_mul ((n : ℝ) + 2) hOne
  nlinarith [sq_nonneg (n : ℝ)]

private theorem hintCeil_scaledLogPow (R x : ℝ) (n p c : ℕ)
    (hx : 0 ≤ x) (hLog : x ≤ ((n + 2) ^ 2 : ℕ)) (hR : R ≤ (c : ℝ)) :
    ⌈R * x ^ p⌉₊ ≤ c * (n + 2) ^ (2 * p) := by
  apply Nat.ceil_le.mpr
  have hp := pow_le_pow_left₀ hx hLog p
  have h := mul_le_mul hR hp (pow_nonneg hx _) (Nat.cast_nonneg _)
  exact h.trans (by push_cast; rw [pow_mul])

theorem hintRawResources_polynomial (S : CRSourceBundle) (H : HintParams) (K : ℝ) (T : Node)
    (hn : 2 ≤ H.n) (hCount : (T.nodeCount : ℝ) ≤ K * (H.A : ℝ) * H.lgn ^ 27) :
    let q := hintResourceCoefficient S H.A H.C K * (H.n + 2) ^ hintResourceDegree S
    H.n ≤ q ∧ colBc S.K H.n ≤ q ∧ hintEventColCap H ≤ q ∧ T.nodeCount ≤ q ∧
    ∀ m t, 1 ≤ m → m ≤ H.n → t ≤ m →
      (S.data m t).R ≤ q ∧ 2 ^ ((S.data m t).W + 1) ≤ q ∧ crSourceSteps S m t ≤ q := by
  let n := H.n
  let b := n + 2
  let c := hintResourceCoefficient S H.A H.C K
  let p := hintResourceDegree S
  let q := c * b ^ p
  have h54 : 54 ≤ p := le_max_left _ _
  have hB : 1 ≤ b := by unfold b; omega
  have hC1 : 1 ≤ c := by unfold c hintResourceCoefficient; omega
  have hDom (k d : ℕ) (hk : k ≤ c) (hd : d ≤ p) : k * b ^ d ≤ q :=
    Nat.mul_le_mul hk (Nat.pow_le_pow_right hB hd)
  have hN : n ≤ q := by
    apply (Nat.le_add_right n 2).trans
    have h := hDom 1 1 hC1 (by omega)
    simpa only [Nat.one_mul, pow_one] using h
  obtain ⟨hLogP0, hLogP⟩ := hintLogPlusTwo_bound n
  have hLog0 : 0 ≤ H.lgn := by have := one_le_lg hn; change 0 ≤ lg (n : ℝ); linarith
  have hLog : H.lgn ≤ (b ^ 2 : ℕ) := by
    have hPos : (0 : ℝ) < n := by change 0 < (H.n : ℝ); exact_mod_cast (by omega : 0 < H.n)
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) hPos (show (n : ℝ) ≤ (n : ℝ) + 2 by linarith)
    exact h.trans hLogP
  have hPad : colBc S.K n ≤ q := by
    have h := hintCeil_scaledLogPow S.K (lg ((n : ℝ) + 2)) n 2 ⌈S.K⌉₊ hLogP0 hLogP (Nat.le_ceil _)
    unfold colBc
    rw [max_eq_left S.K_pos.le]
    exact h.trans (hDom ⌈S.K⌉₊ 4 (by unfold c hintResourceCoefficient; omega) (by omega))
  have hCols : hintEventColCap H ≤ q := by
    let k := 48 * (H.A + H.C + 2) + 1
    have hk : (48 * ((H.A : ℝ) + H.C + 2) + 1) ≤ (k : ℝ) := by unfold k; push_cast; norm_num
    exact (hintCeil_scaledLogPow _ H.lgn n 3 k hLog0 hLog hk).trans
      (hDom k 6 (by unfold k c hintResourceCoefficient; omega) (by omega))
  have hNodes : T.nodeCount ≤ q := by
    have hc : T.nodeCount ≤ ⌈K * (H.A : ℝ) * H.lgn ^ 27⌉₊ :=
      by exact_mod_cast hCount.trans (Nat.le_ceil _)
    exact hc.trans ((hintCeil_scaledLogPow _ H.lgn n 27 ⌈K * (H.A : ℝ)⌉₊ hLog0 hLog (Nat.le_ceil _)).trans
      (hDom ⌈K * (H.A : ℝ)⌉₊ 54 (by unfold c hintResourceCoefficient; omega) h54))
  refine ⟨hN, hPad, hCols, hNodes, ?_⟩
  intro m t hm hmn ht
  have hSpill := (hintCRSpill_le S hm ht hmn).trans
    (hDom 2 ⌈S.cW⌉₊ (by unfold c hintResourceCoefficient; omega) (le_max_right _ _))
  let k := ⌈33 * S.K + 184⌉₊
  have hSq : lg ((n : ℝ) + 2) ^ 2 ≤ (b ^ 4 : ℕ) := by
    have h := pow_le_pow_left₀ hLogP0 hLogP 2
    exact h.trans (by unfold b; push_cast; ring_nf; exact le_rfl)
  have hM : (m : ℝ) ≤ (b : ℕ) := by
    exact_mod_cast hmn.trans (Nat.le_add_right n 2)
  have hRealCost : (hintCRNodeBudget S m t : ℝ) ≤ (k * b ^ 5 : ℕ) := by
    calc
      _ ≤ (33 * S.K + 184) * (m : ℝ) * lg ((n : ℝ) + 2) ^ 2 := hintCRNodeBudget_le S hm ht hmn
      _ ≤ (k : ℝ) * (b : ℝ) * (b ^ 4 : ℕ) := by gcongr; exact Nat.le_ceil _
      _ = _ := by push_cast; ring
  have hNatCost : hintCRNodeBudget S m t ≤ k * b ^ 5 := by exact_mod_cast hRealCost
  have hCost := hNatCost.trans (hDom k 5 (by unfold k c hintResourceCoefficient; omega) (by omega))
  have hCost' : 17 * (S.data m t).R + 16 * crSourceSteps S m t + 20 * m + 148 ≤ q := hCost
  change (S.data m t).R ≤ q ∧ 2 ^ ((S.data m t).W + 1) ≤ q ∧ crSourceSteps S m t ≤ q
  exact ⟨by omega, hSpill, by omega⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRawResources_polynomial
end -- Def_LinearSetReconciliation327_Main_HintScalarResources20261120

section -- Def_LinearSetReconciliation327_Main_HintActualDecoderLimits20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintWidthScale (coefficient degree : ℕ) : ℕ :=
  let a := 128 * ((128 * (coefficient + 1) ^ 4 + 1) ^ 4)
  Nat.clog 2 (a + 1) + degree * 16 + 1

theorem hintWidthScale_pos (coefficient degree : ℕ) : 1 ≤ hintWidthScale coefficient degree := by
  exact Nat.succ_le_succ (Nat.zero_le _)

theorem hintWidthScale_fits (n coefficient degree base : ℕ) (hBase : 1 ≤ base)
    (hLog : Nat.clog 2 (n + 2) ≤ base) :
    let q := coefficient * (n + 2) ^ degree
    128 * (hintActualResourceCap q + 1) ^ 4 < 2 ^ (4 * (hintWidthScale coefficient degree * base)) := by
  let b := n + 2
  let g := b ^ degree
  let q := coefficient * g
  let a := 128 * (coefficient + 1) ^ 4 + 1
  let coef := 128 * a ^ 4
  let e := degree * 16
  have hg : 1 ≤ g := one_le_pow₀ (by unfold b; omega)
  have hSmall : q + 1 ≤ (coefficient + 1) * g := by
    unfold q
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hLocal : hintActualResourceCap q + 1 ≤ a * g ^ 4 := by
    have hg4 : 1 ≤ g ^ 4 := one_le_pow₀ hg
    have hh : (q + 1) ^ 4 ≤ ((coefficient + 1) * g) ^ 4 := Nat.pow_le_pow_left hSmall _
    calc
      _ ≤ 128 * (((coefficient + 1) * g) ^ 4) + g ^ 4 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hh) hg4
      _ = _ := by unfold a; ring
  have hSize : 128 * (hintActualResourceCap q + 1) ^ 4 ≤ coef * b ^ e := by
    calc
      _ ≤ 128 * ((a * g ^ 4) ^ 4) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLocal _)
      _ = coef * (g ^ (4 * 4)) := by unfold coef; ring
      _ = _ := by unfold g e; rw [← pow_mul]
  have hSpan : Nat.clog 2 (coef + 1) + Nat.clog 2 (n + 2) * e ≤
      4 * (hintWidthScale coefficient degree * base) := by
    calc
      _ ≤ Nat.clog 2 (coef + 1) * base + base * e :=
        Nat.add_le_add (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (Nat.clog 2 (coef + 1)) hBase)
          (Nat.mul_le_mul_right _ hLog)
      _ = (Nat.clog 2 (coef + 1) + e) * base := by ring
      _ ≤ hintWidthScale coefficient degree * base := by
        apply Nat.mul_le_mul_right
        unfold hintWidthScale coef e a
        dsimp only
        omega
      _ ≤ _ := by omega
  exact hSize.trans_lt (hintPolynomial_lt_word n coef e _ hSpan)

theorem hintActualDecoderLimits (S : CRSourceBundle) (H : HintParams) (K : ℝ)
    (fuel N X Y base : ℕ) (T : Node)
    (hArgs : H.NodeArgs N X Y) (hTree : H.tree fuel N X Y = some T)
    (hCount : (T.nodeCount : ℝ) ≤ K * (H.A : ℝ) * H.lgn ^ 27)
    (hBase : 1 ≤ base) (hBaseLog : Nat.clog 2 (H.n + 2) ≤ base) :
    let Bc := colBc S.K H.n
    let growth := hintWidthScale (hintResourceCoefficient S H.A H.C K) (hintResourceDegree S)
    let header := decAfterBase (upRootBase Bc T) (upTabLen Bc T)
    ∃ hT : IsSchemeTree H T, T.N = N ∧ Node.WF T X Y ∧
      HintDecoderLimits S H hT (upWideWord (growth * base)) Bc header := by
  let CR := crFamily S
  let Bc := colBc S.K H.n
  let coefficient := hintResourceCoefficient S H.A H.C K
  let degree := hintResourceDegree S
  let growth := hintWidthScale coefficient degree
  let wide := upWideWord (growth * base)
  let q := coefficient * (H.n + 2) ^ degree
  let header := decAfterBase (upRootBase Bc T) (upTabLen Bc T)
  obtain ⟨hT, hRoot, hWF, hInputs⟩ := hintActualTreeInfo H CR fuel N X Y T hArgs hTree
  obtain ⟨hU, hPad, hCol, hCount', hCR⟩ := hintRawResources_polynomial S H K T hArgs.1 hCount
  change H.n ≤ q at hU
  have hs : UpTreeStatic CR Bc H.n T := by
    apply upTreeStatic_tree CR H Bc ?_ fuel N X Y T hArgs hTree
    intro m t hmn ht i hi
    exact ⟨col_card_le_ceil (crFamily_columns S m t ht i) hmn, crFamily_range S m t i⟩
  have hCaps := hintWidthResources_of_actual S H fuel N X Y Bc q hT hArgs hTree hRoot hWF
    (hInputs 0 0) hU hPad hCol hCount' hCR hs
  have hSpan := hintWidthScale_fits H.n coefficient degree base hBase hBaseLog
  change 128 * (hintActualResourceCap q + 1) ^ 4 < 2 ^ (4 * (growth * base)) at hSpan
  have hHeader : 3 < header := by unfold header decAfterBase upRootBase; omega
  have hG : 1 ≤ growth * base := Nat.mul_pos (hintWidthScale_pos coefficient degree) hBase
  have hHalf : 2 ^ (4 * (growth * base)) ≤ 2 ^ wide :=
    Nat.pow_le_pow_right (by decide) (by unfold wide upWideWord; omega)
  have hQ2 : 2 ≤ q := hArgs.1.trans hU
  have hBig : q ^ 3 ≤ 128 * (hintActualResourceCap q + 1) ^ 4 := by
    have h1 : q ≤ hintActualResourceCap q + 1 := by
      unfold hintActualResourceCap
      nlinarith only [show 0 ≤ q from Nat.zero_le _, show 0 ≤ q ^ 2 from Nat.zero_le _,
        show 0 ≤ q ^ 3 from Nat.zero_le _, show 0 ≤ q ^ 4 from Nat.zero_le _]
    have h2 : (hintActualResourceCap q + 1) ^ 3 ≤ (hintActualResourceCap q + 1) ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    exact (Nat.pow_le_pow_left h1 3).trans (h2.trans (by omega))
  have hQfit : q ^ 3 ≤ 2 ^ wide := hBig.trans (hSpan.le.trans hHalf)
  have hQle : q ≤ q ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ q) (by decide : 1 ≤ 3)
  have hShape := hintScheduleShape_tree H q fuel N X Y T (hArgs.2.2.2.1.trans hU) hArgs hTree
  have hEll : UpEllOK q T :=
    HintScheduleShape.ell T (HintScheduleShape.mono le_rfl hCol T hShape)
  have hDims := UpDimsBound.mono (max_le hU le_rfl) T (upDims_actual_tree H q fuel N X Y T hArgs hTree hEll)
  have hFit : (hintSpec T).Fits wide :=
    upSpecFits_of_dims T q wide (by omega) hDims (hCount'.trans (hQle.trans hQfit))
      hQfit (hQ2.trans (hQle.trans hQfit))
  have hSize : 2 ≤ hintActualResourceCap q := by
    have hPositive : 1 ≤ (q + 1) ^ 4 := one_le_pow₀ (by omega)
    unfold hintActualResourceCap
    omega
  exact ⟨hT, hRoot, hWF, hintDecoderLimits_of_resources S H hT (growth * base) Bc header (hintActualResourceCap q)
    H.n hHeader hG hSize hCaps hs hFit hSpan⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintActualDecoderLimits
end -- Def_LinearSetReconciliation327_Main_HintActualDecoderLimits20261120

section -- Def_LinearSetReconciliation327_Main_HintRowCostExp20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintRowCallCap_le_pow (U R : ℕ) (hR : R ≤ U) :
    hintRowCallCap U R ≤ 65536 * (U + 1) ^ (R + 5) := by
  let x := U + 1
  let p := x ^ R
  let Q := x ^ 3 * p
  let V := x ^ 5 * p
  have hx : 1 ≤ x := by omega
  have hxU : U ≤ x := by omega
  have hxR : R + 1 ≤ x := Nat.add_le_add_right hR 1
  have hx2 : x ≤ x ^ 2 := by
    simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left x hx
  have hx3 : x ^ 2 ≤ x ^ 3 := pow_le_pow_right₀ hx (by decide)
  have hp : 1 ≤ p := one_le_pow₀ hx
  have hXQ : x ≤ Q := (hx2.trans hx3).trans (by
    change x ^ 3 ≤ x ^ 3 * p
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (x ^ 3) hp)
  have hQV : Q ≤ V := Nat.mul_le_mul_right _ (pow_le_pow_right₀ hx (by decide))
  have hVV : x * (x * Q) = V := by
    unfold Q V
    ring
  have hXX : x * Q ≤ V := by
    rw [← hVV]
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (x * Q) hx
  have hGauss : (U + U + 1) ^ 3 ≤ 8 * x ^ 3 := by
    calc
      _ ≤ (2 * x) ^ 3 := Nat.pow_le_pow_left (by omega : U + U + 1 ≤ 2 * x) 3
      _ = 8 * x ^ 3 := by ring
  have hUU : U * U ≤ x ^ 3 :=
    (by simpa only [pow_two] using Nat.mul_le_mul hxU hxU : U * U ≤ x ^ 2).trans hx3
  have hUX : U ≤ x ^ 3 := hxU.trans (hx2.trans hx3)
  have hUnit : 1 ≤ x ^ 3 := one_le_pow₀ hx
  have hCross : (20 * U + 50) * U ≤ 70 * x ^ 3 := by
    rw [Nat.add_mul, Nat.mul_assoc]
    omega
  have hScan : hintScanCostCap U + 2 ≤ 5000 * x ^ 3 := by
    unfold hintScanCostCap
    rw [Nat.mul_assoc 11 U U]
    omega
  have hExp : (hintScanCostCap U + 2) * p ≤ 5000 * Q := by
    simpa only [Q, Nat.mul_assoc] using Nat.mul_le_mul_right p hScan
  have hIter : hintRowIterationCap U R ≤ 10250 * Q := by
    change 50 * U + 200 + 2 * ((hintScanCostCap U + 2) * p) ≤ _
    omega
  let B := (R + 1) * hintRowIterationCap U R
  have hB : B ≤ 10250 * (x * Q) := by
    calc
      B ≤ x * (10250 * Q) := Nat.mul_le_mul hxR hIter
      _ = _ := by ring
  have hIterated : (B + 2) * (R + 1) ≤ 10250 * V + 2 * x := by
    calc
      _ ≤ (10250 * (x * Q) + 2) * x := Nat.mul_le_mul (Nat.add_le_add_right hB _) hxR
      _ = 10250 * (x * (x * Q)) + 2 * x := by ring
      _ = _ := by rw [hVV]
  have hxV : x ≤ V := hXQ.trans hQV
  have hBV : B ≤ 10250 * V := hB.trans (Nat.mul_le_mul_left _ hXX)
  have hGoal : hintRowCallCap U R ≤ 65536 * V := by
    change (B + 2) * (R + 1) + B + 64 * U + 8 * R + 470 ≤ _
    omega
  simpa only [V, p, x, pow_add, Nat.mul_comm ((U + 1) ^ 5) ((U + 1) ^ R)] using hGoal

theorem hintRowCallCap_le_exp (U R : ℕ) (hR : R ≤ U) (L a b : ℝ)
    (hL : 1 ≤ L) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hU : Real.log ((U : ℝ) + 1) ≤ a * (Real.log L + 1))
    (hRlog : (R : ℝ) + 5 ≤ b * (Real.log L + 1)) :
    (hintRowCallCap U R : ℝ) ≤ 65536 * Real.exp (2 * a * b) *
      Real.exp (2 * a * b * (Real.log L) ^ 2) := by
  have hq : 0 ≤ Real.log L := Real.log_nonneg hL
  have hx : 0 < (U : ℝ) + 1 := by positivity
  have hLog : 0 ≤ Real.log ((U : ℝ) + 1) := Real.log_nonneg (by have hu : 0 ≤ (U : ℝ) := Nat.cast_nonneg _; linarith)
  have hProd := mul_le_mul hRlog hU hLog (mul_nonneg hb (by linarith : 0 ≤ Real.log L + 1))
  have hExponent : ((R : ℝ) + 5) * Real.log ((U : ℝ) + 1) ≤
      2 * a * b + 2 * a * b * (Real.log L) ^ 2 := by
    refine hProd.trans ?_
    have hSquare : (Real.log L + 1) ^ 2 ≤ 2 * (1 + (Real.log L) ^ 2) := by
      nlinarith only [sq_nonneg (Real.log L - 1)]
    calc
      _ = (a * b) * (Real.log L + 1) ^ 2 := by ring
      _ ≤ (a * b) * (2 * (1 + (Real.log L) ^ 2)) := mul_le_mul_of_nonneg_left hSquare (mul_nonneg ha hb)
      _ = _ := by ring
  have hNat := hintRowCallCap_le_pow U R hR
  have hCast : (hintRowCallCap U R : ℝ) ≤ 65536 * ((U : ℝ) + 1) ^ (R + 5) := by
    exact_mod_cast hNat
  calc
    _ ≤ 65536 * ((U : ℝ) + 1) ^ (R + 5) := hCast
    _ = 65536 * Real.exp (((R : ℝ) + 5) * Real.log ((U : ℝ) + 1)) := by
      rw [show (R : ℝ) + 5 = ((R + 5 : ℕ) : ℝ) from by push_cast; rfl, Real.exp_nat_mul, Real.exp_log hx]
    _ ≤ 65536 * Real.exp (2 * a * b + 2 * a * b * (Real.log L) ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExponent) (by norm_num)
    _ = _ := by rw [Real.exp_add]; exact (mul_assoc _ _ _).symm

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRowCallCap_le_exp
end -- Def_LinearSetReconciliation327_Main_HintRowCostExp20261120

section -- Def_LinearSetReconciliation327_Main_HintActualRowCost20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintRowSizeFactor (A C : ℕ) : ℕ := 48 * (A + C + 2) + 6

noncomputable def hintUniformRowSize (H : HintParams) : ℕ :=
  ⌈(hintRowSizeFactor H.A H.C : ℝ) * H.lgn ^ 13⌉₊

noncomputable def hintUniformOutside (H : HintParams) : ℕ :=
  min (hintUniformRowSize H) ⌈(H.C : ℝ) * (lg H.lgn + 2) + 5⌉₊

noncomputable def hintRowLogFactor (A C : ℕ) : ℝ :=
  Real.log ((hintRowSizeFactor A C : ℝ) + 2) + 13

noncomputable def hintOutsideLogFactor (C : ℕ) : ℝ :=
  (C : ℝ) / Real.log 2 + 2 * (C : ℝ) + 11

noncomputable def hintRowExpRate (A C : ℕ) : ℝ :=
  2 * hintRowLogFactor A C * hintOutsideLogFactor C

theorem hintUniformRowSize_bounds (H : HintParams) {N X Y : ℕ}
    (hArgs : H.NodeArgs N X Y) (hNonLeaf : H.NonLeaf N X Y) :
    let U := hintUniformRowSize H
    let R := hintUniformOutside H
    H.Nmax N X Y ≤ U ∧ H.ell N X Y ≤ U ∧ H.BY N X Y ≤ R ∧ R ≤ U := by
  let U := hintUniformRowSize H
  have hL : 1 ≤ H.lgn := one_le_lg hArgs.1
  have hK := hintNmax_le_nonleaf H hL hNonLeaf
  have hEll : 1 ≤ H.rows X Y := by
    rcases hNonLeaf with hr | hd
    · have h := rule_recursive_spec hr
      rw [h.2.2]
      exact one_le_Y_of_recursive hL h.1 h.2.2
    · exact one_le_rows_of_ne (rule_direct_spec hd).2.2
  have hs : (3 : ℝ) ≤ (hintRowSizeFactor H.A H.C : ℝ) := by
    unfold hintRowSizeFactor
    push_cast
    have ha : 0 ≤ (H.A : ℝ) := Nat.cast_nonneg _
    have hc : 0 ≤ (H.C : ℝ) := Nat.cast_nonneg _
    linarith
  have hU : (hintRowSizeFactor H.A H.C : ℝ) * H.lgn ^ 13 ≤ (U : ℝ) := Nat.le_ceil _
  have hU' : H.Nmax N X Y ≤ U := by
    exact_mod_cast hK.trans ((mul_le_mul_of_nonneg_right hs (by positivity)).trans hU)
  have hCompare : (48 * ((H.A : ℝ) + H.C + 2) + 1) * H.lgn ^ 3 ≤
      (hintRowSizeFactor H.A H.C : ℝ) * H.lgn ^ 13 := by
    have hh : H.lgn ^ 3 ≤ H.lgn ^ 13 := pow_le_pow_right₀ hL (by decide)
    apply mul_le_mul _ hh (by positivity) (Nat.cast_nonneg _)
    unfold hintRowSizeFactor
    push_cast
    linarith
  have hSteps : H.ell N X Y ≤ U := (hintEll_le_colCap hArgs hEll).trans (Nat.ceil_le.mpr (hCompare.trans hU))
  have hBY : H.BY N X Y ≤ H.Nmax N X Y := min_le_left _ _
  exact ⟨hU', hSteps, le_min (hBY.trans hU') (by
    exact_mod_cast (hintBY_le_loglog H N X Y hL).trans (Nat.le_ceil _)), min_le_left _ _⟩

theorem hintUniformRowCost_le (H : HintParams) (hn : 2 ≤ H.n) :
    (hintRowCallCap (hintUniformRowSize H) (hintUniformOutside H) : ℝ) ≤
      65536 * Real.exp (hintRowExpRate H.A H.C) * Real.exp (hintRowExpRate H.A H.C * (lg H.lgn) ^ 2) := by
  let L := H.lgn
  let U := hintUniformRowSize H
  let R := hintUniformOutside H
  let k := (hintRowSizeFactor H.A H.C : ℝ)
  let a := hintRowLogFactor H.A H.C
  let b := hintOutsideLogFactor H.C
  have hL : 1 ≤ L := one_le_lg hn
  have hln := Real.log_nonneg hL
  have hLpos : 0 < L := by linarith
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have ha0 : 0 ≤ Real.log (k + 2) := Real.log_nonneg (by linarith)
  have hTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 ≤ (H.C : ℝ) := Nat.cast_nonneg _
  have ha : 0 ≤ a := by change 0 ≤ Real.log (k + 2) + 13; linarith
  have hb : 0 ≤ b := by unfold b hintOutsideLogFactor; positivity
  have hU : (U : ℝ) + 1 ≤ (k + 2) * L ^ 13 := by
    have hCeil : (U : ℝ) < k * L ^ 13 + 1 := Nat.ceil_lt_add_one (mul_nonneg hk (by positivity))
    have hP : 1 ≤ L ^ 13 := one_le_pow₀ hL
    nlinarith only [hCeil, hP]
  have hLogU : Real.log ((U : ℝ) + 1) ≤ a * (Real.log L + 1) := by
    calc
      _ ≤ Real.log ((k + 2) * L ^ 13) := Real.log_le_log (by positivity) hU
      _ = Real.log (k + 2) + 13 * Real.log L := by rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; norm_num
      _ ≤ _ := by
        change _ ≤ (Real.log (k + 2) + 13) * (Real.log L + 1)
        nlinarith only [mul_nonneg ha0 hln]
  have hLogR : (R : ℝ) + 5 ≤ b * (Real.log L + 1) := by
    have hCeil : (⌈(H.C : ℝ) * (lg L + 2) + 5⌉₊ : ℝ) < (H.C : ℝ) * (lg L + 2) + 6 := by
      have hLg := lg_nonneg_of_one_le hL
      have hExpr : 0 ≤ (H.C : ℝ) * (lg L + 2) + 5 := by positivity
      have hh := Nat.ceil_lt_add_one hExpr
      linarith
    have hMin : (R : ℝ) ≤ (⌈(H.C : ℝ) * (lg L + 2) + 5⌉₊ : ℝ) := by
      exact_mod_cast (show R ≤ ⌈(H.C : ℝ) * (lg L + 2) + 5⌉₊ from min_le_right _ _)
    have hcL : 0 ≤ (H.C : ℝ) / Real.log 2 := div_nonneg hc hTwo.le
    have ht : (H.C : ℝ) * lg L = ((H.C : ℝ) / Real.log 2) * Real.log L := by
      change (H.C : ℝ) * (Real.log L / Real.log 2) = _
      ring
    change _ ≤ (((H.C : ℝ) / Real.log 2) + 2 * (H.C : ℝ) + 11) * (Real.log L + 1)
    nlinarith only [hMin, hCeil, ht, hcL, hln, mul_nonneg hc hln]
  have hReal := hintRowCallCap_le_exp U R (min_le_left _ _) L a b hL ha hb hLogU hLogR
  have hTwoLE : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hLg : Real.log L ≤ lg L := by
    change Real.log L ≤ Real.log L / Real.log 2
    exact (le_div_iff₀ hTwo).mpr (mul_le_of_le_one_right hln hTwoLE)
  have hSq := pow_le_pow_left₀ hln hLg 2
  apply hReal.trans
  have hRate : 0 ≤ 2 * a * b := by positivity
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hSq hRate)) (by positivity)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintUniformRowSize_bounds
#print axioms LinearSetReconciliation327.Main.hintUniformRowCost_le
end -- Def_LinearSetReconciliation327_Main_HintActualRowCost20261120

section -- Def_LinearSetReconciliation327_Main_HintCombinedTime20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintLogPower_le_exp (L : ℝ) (hL : 1 ≤ L) (p : ℕ) :
    L ^ p ≤ Real.exp ((p : ℝ) / 2) * Real.exp (((p : ℝ) / 2) * (lg L) ^ 2) := by
  have hPos : 0 < L := by linarith
  have hLog := Real.log_nonneg hL
  have hTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hTwo' : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hLg : Real.log L ≤ lg L := by
    change Real.log L ≤ Real.log L / Real.log 2
    apply (le_div_iff₀ hTwo).mpr
    exact mul_le_of_le_one_right hLog hTwo'
  have hSq : Real.log L ≤ (1 + (lg L) ^ 2) / 2 := by
    nlinarith [sq_nonneg (lg L - 1)]
  have hExp : (p : ℝ) * Real.log L ≤ (p : ℝ) / 2 + ((p : ℝ) / 2) * (lg L) ^ 2 := by
    calc
      _ ≤ (p : ℝ) * ((1 + (lg L) ^ 2) / 2) := mul_le_mul_of_nonneg_left hSq (Nat.cast_nonneg p)
      _ = _ := by ring
  rw [← Real.exp_add]
  calc
    L ^ p = (Real.exp (Real.log L)) ^ p := congrArg (fun z : ℝ => z ^ p) (Real.exp_log hPos).symm
    _ = Real.exp ((p : ℝ) * Real.log L) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hExp

noncomputable def hintCombinedTimeConstant (A B c : ℝ) (p q : ℕ) : ℝ :=
  max 1 (max (A * Real.exp ((p : ℝ) / 2) + B * Real.exp ((q : ℝ) / 2) + 96)
    (c + (p : ℝ) / 2 + (q : ℝ) / 2))

theorem hintCombinedTimeConstant_pos (A B c : ℝ) (p q : ℕ) :
    0 < hintCombinedTimeConstant A B c p q :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem hintCombinedTime_le (L N A B c : ℝ) (p q : ℕ)
    (hL : 1 ≤ L) (hN : 1 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ c) :
    let C := hintCombinedTimeConstant A B c p q
    A * N * L ^ p * Real.exp (c * (lg L) ^ 2) + B * N * L ^ q + 29 * N + 67 ≤
      C * N * Real.exp (C * (lg L) ^ 2) := by
  let C := hintCombinedTimeConstant A B c p q
  let s := (lg L) ^ 2
  let ep := Real.exp ((p : ℝ) / 2)
  let eq := Real.exp ((q : ℝ) / 2)
  let error := Real.exp (C * s)
  have hs : 0 ≤ s := sq_nonneg _
  have hC : 0 < C := hintCombinedTimeConstant_pos A B c p q
  have hCost : A * ep + B * eq + 96 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hRate : c + (p : ℝ) / 2 + (q : ℝ) / 2 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hRateP : c + (p : ℝ) / 2 ≤ C := by
    exact le_trans (by have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _; linarith) hRate
  have hRateQ : (q : ℝ) / 2 ≤ C := by
    exact le_trans (by have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg _; linarith) hRate
  have hOne : 1 ≤ error := by
    change 1 ≤ Real.exp (C * s)
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg hC.le hs)
  have hP : A * N * L ^ p * Real.exp (c * s) ≤ A * ep * N * error := by
    calc
      _ ≤ A * N * (ep * Real.exp (((p : ℝ) / 2) * s)) * Real.exp (c * s) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hintLogPower_le_exp L hL p)
          (mul_nonneg hA (by linarith))) (Real.exp_nonneg _)
      _ = A * ep * N * Real.exp ((c + (p : ℝ) / 2) * s) := by
        rw [add_mul, Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hRateP hs))
          (mul_nonneg (mul_nonneg hA (Real.exp_nonneg _)) (by linarith))
  have hQ : B * N * L ^ q ≤ B * eq * N * error := by
    calc
      _ ≤ B * N * (eq * Real.exp (((q : ℝ) / 2) * s)) :=
        mul_le_mul_of_nonneg_left (hintLogPower_le_exp L hL q) (mul_nonneg hB (by linarith))
      _ = B * eq * N * Real.exp (((q : ℝ) / 2) * s) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hRateQ hs))
          (mul_nonneg (mul_nonneg hB (Real.exp_nonneg _)) (by linarith))
  have hRest : 29 * N + 67 ≤ 96 * N * error := by
    calc
      _ ≤ 96 * N := by linarith
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hOne (by linarith : 0 ≤ 96 * N)
  change A * N * L ^ p * Real.exp (c * s) + B * N * L ^ q + 29 * N + 67 ≤ C * N * error
  calc
    _ ≤ A * ep * N * error + B * eq * N * error + (96 * N * error) := by linarith only [hP, hQ, hRest]
    _ = (A * ep + B * eq + 96) * N * error := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCost (by linarith))
      (Real.exp_nonneg _)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintCombinedTime_le
end -- Def_LinearSetReconciliation327_Main_HintCombinedTime20261120

section -- Def_LinearSetReconciliation327_Main_HintScheduledCost20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintScheduledRunBudget_le (S : CRSourceBundle) (events : List HintTreeEvent) (N : ℕ)
    (budget : ℕ → ℕ) (base extra : ℕ) (L A B E F rate : ℝ) (p q t : ℕ)
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hRate : 0 ≤ rate)
    (hLocal : HintBudgetFollows events 0 events.length budget (fun e => base + (if e.linearWork then extra else 0)))
    (hLength : (events.length : ℝ) ≤ E * N * L ^ p)
    (hLinear : ((events.filter HintTreeEvent.linearWork).length : ℝ) ≤ F * L ^ q)
    (hBase : (base : ℝ) + 44 ≤ A * Real.exp (rate * (lg L) ^ 2))
    (hExtra : (extra : ℝ) ≤ B * N * L ^ t) :
    let C := hintCombinedTimeConstant (A * E) (B * F) rate p (q + t)
    (hintPhaseRunBudget S events.length N budget : ℝ) ≤ C * N * Real.exp (C * (lg L) ^ 2) := by
  let C := hintCombinedTimeConstant (A * E) (B * F) rate p (q + t)
  have hR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hSum : (hintPhaseRunBudget S events.length N budget : ℝ) ≤
      ((base : ℝ) + 44) * events.length + (extra : ℝ) * (events.filter HintTreeEvent.linearWork).length + 29 * N + 67 := by
    exact_mod_cast hintPhaseRunBudget_of_follows S events N budget base extra hLocal
  have hMain : ((base : ℝ) + 44) * events.length ≤ (A * E) * N * L ^ p * Real.exp (rate * (lg L) ^ 2) := by
    calc
      _ ≤ (A * Real.exp (rate * (lg L) ^ 2)) * (E * (N : ℝ) * L ^ p) :=
        mul_le_mul hBase hLength (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hLarge : (extra : ℝ) * (events.filter HintTreeEvent.linearWork).length ≤ (B * F) * N * L ^ (q + t) := by
    calc
      _ ≤ (B * (N : ℝ) * L ^ t) * (F * L ^ q) := mul_le_mul hExtra hLinear (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [pow_add]; ring
  refine hSum.trans (le_trans ?_ (hintCombinedTime_le L N (A * E) (B * F) rate p (q + t)
    hL hR (mul_nonneg hA hE) (mul_nonneg hB hF) hRate))
  linarith only [hMain, hLarge]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintScheduledRunBudget_le
end -- Def_LinearSetReconciliation327_Main_HintScheduledCost20261120

section -- Def_LinearSetReconciliation327_Main_HintTimeScalars20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintLogAddTwo_square_le (H : HintParams) (hn : 2 ≤ H.n) :
    lg ((H.n : ℝ) + 2) ^ 2 ≤ 4 * H.lgn ^ 2 := by
  have hL : 1 ≤ H.lgn := one_le_lg hn
  have hPos : 0 ≤ lg ((H.n : ℝ) + 2) :=
    Real.logb_nonneg (by norm_num) (by norm_cast; omega)
  have hLe : lg ((H.n : ℝ) + 2) ≤ 2 * H.lgn := by
    have hLog : lg ((H.n : ℝ) + 2) ≤ H.lgn + 1 := lg_add_two_le hn
    linarith
  calc
    _ ≤ (2 * H.lgn) ^ 2 := pow_le_pow_left₀ hPos hLe _
    _ = _ := by ring

noncomputable def hintCRTimeCap (S : CRSourceBundle) (H : HintParams) (N : ℕ) : ℕ :=
  ⌈(4 * (33 * S.K + 184)) * N * H.lgn ^ 2⌉₊

theorem hintCRTimeCap_bounds (S : CRSourceBundle) (H : HintParams) {N m t : ℕ}
    (hn : 2 ≤ H.n) (hNn : N ≤ H.n) (hm : 1 ≤ m) (hmN : m ≤ N) (ht : t ≤ m) :
    hintCRNodeBudget S m t ≤ hintCRTimeCap S H N := by
  have hM : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have hA : 0 ≤ 33 * S.K + 184 := by linarith [S.K_pos]
  have h : (hintCRNodeBudget S m t : ℝ) ≤ (4 * (33 * S.K + 184)) * N * H.lgn ^ 2 := by
    calc
      _ ≤ (33 * S.K + 184) * (m : ℝ) * lg ((H.n : ℝ) + 2) ^ 2 := hintCRNodeBudget_le S hm ht (hmN.trans hNn)
      _ ≤ (33 * S.K + 184) * (N : ℝ) * (4 * H.lgn ^ 2) := by gcongr; exact hintLogAddTwo_square_le H hn
      _ = _ := by ring
  exact_mod_cast h.trans (Nat.le_ceil _)

theorem hintCRTimeCap_real_le (S : CRSourceBundle) (H : HintParams) {N : ℕ}
    (hn : 2 ≤ H.n) (hN : 1 ≤ N) :
    (hintCRTimeCap S H N : ℝ) ≤ (4 * (33 * S.K + 184) + 1) * N * H.lgn ^ 2 := by
  have hL : 1 ≤ H.lgn := one_le_lg hn
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNL : 1 ≤ (N : ℝ) * H.lgn ^ 2 := one_le_mul_of_one_le_of_one_le hN' (one_le_pow₀ hL)
  have hK := S.K_pos.le
  unfold hintCRTimeCap
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  nlinarith only [hNL]

theorem hintTime_cols_le (H : HintParams) (hn : 2 ≤ H.n) :
    (hintEventColCap H : ℝ) ≤ (48 * ((H.A : ℝ) + H.C + 2) + 2) * H.lgn ^ 3 := by
  have hL : 1 ≤ H.lgn := one_le_lg hn
  have hL3 : 1 ≤ H.lgn ^ 3 := one_le_pow₀ hL
  have hL0 : 0 ≤ H.lgn := by linarith
  unfold hintEventColCap
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  nlinarith only [hL3]

theorem hintTime_padding_le (S : CRSourceBundle) (H : HintParams) (hn : 2 ≤ H.n) :
    (colBc S.K H.n : ℝ) ≤ (4 * S.K + 1) * H.lgn ^ 2 := by
  have hL : 1 ≤ H.lgn := one_le_lg hn
  have hL2 : 1 ≤ H.lgn ^ 2 := one_le_pow₀ hL
  have hK := S.K_pos.le
  unfold colBc
  rw [max_eq_left hK]
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  have hs := mul_le_mul_of_nonneg_left (hintLogAddTwo_square_le H hn) hK
  nlinarith only [hs, hL2]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintCRTimeCap_bounds
#print axioms LinearSetReconciliation327.Main.hintTime_cols_le
#print axioms LinearSetReconciliation327.Main.hintTime_padding_le
end -- Def_LinearSetReconciliation327_Main_HintTimeScalars20261120

section -- Def_LinearSetReconciliation327_Main_HintTreeTimeCaps20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintDecBase (H : HintParams) (Bc records : ℕ) : ℕ :=
  hintRowCallCap (hintUniformRowSize H) (hintUniformOutside H) + 147 * (1 + Bc + records) + 24

noncomputable def hintDecExtra (S : CRSourceBundle) (H : HintParams) (N bits : ℕ) : ℕ :=
  17 * bits + 13 + hintCRTimeCap S H N + (12 * N + 12)

private theorem hintRowTimeBounds_of_nodeInput (S : CRSourceBundle) (H : HintParams)
    (N Bc bits records m X Y t : ℕ) (hn : 2 ≤ H.n) (hNn : N ≤ H.n)
    (hm : m ≤ N) (hArgs : H.NodeArgs m X Y) (hNonLeaf : H.NonLeaf m X Y) (ht : t ≤ m) :
    HintRowTimeBounds S H m X Y t Bc (hintUniformRowSize H) (hintUniformOutside H)
      (hintDecBase H Bc records) (hintDecExtra S H N bits) := by
  obtain ⟨hKeys, hColumns, hBY, hRU⟩ := hintUniformRowSize_bounds H hArgs hNonLeaf
  have hCR := hintCRTimeCap_bounds S H hn hNn hArgs.2.2.1 hm ht
  refine ⟨hKeys, hColumns, hBY, hRU, ?_, ?_, ?_, ?_, ?_⟩
  · unfold hintDecBase
    omega
  · have hCopy : 17 * (S.data m t).R + 13 ≤ hintCRNodeBudget S m t := by
      unfold hintCRNodeBudget
      omega
    unfold hintDecExtra
    omega
  · unfold hintDecBase
    omega
  · unfold hintDecExtra
    omega
  · unfold hintDecExtra
    omega

theorem hintTreeTimeBounds_of_inputs (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (N Bc bits records : ℕ) (hn : 2 ≤ H.n) (hNn : N ≤ H.n) :
    ∀ (node seed : ℕ),
      (∀ info ∈ hintNodeInfos (crFamily S) hT node seed, HintActualNodeInput H N info) →
      synLen (crFamily S) T ≤ bits → upRest Bc T ≤ records →
      HintTreeTimeBounds S H Bc (hintUniformRowSize H) (hintUniformOutside H)
        (hintDecBase H Bc records) (hintDecExtra S H N bits) hT := by
  induction hT with
  | store m =>
    intro node seed hInputs _ _
    have hw := hInputs (hintNodeInfo (P := H) (crFamily S) (.store m) node seed) (by simp [hintNodeInfos])
    have hm : m ≤ N := hw.size
    change 12 * m + 12 ≤ hintDecExtra S H N bits
    unfold hintDecExtra
    omega
  | cr m t =>
    intro node seed hInputs _ _
    have hw := hInputs (hintNodeInfo (P := H) (crFamily S) (.cr m t) node seed) (by simp [hintNodeInfos])
    have hCR := hintCRTimeCap_bounds S H (m := m) (t := t) hn hNn hw.positive hw.size hw.capacity
    change hintCRNodeBudget S m t ≤ hintDecExtra S H N bits
    unfold hintDecExtra
    omega
  | direct m X Y t =>
    intro node seed hInputs _ _
    have hw := hInputs (hintNodeInfo (P := H) (crFamily S) (.direct m X Y t) node seed) (by simp [hintNodeInfos])
    obtain ⟨hArgs, hNonLeaf⟩ := hw.row X Y rfl
    exact hintRowTimeBounds_of_nodeInput S H N Bc bits records m X Y t hn hNn hw.size hArgs hNonLeaf hw.capacity
  | recursive m X Y t Xs Ys kids hc ih =>
    intro node seed hInputs hBits hRecords
    let sch := H.scheme m X Y
    let rt : IsSchemeTree H (.recursive sch t Xs Ys kids) := .recursive m X Y t Xs Ys kids hc
    have hw := hInputs (hintNodeInfo (P := H) (crFamily S) rt node seed) (by simp [rt, hintNodeInfos])
    obtain ⟨hArgs, hNonLeaf⟩ := hw.row X Y rfl
    have hm : m ≤ N := hw.size
    have hrows : (H.scheme m X Y).m ≤ m := up_rows_le_N H m X Y (one_le_lg hn) hArgs.2.2.2.2.1 hArgs.2.2.2.2.2
    refine ⟨hintRowTimeBounds_of_nodeInput S H N Bc bits records m X Y t hn hNn hm hArgs hNonLeaf hw.capacity, ?_, ?_⟩
    · unfold hintDecExtra
      omega
    · intro col
      have hSyn : synLen (crFamily S) (kids col) ≤ bits := by
        have hSum : synLen (crFamily S) (kids col) ≤ ∑ j, synLen (crFamily S) (kids j) :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (synLen (crFamily S) (kids j))) (Finset.mem_univ col)
        exact hSum.trans ((Nat.le_add_right _ _).trans hBits)
      have hRest : upRest Bc (kids col) ≤ records := by
        have hSum : 2 + upRest Bc (kids col) ≤ ∑ j, (2 + upRest Bc (kids j)) :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (2 + upRest Bc (kids j))) (Finset.mem_univ col)
        exact (Nat.le_add_left _ _).trans (hSum.trans ((Nat.le_add_left _ _).trans hRecords))
      refine ⟨?_, ?_, ih col (hintChildPhysicalIndex kids node col) (hintChildSchemeIndex kids seed col) ?_ hSyn hRest⟩
      · unfold hintDecExtra
        omega
      · unfold hintDecBase
        omega
      · intro info hi
        apply hInputs info
        rw [hintNodeInfos]
        exact List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨col, rfl⟩, hi⟩)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintTreeTimeBounds_of_inputs
end -- Def_LinearSetReconciliation327_Main_HintTreeTimeCaps20261120


