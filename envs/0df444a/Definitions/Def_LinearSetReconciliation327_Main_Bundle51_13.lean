-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_13
-- name    : LinearSetReconciliation327_Main_Bundle51_13
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T08:05:45.474309+00:00
-- url     : https://prove2.me/theorems/2c0ac693-77fc-4ac3-a870-140dbbd6a2f6
-- title:
--   LinearSetReconciliation327 鈥?Bundle51_13
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_13` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_09
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_10
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_11
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_11a
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_12

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_13
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintDirectReadAtPhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintNodeEventSlices20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRecursiveRowsPhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRecursiveFold20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedMemory20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPublicRow20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedColumn20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintStoreAtPhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintCRAtPhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedLeaves20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedBinaryLeaves20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintBinarySubtree20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintEventCount20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPhaseBudgetSum20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintEventWorkCount20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintBudgetFollows20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintBinaryNodeResidual20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintResidualBudget20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintDirectReadAtPhase20261120
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
end -- Def_LinearSetReconciliation327_Main_HintDirectReadAtPhase20261120

section -- Def_LinearSetReconciliation327_Main_HintNodeEventSlices20261120
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
end -- Def_LinearSetReconciliation327_Main_HintNodeEventSlices20261120

section -- Def_LinearSetReconciliation327_Main_HintRecursiveRowsPhase20261120
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
end -- Def_LinearSetReconciliation327_Main_HintRecursiveRowsPhase20261120

section -- Def_LinearSetReconciliation327_Main_HintRecursiveFold20261120
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
end -- Def_LinearSetReconciliation327_Main_HintRecursiveFold20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedMemory20261120
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
end -- Def_LinearSetReconciliation327_Main_HintPlacedMemory20261120

section -- Def_LinearSetReconciliation327_Main_HintPublicRow20261120
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
end -- Def_LinearSetReconciliation327_Main_HintPublicRow20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedColumn20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintWordSpan_lt (W word bits limit : ℕ) (hW : 0 < W)
    (hSpan : word + wordsOf W bits ≤ limit) (hFit : limit * W < 2 ^ W) :
    word * W + bits < 2 ^ W := by
  have h := Nat.mul_le_mul_right W hSpan
  rw [Nat.add_mul] at h
  have hCover := up_words_cover_budget W bits hW
  exact (Nat.add_le_add_left hCover _).trans_lt (h.trans_lt hFit)

noncomputable def hintPlacedColumn_phase (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (seedData : (hintSpec R).Seed) (up previous : ℕ → ℕ)
    (W Bc header node seed first N X Y t : ℕ)
    (Xs Ys : Fin (H.scheme N X Y).ℓ → ℕ) (children : Fin (H.scheme N X Y).ℓ → Node)
    (hchildren : ∀ col, IsSchemeTree H (children col))
    (x J : Finset ℕ) (col : Fin (H.scheme N X Y).ℓ)
    (hHeader : 3 < header) (hW : 0 < W) (hWord : 30 < 2 ^ W) (hBc : Bc + 1 < 2 ^ W)
    (hFit : (hintSpec R).Fits W)
    (hSeedFit : seed < 2 ^ W) (hKFit : H.Nmax N X Y < 2 ^ W)
    (hStepsFit : H.ell N X Y < 2 ^ W) (hBXFit : H.BX N X Y < 2 ^ W)
    (hBYFit : H.BY N X Y + 1 < 2 ^ W)
    (hm : H.rows X Y ≤ N) (hSize : (children col).N = (H.scheme N X Y).m)
    (hSteps : 0 < H.ell N X Y)
    (hDims : UpDimsBound (2 ^ W - 1) (children col))
    (hStatic : UpTreeStatic (crFamily S) Bc (children col).N (children col))
    (hChildSeed : hintChildSchemeIndex children seed col + (schemeNodes (children col)).length < 2 ^ W) :
    let sch := H.scheme N X Y
    let T := Node.recursive sch t Xs Ys children
    let hT : IsSchemeTree H T := .recursive N X Y t Xs Ys children hchildren
    let D := hintDecoderTables S H hR W Bc header
    let L := D.placement
    let E := (hintSpec R).env W (D.det S H up previous header R.N) seedData
    let offsets := fun i => L.inputWord i * W
    let r := hintKappaAux H R seedData T hT seed
    BlockOf R seed (schemeNodes T) →
    HintPlacedSubtree (crFamily S) H D hT node seed →
    (node = 0 → synLen (crFamily S) T ≤ synLen (crFamily S) R) →
    hintArenaStart D.heap D.stride D.infos.length * W < 2 ^ W →
    hintDecoderDetEnd S H D header < 2 ^ W →
    HintEventSlice D first (hintRecursiveColumnEvents (crFamily S) offsets sch children node seed (offsets node) col) →
    HintColumnPhase S H D E header node seed first t sch Xs Ys children r x J col := by
  let sch := H.scheme N X Y
  let CR := crFamily S
  let T := Node.recursive sch t Xs Ys children
  let hT : IsSchemeTree H T := .recursive N X Y t Xs Ys children hchildren
  let D := hintDecoderTables S H hR W Bc header
  let L := D.placement
  let det := D.det S H up previous header R.N
  let E := (hintSpec R).env W det seedData
  let r := hintKappaAux H R seedData T hT seed
  let cn := hintChildPhysicalIndex children node col
  let cs := hintChildSchemeIndex children seed col
  let C := children col
  let A := L.arena node
  let B := L.arena cn
  let arena := hintArenaStart D.heap D.stride
  let maxAddr := arena D.infos.length
  let last := arena (cn + C.nodeCount)
  dsimp only
  intro hBlock hPlaced hRoot hMem hDet hSlice
  change maxAddr * W < 2 ^ W at hMem
  change hintDecoderDetEnd S H D header < 2 ^ W at hDet
  have hPlacedC := HintPlacedSubtree.child hPlaced col
  have hParentSpan : node + T.nodeCount ≤ D.infos.length := hPlaced.span
  have hChildSpan : cn + C.nodeCount ≤ D.infos.length := hPlacedC.span
  have hn : node < D.infos.length := by have := hintNodeCount_pos T; omega
  have hc : cn < D.infos.length := by have := hintNodeCount_pos C; omega
  let i : Fin D.infos.length := ⟨node, hn⟩
  let j : Fin D.infos.length := ⟨cn, hc⟩
  have hNodeChild : node < cn := by unfold cn hintChildPhysicalIndex; omega
  have hSep : A.limit ≤ B.payload := hintDecoderTables_arena_separate S H hR W Bc header i j hNodeChild
  have hAM := hintDecoderTables_placedMemory S H hR hT W Bc header node seed hPlaced hRoot
  have hBM := hintDecoderTables_placedMemory S H hR (hchildren col) W Bc header cn cs hPlacedC
    (by intro he; omega)
  have hHeap : D.listBase ≤ D.heap := hAM.heap
  have hAa : A.payload = arena node := hAM.payload
  have hBa : B.payload = arena cn := hBM.payload
  have hAaLo : D.heap ≤ A.payload := hAa ▸ Nat.le_add_right _ _
  have hALo : D.listBase ≤ A.transcript := hHeap.trans (hAaLo.trans hAM.transcript)
  have hLast : last ≤ maxAddr := hintArenaStart_mono D.heap D.stride hChildSpan
  have hBLast : B.limit ≤ last := hBM.own.trans hBM.finish
  have hARes : A.result ≤ A.limit := (Nat.le_add_right _ N).trans hAM.limit.le
  have hBRes : B.result ≤ B.limit := (Nat.le_add_right _ C.N).trans hBM.limit.le
  have hATran : A.transcript ≤ A.limit :=
    hAM.hints.trans ((Nat.le_add_right _ N).trans (hAM.result.le.trans hARes))
  have hBTran : B.transcript ≤ B.limit :=
    hBM.hints.trans ((Nat.le_add_right _ C.N).trans (hBM.result.le.trans hBRes))
  have hWOne : 1 ≤ W := hW
  have hMemWord : maxAddr < 2 ^ W := by
    have h := Nat.mul_le_mul_left maxAddr hWOne
    rw [Nat.mul_one] at h
    exact h.trans_lt hMem
  have hBLastFit : last < 2 ^ W := hLast.trans_lt hMemWord
  have hBOut : B.result + sch.m ≤ last := by
    have h := hBM.limit
    change B.result + C.N < B.limit at h
    rw [hSize] at h
    exact h.le.trans hBLast
  have hInputWord : L.inputWord cn = B.payload := by
    have hnz : cn ≠ 0 := by omega
    simp [L, B, HintDecoderPlacement.inputWord, hnz]
  have hInfo : L.info node = hintNodeInfo CR hT node seed :=
    HintPlacedSubtree.info S H hR hT W Bc header node seed hPlaced
  have hInfoN : (L.info node).universeSize = N := by rw [hInfo]; rfl
  have hInfoXY : (L.info node).rowParams = some (X, Y) := by rw [hInfo]; rfl
  have hInfoT : (L.info node).residualCapacity = t := by rw [hInfo]; rfl
  have hChild : (L.info node).children[col.val]? = some cn := by
    rw [hInfo]
    change (List.ofFn (hintChildPhysicalIndex children node))[col.val]? = some cn
    exact getElem?_ofFn' _ col
  have hInfoAt : L.info node = D.infos[i.val] := by
    change D.infos[node]?.getD _ = _
    rw [List.getElem?_eq_getElem hn, Option.getD_some]
  have hScratch : hintPredictScratchEnd H L.rowScratch N X Y col.val ≤ D.listBase :=
    hintDecoderTables_rowScratch S H hR W Bc header N X Y col.val 0 0 (H.Nmax N X Y)
      col.isLt.le i (hInfoAt ▸ hInfoN) (hInfoAt ▸ hInfoXY)
  have hShape := hintArenaFor_rowOrder S H W (L.info node) (arena node) N X Y t hInfoN hInfoT hInfoXY
  have hTran : A.transcript + sch.ℓ * sch.m ≤ A.hints := by
    rw [Nat.mul_comm]
    exact hShape.1
  have hPar : A.hints + N ≤ B.payload := (hAM.result.le.trans hARes).trans hSep
  obtain ⟨hRoom1, hRoom2, hBWork, _, _⟩ := hintDecoderTables_localInput S H hR (hchildren col)
    W Bc header cn cs hPlacedC
  have hBHint : B.hints + sch.m ≤ B.result := by
    have h := hBM.result
    change B.hints + C.N < B.result at h
    rw [hSize] at h
    exact h.le
  have hInputFit : L.inputWord node * W + synLen CR T < 2 ^ W :=
    hintWordSpan_lt W _ _ maxAddr hW
      (hAM.packed.trans (hATran.trans (hSep.trans (hBM.transcript.trans (hBTran.trans (hBLast.trans hLast)))))) hMem
  have hInputSep : (L.inputWord node * W + synLen CR T) / W < B.payload :=
    (hAM.readable hW).trans_le (hATran.trans hSep)
  have hBlockC : BlockOf R cs (schemeNodes C) := BlockOf_child hBlock col
  have hHead : (schemeNodes R)[seed]? = some T := BlockOf_head hBlock
  obtain ⟨hPerm, hCoeff, _⟩ := hintRowPublic_of_head H R T seedData W det seed N X Y hHead rfl
  have hCoeffSpace : H.rows X Y * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ W :=
    (hintSpec_sizes_of_head R T seed W hHead hFit).2
  obtain ⟨_, _, hThreshold⟩ := hintDecoderTables_rowAux S H hR E up previous W Bc header N X Y t
    hHeader rfl i hInfoN hInfoT hInfoXY
  obtain ⟨hTableAt, hTableEnd⟩ := hintDecoderTables_updateAux S H hR (hchildren col) E up previous
    W Bc header cn cs hHeader rfl hPlacedC
  let table := L.updateTable cn
  let colBase := hintSubtreeColBase Bc C
  have hTableFit : table + colBase + upTabLen Bc C < 2 ^ W := by
    have h := hTableEnd.trans_lt hDet
    change table + (colBase + upTabLen Bc C) < 2 ^ W at h
    omega
  have hTable3 : table + 3 < 2 ^ W := by unfold colBase hintSubtreeColBase at hTableFit; omega
  have hCInput : synLen CR C < 2 ^ W := by
    have hh := hintWordSpan_lt W (L.inputWord cn) (synLen CR C) maxAddr hW
      (hBM.packed.trans (hBTran.trans (hBLast.trans hLast))) hMem
    omega
  have hSavFit : B.saveOffset + 1 < 2 ^ W := by
    have hB : B.payload + B.saveOffset + 2 = B.transcript := hBWork
    have hF : B.transcript < 2 ^ W :=
      hBTran.trans_lt (hBLast.trans_lt hBLastFit)
    omega
  obtain ⟨hLayout, hCount, hReturn, hLocal⟩ := hintChildTable_ready S H R C (hchildren col)
    seedData W det Bc D.control table cs B.saveOffset hW (by omega) hFit hDims hStatic hBlockC
    hChildSeed hBc hSavFit hCInput hTableFit hTableAt
  intro keep
  exact hintRecursiveColumn_phase S H D E header node seed first N X Y t Bc Xs Ys children r x J col
    keep rfl hW hWord rfl hInfoN hInfoXY hChild hm hSize hSteps hSeedFit hKFit hStepsFit hBXFit hBYFit
    hCoeffSpace (fun a b c => hCoeff a c b) hPerm hSlice hAM.scratch hAM.list hALo hScratch hTran hPar
    hBa hInputWord (hBWork.le.trans hBM.hints) hBHint hBOut hBLastFit hRoom1 hRoom2 hInputFit hInputSep
    hTable3 hReturn hLayout hCount hLocal
    (fun k => ⟨(hThreshold k).1, ((hThreshold k).2.trans_lt hDet).le⟩)
    (fun k => by rw [← hintEventRecord_length S H L]; exact (hintDecoderEvent_end S H D header k).trans_lt hDet)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedColumn_phase
end -- Def_LinearSetReconciliation327_Main_HintPlacedColumn20261120

section -- Def_LinearSetReconciliation327_Main_HintStoreAtPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintStoreAt_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node first word N : ℕ) (x : Finset ℕ) (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hWord : 2 < 2 ^ E.W)
    (hEvent : D.events[first]? = some (.store node (word * E.W) N)) :
    let A := D.placement.arena node
    let y := hintSketchVector (crFamily S) (.store N) () x
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
      (fun m => HintMemoryWords E.W word y m ∧ keep m)
      (fun m => HintBitmap m A.result N x ∧ keep m) := by
  let A := D.placement.arena node
  let y := hintSketchVector (crFamily S) (.store N) () x
  dsimp only
  intro hCtrl hDest hOffset hPre hDescriptor hInputFrame hKeep hCursor
  change D.control + 2 < A.result at hCtrl
  apply HintDecoderPhase.single (time := 12 * N + 12)
  · rintro m v ⟨hp, hk⟩
    refine ⟨?_, hCursor _ _ hk⟩
    intro a ha
    change a < wordsOf E.W N at ha
    rw [Function.update_of_ne (by rcases hInputFrame with h | h <;> omega : word + a ≠ D.control + 2)]
    exact hp a ha
  · rintro m v ⟨hb, hk⟩
    exact ⟨hb.update_below _ _ hCtrl, hCursor _ _ hk⟩
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
    obtain ⟨hPacked, hK⟩ := hInv
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
    refine ⟨hk, ⟨?_, hKeep _ _ hf hK⟩, hc.trans hCtx, fun a _ ha => hf a (Or.inl (ha.trans_lt hCtrl))⟩
    intro i hi
    rw [hb i hi]
    have hBit := hintBitAt_aligned state.mem E.W word y ⟨i, hi⟩ hPre.positive hPacked
    have hY : y ⟨i, hi⟩ = if i ∈ x then 1 else 0 := rfl
    rw [hBit, hY]
    by_cases hm : i ∈ x
    · simp [hm, hintTruth]
    · simp [hm, hintTruth]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintStoreAt_phase
end -- Def_LinearSetReconciliation327_Main_HintStoreAtPhase20261120

section -- Def_LinearSetReconciliation327_Main_HintCRAtPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintCRAt_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node first word N t : ℕ) (x : Finset ℕ) (keep : (ℕ → ℕ) → Prop)
    (hControl : D.placement.control = D.control)
    (hWidth : E.W = D.placement.width) (hW : 0 < E.W)
    (hx : x ⊆ Finset.range N) (hCount : x.card ≤ t) (hN : 1 ≤ N) (ht : t ≤ N)
    (hWord : 11 < 2 ^ E.W) (hEvent : D.events[first]? = some (.decodeLeaf node (word * E.W) N t)) :
    let L := D.placement
    let A := L.arena node
    let data := S.data N t
    let spill := A.crRegisters + 16
    let spillSize := 2 ^ (data.W + 1) + 1
    let spillEnd := spill + spillSize + crSourceSteps S N t + 1
    let y := hintSketchVector (crFamily S) (.cr N t) () x
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
      (fun m => HintMemoryWords E.W word y m ∧ HintFreshWords spill spillSize m ∧ keep m)
      (fun m => HintBitmap m A.result N x ∧ keep m) := by
  let L := D.placement
  let A := L.arena node
  let data := S.data N t
  let spill := A.crRegisters + 16
  let spillSize := 2 ^ (data.W + 1) + 1
  let spillEnd := spill + spillSize + crSourceSteps S N t + 1
  let y := hintSketchVector (crFamily S) (.cr N t) () x
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
  · rintro m v ⟨hp, hf, hk⟩
    refine ⟨?_, hf.update_below _ _ hCtrlSpill, hCursor _ _ hk⟩
    intro a ha
    change a < wordsOf E.W data.R at ha
    rw [Function.update_of_ne (by rcases hInputFrame with h | h <;> omega : word + a ≠ D.control + 2)]
    exact hp a ha
  · rintro m v ⟨hb, hk⟩
    exact ⟨hb.update_below _ _ hCtrl, hCursor _ _ hk⟩
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
    obtain ⟨hPacked, hFresh, hK⟩ := hInv
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
    have hSupport : (Finset.univ.filter fun i : Fin N => crInput N x i = 1).card ≤ t := by
      rw [crInput_card N x hx]
      exact hCount
    have hBits (i : Fin data.R) :
        bitAt state.mem E.W 0 (area.offset + i.val) =
          if data.H (crInput N x) i = 1 then 1 else 0 := by
      apply hintBitAt_aligned state.mem E.W word _ i hW
      intro q hq
      rw [← hintCRSketchVector_native S N t () x hx]
      exact hPacked q hq
    have hRun := hintCRNode_correct S (hintNativeProgram S) E state area N t base 75 hintNativeOtherActions act
      (crInput N x) hPre hSupport hPc hArg hBits
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
    change out.mem (area.destination + (⟨i, hi⟩ : Fin N).val) = hintTruth (i ∈ x)
    rw [hb ⟨i, hi⟩]
    change (if i ∈ x then (1 : ZMod 2) else 0).val = hintTruth (i ∈ x)
    by_cases h : i ∈ x
    · rw [if_pos h, hintTruth, if_pos h]
      decide
    · rw [if_neg h, hintTruth, if_neg h]
      decide

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintCRAt_phase
end -- Def_LinearSetReconciliation327_Main_HintCRAtPhase20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedLeaves20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem HintSubtreeReady.cursor {S : CRSourceBundle} {D : HintDecoderTables}
    {W node : ℕ} {T : Node} {r : T.Seed} {x J : Finset ℕ} {mem : ℕ → ℕ}
    (h : HintSubtreeReady S D W node T r x J mem)
    (g : HintPlacedMemory D W node T.nodeCount T.N (synLen (crFamily S) T)) (v : ℕ) :
    HintSubtreeReady S D W node T r x J (Function.update mem (D.control + 2) v) := by
  let A := D.placement.arena node
  have hHeap : D.heap ≤ A.payload := g.payload ▸ Nat.le_add_right _ _
  have hCtrl : D.control + 2 < A.hints :=
    g.scratch.trans_le (g.list.trans (g.heap.trans (hHeap.trans (g.transcript.trans g.hints))))
  have hOut : D.control + 2 < A.result := hCtrl.trans (lt_of_le_of_lt (Nat.le_add_right _ _) g.result)
  obtain ⟨hp, hj, hf⟩ := h
  refine ⟨?_, hj.update_below _ _ hCtrl, hf.update_below v hOut⟩
  intro q hq
  have hc : D.placement.inputWord node + wordsOf W (synLen (crFamily S) T) ≤ D.control + 2 ∨
      D.control + 2 < D.placement.inputWord node := g.outsideCursor
  change q < wordsOf W (synLen (crFamily S) T) at hq
  rw [Function.update_of_ne (by rcases hc with hc | hc <;> omega)]
  exact hp q hq

theorem HintPlacedMemory.result_frame {D : HintDecoderTables} {W node count N M : ℕ}
    (g : HintPlacedMemory D W node count N M) {m m' : ℕ → ℕ} {last : ℕ}
    (hLast : last ≤ (D.placement.arena node).limit)
    (hf : CRMemFrame (D.placement.arena node).result last m m') :
    HintSubtreeFrame D node count m m' := by
  let A := D.placement.arena node
  have hStart : hintArenaStart D.heap D.stride node ≤ A.result := by
    rw [← g.payload]
    exact (g.transcript.trans g.hints).trans ((Nat.le_add_right _ _).trans g.result.le)
  have hEnd : last ≤ hintArenaStart D.heap D.stride (node + count) :=
    hLast.trans (g.own.trans g.finish)
  intro a _ ha
  exact hf a (ha.imp (fun h => h.trans_le hStart) (fun h => hEnd.trans h))

noncomputable def hintPlacedStore_phase (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (E : RAMEnv)
    (W Bc header node seed first N : ℕ) (x J : Finset ℕ)
    (hWidth : E.W = W) (hW : 0 < W) (hWord : 2 < 2 ^ W) :
    let D := hintDecoderTables S H hR W Bc header
    let offsets := fun i => D.placement.inputWord i * E.W
    HintPlacedSubtree (crFamily S) H D (.store N) node seed →
    (node = 0 → N ≤ synLen (crFamily S) R) →
    hintArenaStart D.heap D.stride D.infos.length * W < 2 ^ W →
    hintDecoderDetEnd S H D header < 2 ^ W →
    HintEventSlice D first (hintTreeEvents (crFamily S) offsets (.store N) node seed (offsets node)) →
    HintSubtreePhase S H D E header node seed first (.store N) () x J := by
  subst W
  let D := hintDecoderTables S H hR E.W Bc header
  let L := D.placement
  let A := L.arena node
  let word := L.inputWord node
  let maxAddr := hintArenaStart D.heap D.stride D.infos.length
  dsimp only
  intro hp hRoot hMem hDet hSlice keep hKeep hCursor
  change maxAddr * E.W < 2 ^ E.W at hMem
  change hintDecoderDetEnd S H D header < 2 ^ E.W at hDet
  have g := hintDecoderTables_placedMemory S H hR (.store N) E.W Bc header node seed hp hRoot
  have hSpan : node + 1 ≤ D.infos.length := hp.span
  have hAFinal : A.limit ≤ maxAddr := g.own.trans (hintArenaStart_mono D.heap D.stride hSpan)
  have hAWord : A.limit < 2 ^ E.W := by
    have hh : maxAddr ≤ maxAddr * E.W := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left maxAddr (show 1 ≤ E.W from hW)
    exact (hAFinal.trans hh).trans_lt hMem
  have hRes : A.result + N < A.limit := g.limit
  have hHeap : D.heap ≤ A.payload := g.payload ▸ Nat.le_add_right _ _
  have hTran : A.transcript ≤ A.result :=
    g.hints.trans ((Nat.le_add_right _ _).trans g.result.le)
  have hCtrl : D.control + 2 < A.result :=
    g.scratch.trans_le (g.list.trans (g.heap.trans (hHeap.trans (g.transcript.trans hTran))))
  have hAddrFit : word * E.W + N < 2 ^ E.W :=
    hintWordSpan_lt E.W _ _ maxAddr hW (g.packed.trans (hTran.trans
      ((Nat.le_add_right _ _).trans (hRes.le.trans hAFinal)))) hMem
  have hEvent : D.events[first]? = some (.store node (word * E.W) N) := by
    have hh := hSlice.read 0 (by change 0 < 1; decide)
    rw [Nat.add_zero] at hh
    exact hh
  have hDesc (pos : Fin D.events.length) :
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ E.W := by
    apply lt_of_le_of_lt (Nat.add_le_add_left ?_ _) ((hintDecoderEvent_end S H D header pos).trans_lt hDet)
    rw [hintEventRecord_length]
    cases D.events[pos.val] <;> simp [HintTreeEvent.recordLength]
  let p := hintStoreAt_phase S H D E header node first word N x keep rfl hWord hEvent
    hCtrl (by omega : A.result < 2 ^ E.W) (by omega : word * E.W < 2 ^ E.W)
    ⟨hW, by omega, by omega, (show A.result + N ≤ 2 ^ E.W by omega), hAddrFit.le, (g.readable hW).trans_le hTran⟩
    (fun pos _ => hDesc pos) g.outsideCursor.symm
    (fun m m' hf hk => hKeep m m' (g.result_frame hRes.le hf) hk) hCursor
  change HintDecoderPhase S H D E header first 1
    (fun m => HintSubtreeReady S D E.W node (.store N) () x J m ∧ keep m)
    (fun m => HintBitmap m A.result N x ∧ keep m)
  refine p.adapt Nat.zero_lt_one (fun _ h => ⟨h.1.1, h.2⟩) (fun _ h => h) ?_ ?_
  · rintro m v ⟨h, hk⟩
    exact ⟨h.cursor g v, hCursor m v hk⟩
  · rintro m v ⟨h, hk⟩
    exact ⟨h.update_below _ _ hCtrl, hCursor m v hk⟩

noncomputable def hintPlacedCR_phase (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (E : RAMEnv) (up previous : ℕ → ℕ)
    (W Bc header node seed first N t : ℕ) (x J : Finset ℕ)
    (hHeader : 3 < header) (hWidth : E.W = W) (hW : 0 < W) (hWord : 11 < 2 ^ W)
    (hSmall : (S.data N t).W + 1 < W)
    (hN : 1 ≤ N) (ht : t ≤ N) (hx : x ⊆ Finset.range N) (hCount : x.card ≤ t) :
    let D := hintDecoderTables S H hR W Bc header
    let offsets := fun i => D.placement.inputWord i * E.W
    E.det = D.det S H up previous header R.N →
    HintPlacedSubtree (crFamily S) H D (.cr N t) node seed →
    (node = 0 → (S.data N t).R ≤ synLen (crFamily S) R) →
    hintArenaStart D.heap D.stride D.infos.length * W < 2 ^ W →
    hintDecoderDetEnd S H D header < 2 ^ W →
    HintEventSlice D first (hintTreeEvents (crFamily S) offsets (.cr N t) node seed (offsets node)) →
    HintSubtreePhase S H D E header node seed first (.cr N t) () x J := by
  subst W
  let D := hintDecoderTables S H hR E.W Bc header
  let L := D.placement
  let A := L.arena node
  let word := L.inputWord node
  let arena := hintArenaStart D.heap D.stride
  let maxAddr := arena D.infos.length
  let data := S.data N t
  let spill := A.crRegisters + 16
  let spillSize := 2 ^ (data.W + 1) + 1
  dsimp only
  intro hDet hp hRoot hMem hDetEnd hSlice keep hKeep hCursor
  change maxAddr * E.W < 2 ^ E.W at hMem
  change hintDecoderDetEnd S H D header < 2 ^ E.W at hDetEnd
  have g := hintDecoderTables_placedMemory S H hR (.cr N t) E.W Bc header node seed hp hRoot
  have hSpan : node + 1 ≤ D.infos.length := hp.span
  have hAFinal : A.limit ≤ maxAddr := g.own.trans (hintArenaStart_mono D.heap D.stride hSpan)
  have hAWord : A.limit < 2 ^ E.W := by
    have hh : maxAddr ≤ maxAddr * E.W := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left maxAddr (show 1 ≤ E.W from hW)
    exact (hAFinal.trans hh).trans_lt hMem
  have hRes : A.result + N < A.limit := g.limit
  have hHeap : D.heap ≤ A.payload := g.payload ▸ Nat.le_add_right _ _
  have hTran : A.transcript ≤ A.result :=
    g.hints.trans ((Nat.le_add_right _ _).trans g.result.le)
  have hCtrl : D.control + 2 < A.result :=
    g.scratch.trans_le (g.list.trans (g.heap.trans (hHeap.trans (g.transcript.trans hTran))))
  have hInfo : L.info node = hintNodeInfo (crFamily S) (.cr (P := H) N t) node seed :=
    HintPlacedSubtree.info S H hR (.cr N t) E.W Bc header node seed hp
  have hArea : A = hintNodeArena (arena node) E.W data.R 0 0 0 N data.R data.W (crSourceSteps S N t) := by
    change hintArenaFor S H E.W (L.info node) (arena node) = _
    rw [hInfo]
    rfl
  have hEnd : A.limit = spill + spillSize + crSourceSteps S N t + 1 := by
    unfold spill
    rw [hArea]
    rfl
  have hReg : A.result + N < A.crRegisters := by
    rw [hArea]
    dsimp only [hintNodeArena]
    omega
  have hSpill : A.result ≤ spill := by unfold spill; omega
  have hSpillFit : spill + spillSize + crSourceSteps S N t + 1 < 2 ^ E.W := hEnd ▸ hAWord
  have hAddrFit : word * E.W + data.R < 2 ^ E.W :=
    hintWordSpan_lt E.W _ _ maxAddr hW (g.packed.trans (hTran.trans
      ((Nat.le_add_right _ _).trans (hRes.le.trans hAFinal)))) hMem
  have hEvent : D.events[first]? = some (.decodeLeaf node (word * E.W) N t) := by
    have hh := hSlice.read 0 (by change 0 < 1; decide)
    rw [Nat.add_zero] at hh
    exact hh
  have hDesc (pos : Fin D.events.length) (hh : pos.val = first) :
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 11 < 2 ^ E.W := by
    have he : D.events[pos.val]? = some (.decodeLeaf node (word * E.W) N t) := by rw [hh]; exact hEvent
    have heq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans he)
    apply lt_of_le_of_lt (Nat.add_le_add_left ?_ _) ((hintDecoderEvent_end S H D header pos).trans_lt hDetEnd)
    rw [hintEventRecord_length, heq]
    simp [HintTreeEvent.recordLength]
  let cr := hintCRTableBlock data.W data.det
  have hAux : D.nodeAux S H Bc node =
      [hintSubtreeBlock (crFamily S) E.W D.control Bc (.cr N t) seed A.saveOffset, hintEmptyDetBlock, cr] := by
    change hintNodeAuxBlocks S H E.W D.control Bc (L.info node) A = _
    rw [hInfo]
    rfl
  let i : Fin D.infos.length := ⟨node, by omega⟩
  let j : Fin (D.nodeAux S H Bc i.val).length := ⟨2, by change 2 < (D.nodeAux S H Bc node).length; rw [hAux]; exact Nat.lt_succ_self 2⟩
  have hAt := hintDecoderTables_aux_At S H hR E up previous E.W Bc header hHeader hDet i j
  have hLen := hintDecoderTables_aux_end S H hR E.W Bc header i j
  have hc : (D.nodeAux S H Bc i.val)[j.val] = cr := by
    have ho : (D.nodeAux S H Bc i.val)[j.val]? = some cr :=
      congrArg (fun a : List HintDetBlock => a[2]?) hAux
    exact Option.some.inj ((List.getElem?_eq_getElem (l := D.nodeAux S H Bc i.val) j.isLt).symm.trans ho)
  have hAddr : L.crTable node = D.auxAddress S H Bc header i.val j.val :=
    (hintDecoderTables_aux_addresses S H hR E.W Bc header node 0).2.2.1
  rw [hc, ← hAddr] at hAt hLen
  have hCrFit : L.crTable node + 2 ^ data.W < 2 ^ E.W := by
    have hh := hLen.trans_lt hDetEnd
    change L.crTable node + (2 ^ data.W + 1) < 2 ^ E.W at hh
    omega
  let p := hintCRAt_phase S H D E header node first word N t x keep rfl rfl hW hx hCount hN ht hWord hEvent
    hCtrl hReg hSpillFit hSmall hCrFit hAddrFit
    ((g.readable hW).trans_le (hTran.trans hSpill)) hAt hDesc g.outsideCursor.symm
    (fun m m' hf hk => hKeep m m' (g.result_frame (show spill + spillSize + crSourceSteps S N t + 1 ≤ A.limit by rw [hEnd]) hf) hk)
    hCursor
  change HintDecoderPhase S H D E header first 1
    (fun m => HintSubtreeReady S D E.W node (.cr N t) () x J m ∧ keep m)
    (fun m => HintBitmap m A.result N x ∧ keep m)
  refine p.adapt Nat.zero_lt_one ?_ (fun _ h => h) ?_ ?_
  · rintro m ⟨⟨hp, _, hf⟩, hk⟩
    have hSpillBound : spill + spillSize ≤ arena (node + 1) := by
      apply le_trans ?_ g.own
      rw [hEnd]
      exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
    exact ⟨hp, hf.words hSpill hSpillBound, hk⟩
  · rintro m v ⟨h, hk⟩
    exact ⟨h.cursor g v, hCursor m v hk⟩
  · rintro m v ⟨h, hk⟩
    exact ⟨h.update_below _ _ hCtrl, hCursor m v hk⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedStore_phase
#print axioms LinearSetReconciliation327.Main.hintPlacedCR_phase
end -- Def_LinearSetReconciliation327_Main_HintPlacedLeaves20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedBinaryLeaves20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintPlacedStore_total (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (E : RAMEnv)
    (W Bc header node seed first N : ℕ)
    (hWidth : E.W = W) (hW : 0 < W) (hWord : 2 < 2 ^ W) :
    let D := hintDecoderTables S H hR W Bc header
    let offsets := fun i => D.placement.inputWord i * E.W
    HintPlacedSubtree (crFamily S) H D (.store N) node seed →
    (node = 0 → N ≤ synLen (crFamily S) R) →
    hintArenaStart D.heap D.stride D.infos.length * W < 2 ^ W →
    hintDecoderDetEnd S H D header < 2 ^ W →
    HintEventSlice D first (hintTreeEvents (crFamily S) offsets (.store N) node seed (offsets node)) →
    ∀ keep : (ℕ → ℕ) → Prop,
      (∀ m m', HintSubtreeFrame D node 1 m m' → keep m → keep m') →
      (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
      HintDecoderPhase S H D E header first 1 keep
        (fun m => HintBinaryMemory m (D.placement.arena node).result N ∧ keep m) := by
  subst W
  let D := hintDecoderTables S H hR E.W Bc header
  let L := D.placement
  let A := L.arena node
  let word := L.inputWord node
  let maxAddr := hintArenaStart D.heap D.stride D.infos.length
  dsimp only
  intro hp hRoot hMem hDet hSlice keep hKeep hCursor
  change maxAddr * E.W < 2 ^ E.W at hMem
  change hintDecoderDetEnd S H D header < 2 ^ E.W at hDet
  have g := hintDecoderTables_placedMemory S H hR (.store N) E.W Bc header node seed hp hRoot
  have hSpan : node + 1 ≤ D.infos.length := hp.span
  have hAFinal : A.limit ≤ maxAddr := g.own.trans (hintArenaStart_mono D.heap D.stride hSpan)
  have hAWord : A.limit < 2 ^ E.W := by
    have hh : maxAddr ≤ maxAddr * E.W := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left maxAddr (show 1 ≤ E.W from hW)
    exact (hAFinal.trans hh).trans_lt hMem
  have hRes : A.result + N < A.limit := g.limit
  have hHeap : D.heap ≤ A.payload := g.payload ▸ Nat.le_add_right _ _
  have hTran : A.transcript ≤ A.result :=
    g.hints.trans ((Nat.le_add_right _ _).trans g.result.le)
  have hCtrl : D.control + 2 < A.result :=
    g.scratch.trans_le (g.list.trans (g.heap.trans (hHeap.trans (g.transcript.trans hTran))))
  have hAddrFit : word * E.W + N < 2 ^ E.W :=
    hintWordSpan_lt E.W _ _ maxAddr hW (g.packed.trans (hTran.trans
      ((Nat.le_add_right _ _).trans (hRes.le.trans hAFinal)))) hMem
  have hEvent : D.events[first]? = some (.store node (word * E.W) N) := by
    have hh := hSlice.read 0 (by change 0 < 1; decide)
    rw [Nat.add_zero] at hh
    exact hh
  have hDesc (pos : Fin D.events.length) :
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ E.W := by
    apply lt_of_le_of_lt (Nat.add_le_add_left ?_ _) ((hintDecoderEvent_end S H D header pos).trans_lt hDet)
    rw [hintEventRecord_length]
    cases D.events[pos.val] <;> simp [HintTreeEvent.recordLength]
  exact hintStoreAt_total S H D E header node first word N keep rfl hWord hEvent
    hCtrl (by omega : A.result < 2 ^ E.W) (by omega : word * E.W < 2 ^ E.W)
    ⟨hW, by omega, by omega, (show A.result + N ≤ 2 ^ E.W by omega), hAddrFit.le, (g.readable hW).trans_le hTran⟩
    (fun pos _ => hDesc pos) g.outsideCursor.symm
    (fun m m' hf hk => hKeep m m' (g.result_frame hRes.le hf) hk) hCursor

noncomputable def hintPlacedCR_total (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (E : RAMEnv) (up previous : ℕ → ℕ)
    (W Bc header node seed first N t : ℕ)
    (hHeader : 3 < header) (hWidth : E.W = W) (hW : 0 < W) (hWord : 11 < 2 ^ W)
    (hSmall : (S.data N t).W + 1 < W)
    (hN : 1 ≤ N) (ht : t ≤ N) :
    let D := hintDecoderTables S H hR W Bc header
    let offsets := fun i => D.placement.inputWord i * E.W
    E.det = D.det S H up previous header R.N →
    HintPlacedSubtree (crFamily S) H D (.cr N t) node seed →
    (node = 0 → (S.data N t).R ≤ synLen (crFamily S) R) →
    hintArenaStart D.heap D.stride D.infos.length * W < 2 ^ W →
    hintDecoderDetEnd S H D header < 2 ^ W →
    HintEventSlice D first (hintTreeEvents (crFamily S) offsets (.cr N t) node seed (offsets node)) →
    ∀ keep : (ℕ → ℕ) → Prop,
      (∀ m m', HintSubtreeFrame D node 1 m m' → keep m → keep m') →
      (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
      HintDecoderPhase S H D E header first 1
        (fun m => HintNodeFreshTail D node 1 m ∧ keep m)
        (fun m => HintBinaryMemory m (D.placement.arena node).result N ∧ keep m) := by
  subst W
  let D := hintDecoderTables S H hR E.W Bc header
  let L := D.placement
  let A := L.arena node
  let word := L.inputWord node
  let arena := hintArenaStart D.heap D.stride
  let maxAddr := arena D.infos.length
  let data := S.data N t
  let spill := A.crRegisters + 16
  let spillSize := 2 ^ (data.W + 1) + 1
  dsimp only
  intro hDet hp hRoot hMem hDetEnd hSlice keep hKeep hCursor
  change maxAddr * E.W < 2 ^ E.W at hMem
  change hintDecoderDetEnd S H D header < 2 ^ E.W at hDetEnd
  have g := hintDecoderTables_placedMemory S H hR (.cr N t) E.W Bc header node seed hp hRoot
  have hSpan : node + 1 ≤ D.infos.length := hp.span
  have hAFinal : A.limit ≤ maxAddr := g.own.trans (hintArenaStart_mono D.heap D.stride hSpan)
  have hAWord : A.limit < 2 ^ E.W := by
    have hh : maxAddr ≤ maxAddr * E.W := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left maxAddr (show 1 ≤ E.W from hW)
    exact (hAFinal.trans hh).trans_lt hMem
  have hRes : A.result + N < A.limit := g.limit
  have hHeap : D.heap ≤ A.payload := g.payload ▸ Nat.le_add_right _ _
  have hTran : A.transcript ≤ A.result :=
    g.hints.trans ((Nat.le_add_right _ _).trans g.result.le)
  have hCtrl : D.control + 2 < A.result :=
    g.scratch.trans_le (g.list.trans (g.heap.trans (hHeap.trans (g.transcript.trans hTran))))
  have hInfo : L.info node = hintNodeInfo (crFamily S) (.cr (P := H) N t) node seed :=
    HintPlacedSubtree.info S H hR (.cr N t) E.W Bc header node seed hp
  have hArea : A = hintNodeArena (arena node) E.W data.R 0 0 0 N data.R data.W (crSourceSteps S N t) := by
    change hintArenaFor S H E.W (L.info node) (arena node) = _
    rw [hInfo]
    rfl
  have hEnd : A.limit = spill + spillSize + crSourceSteps S N t + 1 := by
    unfold spill
    rw [hArea]
    rfl
  have hReg : A.result + N < A.crRegisters := by
    rw [hArea]
    dsimp only [hintNodeArena]
    omega
  have hSpill : A.result ≤ spill := by unfold spill; omega
  have hSpillFit : spill + spillSize + crSourceSteps S N t + 1 < 2 ^ E.W := hEnd ▸ hAWord
  have hAddrFit : word * E.W + data.R < 2 ^ E.W :=
    hintWordSpan_lt E.W _ _ maxAddr hW (g.packed.trans (hTran.trans
      ((Nat.le_add_right _ _).trans (hRes.le.trans hAFinal)))) hMem
  have hEvent : D.events[first]? = some (.decodeLeaf node (word * E.W) N t) := by
    have hh := hSlice.read 0 (by change 0 < 1; decide)
    rw [Nat.add_zero] at hh
    exact hh
  have hDesc (pos : Fin D.events.length) (hh : pos.val = first) :
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 11 < 2 ^ E.W := by
    have he : D.events[pos.val]? = some (.decodeLeaf node (word * E.W) N t) := by rw [hh]; exact hEvent
    have heq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans he)
    apply lt_of_le_of_lt (Nat.add_le_add_left ?_ _) ((hintDecoderEvent_end S H D header pos).trans_lt hDetEnd)
    rw [hintEventRecord_length, heq]
    simp [HintTreeEvent.recordLength]
  let cr := hintCRTableBlock data.W data.det
  have hAux : D.nodeAux S H Bc node =
      [hintSubtreeBlock (crFamily S) E.W D.control Bc (.cr N t) seed A.saveOffset, hintEmptyDetBlock, cr] := by
    change hintNodeAuxBlocks S H E.W D.control Bc (L.info node) A = _
    rw [hInfo]
    rfl
  let i : Fin D.infos.length := ⟨node, by omega⟩
  let j : Fin (D.nodeAux S H Bc i.val).length := ⟨2, by change 2 < (D.nodeAux S H Bc node).length; rw [hAux]; exact Nat.lt_succ_self 2⟩
  have hAt := hintDecoderTables_aux_At S H hR E up previous E.W Bc header hHeader hDet i j
  have hLen := hintDecoderTables_aux_end S H hR E.W Bc header i j
  have hc : (D.nodeAux S H Bc i.val)[j.val] = cr := by
    have ho : (D.nodeAux S H Bc i.val)[j.val]? = some cr :=
      congrArg (fun a : List HintDetBlock => a[2]?) hAux
    exact Option.some.inj ((List.getElem?_eq_getElem (l := D.nodeAux S H Bc i.val) j.isLt).symm.trans ho)
  have hAddr : L.crTable node = D.auxAddress S H Bc header i.val j.val :=
    (hintDecoderTables_aux_addresses S H hR E.W Bc header node 0).2.2.1
  rw [hc, ← hAddr] at hAt hLen
  have hCrFit : L.crTable node + 2 ^ data.W < 2 ^ E.W := by
    have hh := hLen.trans_lt hDetEnd
    change L.crTable node + (2 ^ data.W + 1) < 2 ^ E.W at hh
    omega
  let p := hintCRAt_total S H D E header node first word N t keep rfl rfl hW hN ht hWord hEvent
    hCtrl hReg hSpillFit hSmall hCrFit hAddrFit
    ((g.readable hW).trans_le (hTran.trans hSpill)) hAt hDesc g.outsideCursor.symm
    (fun m m' hf hk => hKeep m m' (g.result_frame (show spill + spillSize + crSourceSteps S N t + 1 ≤ A.limit by rw [hEnd]) hf) hk)
    hCursor
  change HintDecoderPhase S H D E header first 1
    (fun m => HintNodeFreshTail D node 1 m ∧ keep m)
    (fun m => HintBinaryMemory m A.result N ∧ keep m)
  refine p.adapt Nat.zero_lt_one ?_ (fun _ h => h) ?_ ?_
  · rintro m ⟨hf, hk⟩
    have hSpillBound : spill + spillSize ≤ arena (node + 1) := by
      apply le_trans ?_ g.own
      rw [hEnd]
      exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
    exact ⟨hf.words hSpill hSpillBound, hk⟩
  · rintro m v ⟨h, hk⟩
    exact ⟨h.update_below v hCtrl, hCursor m v hk⟩
  · rintro m v ⟨h, hk⟩
    exact ⟨(fun q hq => by
      rw [Function.update_of_ne (by omega : A.result + q ≠ D.control + 2)]
      exact h q hq), hCursor m v hk⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedStore_total
#print axioms LinearSetReconciliation327.Main.hintPlacedCR_total
end -- Def_LinearSetReconciliation327_Main_HintPlacedBinaryLeaves20261120

section -- Def_LinearSetReconciliation327_Main_HintBinarySubtree20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintBinarySubtreeReady (D : HintDecoderTables) (node count N : ℕ) (m : ℕ → ℕ) : Prop :=
  HintBinaryMemory m (D.placement.arena node).hints N ∧ HintNodeFreshTail D node count m

def HintBinarySubtreePhase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node seed first : ℕ) (T : Node) :=
  ∀ keep : (ℕ → ℕ) → Prop,
    (∀ m m', HintSubtreeFrame D node T.nodeCount m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first
      (hintTreeEvents (crFamily S) (fun a => D.placement.inputWord a * E.W)
        T node seed (D.placement.inputWord node * E.W)).length
      (fun m => HintBinarySubtreeReady D node T.nodeCount T.N m ∧ keep m)
      (fun m => HintBinaryMemory m (D.placement.arena node).result T.N ∧ keep m)

noncomputable def HintDecoderPhase.binaryHintParam {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header first count base N : ℕ}
    {A B : (ℕ → ℕ) → Prop}
    (p : ∀ J : Finset ℕ, HintDecoderPhase S H D E header first count
      (fun m => HintBitmap m base N J ∧ A m) B)
    (hCount : 0 < count) (hBase : D.control + 2 < base)
    (hA : ∀ m v, A m → A (Function.update m (D.control + 2) v))
    (hB : ∀ m v, B m → B (Function.update m (D.control + 2) v)) :
    HintDecoderPhase S H D E header first count (fun m => HintBinaryMemory m base N ∧ A m) B := by
  classical
  let q := HintDecoderPhase.existsParam (fun J : Finset (Fin N) => p (J.map Fin.valEmbedding))
  refine q.adapt hCount ?_ (fun _ h => h.elim fun _ hb => hb) ?_ hB
  · rintro m ⟨hBits, hStart⟩
    obtain ⟨J, hSub, hJ⟩ := hBits.to_bitmap
    let J' : Finset (Fin N) := Finset.univ.filter fun j => j.val ∈ J
    have hMap : J'.map Fin.valEmbedding = J := by
      ext j
      constructor
      · intro h
        obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp h
        exact (Finset.mem_filter.mp hi).2
      · intro h
        have hj : j < N := Finset.mem_range.mp (hSub h)
        exact Finset.mem_map.mpr ⟨⟨j, hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
    exact ⟨J', hMap ▸ hJ, hStart⟩
  · rintro m v ⟨hb, ha⟩
    exact ⟨hb.update_below v hBase, hA m v ha⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintDecoderPhase.binaryHintParam
end -- Def_LinearSetReconciliation327_Main_HintBinarySubtree20261120

section -- Def_LinearSetReconciliation327_Main_HintEventCount20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintScheduleShape (U L : ℕ) : Node → Prop
  | .store _ | .cr _ _ => True
  | .direct sch _ => sch.N ≤ U ∧ sch.m ≤ U ∧ sch.ℓ ≤ L
  | .recursive sch _ _ _ children =>
      sch.N ≤ U ∧ sch.m ≤ U ∧ sch.ℓ ≤ L ∧ ∀ s, HintScheduleShape U L (children s)

theorem hintRecursiveColumnEvents_length (CR : CRFamily) (payloadOffset : ℕ → ℕ)
    (sch : RowScheme) (children : Fin sch.ℓ → Node) (node seed offset : ℕ) (s : Fin sch.ℓ) :
    (hintRecursiveColumnEvents CR payloadOffset sch children node seed offset s).length =
      2 * sch.m + 2 +
        (hintTreeEvents CR payloadOffset (children s) (hintChildPhysicalIndex children node s)
          (hintChildSchemeIndex children seed s) (payloadOffset (hintChildPhysicalIndex children node s))).length := by
  simp only [hintRecursiveColumnEvents, List.length_append, List.length_map, List.length_range,
    List.length_cons, List.length_nil]
  omega

theorem hintTreeEvents_count (CR : CRFamily) (payloadOffset : ℕ → ℕ)
    (U L : ℕ) (T : Node) (hShape : HintScheduleShape U L T) :
    ∀ node seed offset, (hintTreeEvents CR payloadOffset T node seed offset).length ≤
      ((2 * U + 2) * L + 2 * U + 3) * T.nodeCount := by
  let C := (2 * U + 2) * L + 2 * U + 3
  have hC : 1 ≤ C := by dsimp only [C]; omega
  induction T with
  | store N =>
      intro node seed offset
      simpa [hintTreeEvents, Node.nodeCount, C] using hC
  | cr N t =>
      intro node seed offset
      simpa [hintTreeEvents, Node.nodeCount, C] using hC
  | direct sch t =>
      intro node seed offset
      obtain ⟨hN, hm, hL⟩ := hShape
      rw [hintTreeEvents_direct]
      simp only [List.length_append, hintDirectReads_length, List.length_map, List.length_range,
        hintResidualEvents_length, Node.nodeCount, Nat.mul_one]
      have hBig : sch.m * sch.ℓ ≤ (2 * U + 2) * L := Nat.mul_le_mul (by omega) hL
      omega
  | recursive sch t Xs Ys children ih =>
      intro node seed offset
      obtain ⟨hN, hm, hL, hChildren⟩ := hShape
      let q := fun s => (hintTreeEvents CR payloadOffset (children s) (hintChildPhysicalIndex children node s)
        (hintChildSchemeIndex children seed s) (payloadOffset (hintChildPhysicalIndex children node s))).length
      have hKids : (∑ s, q s) ≤ C * ∑ s, (children s).nodeCount := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun s _ => ih s (hChildren s) _ _ _
      have hu : sch.ℓ * (2 * sch.m + 2) ≤ (2 * U + 2) * L := by
        rw [Nat.mul_comm sch.ℓ]
        exact Nat.mul_le_mul (by omega) hL
      have hLocal : (List.ofFn (hintRecursiveColumnEvents CR payloadOffset sch children node seed offset)).flatten.length =
          sch.ℓ * (2 * sch.m + 2) + ∑ s, q s := by
        rw [length_flatten_ofFn]
        calc
          _ = ∑ s, (2 * sch.m + 2 + q s) := Finset.sum_congr rfl fun s _ =>
            hintRecursiveColumnEvents_length CR payloadOffset sch children node seed offset s
          _ = _ := by
            rw [Finset.sum_add_distrib]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      rw [hintTreeEvents_recursive, List.length_append, List.length_append, hLocal, List.length_map,
        List.length_range, hintResidualEvents_length]
      change _ ≤ C * (1 + ∑ s, (children s).nodeCount)
      rw [Nat.mul_add C 1 (∑ s, (children s).nodeCount), Nat.mul_one]
      dsimp only [C] at *
      omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintTreeEvents_count
end -- Def_LinearSetReconciliation327_Main_HintEventCount20261120

section -- Def_LinearSetReconciliation327_Main_HintPhaseBudgetSum20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintSumRange_countdown (f : ℕ → ℕ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f (n - (i + 1))) = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv_lhs => rw [Finset.sum_range_succ']
    conv_rhs => rw [Finset.sum_range_succ]
    have hstep (i : ℕ) : n + 1 - (i + 1 + 1) = n - (i + 1) := by omega
    simpa only [Nat.succ_eq_add_one, hstep, Nat.add_sub_cancel] using
      congrArg (fun k : ℕ => k + f n) ih

theorem hintPhaseRunBudget_sum (S : CRSourceBundle) (count N : ℕ) (budget : ℕ → ℕ) :
    hintPhaseRunBudget S count N budget =
      (∑ i ∈ Finset.range count, budget i) + 44 * count + 29 * N + 67 := by
  have hc : (hintNativeActions S).length = 7 := rfl
  unfold hintPhaseRunBudget hintDispatchBudget
  simp only [hc]
  change (∑ i ∈ Finset.range count, (budget (count - (i + 1)) + 44)) + 29 * N + 67 = _
  rw [hintSumRange_countdown (fun i => budget i + 44), Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  change (∑ i ∈ Finset.range count, budget i) + count * 44 + 29 * N + 67 = _
  rw [Nat.mul_comm count 44]

theorem HintDecoderPhase.append_budget_sum {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header first n m : ℕ} {A B C : (ℕ → ℕ) → Prop}
    (p : HintDecoderPhase S H D E header first n A B)
    (q : HintDecoderPhase S H D E header (first + n) m B C) :
    (∑ i ∈ Finset.range (n + m), (p.append q).budget i) =
      (∑ i ∈ Finset.range n, p.budget i) + (∑ i ∈ Finset.range m, q.budget i) := by
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have h := Finset.mem_range.mp hi
    change (if i < n then p.budget i else q.budget (i - n)) = p.budget i
    rw [if_pos h]
  · apply Finset.sum_congr rfl
    intro i _
    change (if n + i < n then p.budget (n + i) else q.budget (n + i - n)) = q.budget i
    rw [if_neg (by omega), Nat.add_sub_cancel_left]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPhaseRunBudget_sum
#print axioms LinearSetReconciliation327.Main.HintDecoderPhase.append_budget_sum
end -- Def_LinearSetReconciliation327_Main_HintPhaseBudgetSum20261120

section -- Def_LinearSetReconciliation327_Main_HintEventWorkCount20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintTreeEvent.linearWork : HintTreeEvent → Bool
  | .store .. | .childCopy .. | .residualCopy .. | .recoverColumn .. | .correctEstimate ..
    | .decodeLeaf .. | .decodeResidual .. => true
  | .directBit .. | .predict .. | .finishRow .. | .childToggle .. | .residualToggle .. => false

private theorem hintFilterFlatten (blocks : List (List HintTreeEvent)) :
    blocks.flatten.filter HintTreeEvent.linearWork =
      (blocks.map fun b => b.filter HintTreeEvent.linearWork).flatten := by
  induction blocks with
  | nil => rfl
  | cons b bs ih => simp only [List.flatten_cons, List.filter_append, List.map_cons, ih]

private theorem hintLinearResidual_count (CR : CRFamily) (node offset N t : ℕ) :
    ((hintResidualEvents CR node offset N t).filter HintTreeEvent.linearWork).length = 3 := by
  simp [hintResidualEvents, List.filter_cons, List.filter_append, List.filter_map, Function.comp_def, HintTreeEvent.linearWork]

private theorem hintLinearColumn_count (CR : CRFamily) (offsets : ℕ → ℕ)
    (sch : RowScheme) (children : Fin sch.ℓ → Node) (node seed offset : ℕ) (s : Fin sch.ℓ) :
    ((hintRecursiveColumnEvents CR offsets sch children node seed offset s).filter HintTreeEvent.linearWork).length =
      ((hintTreeEvents CR offsets (children s) (hintChildPhysicalIndex children node s)
        (hintChildSchemeIndex children seed s) (offsets (hintChildPhysicalIndex children node s))).filter
        HintTreeEvent.linearWork).length + 2 := by
  simp [hintRecursiveColumnEvents, List.filter_cons, List.filter_append, List.filter_map, Function.comp_def, HintTreeEvent.linearWork]

theorem hintTreeEvents_linearWork_count (CR : CRFamily) (offsets : ℕ → ℕ) (T : Node) :
    ∀ node seed offset,
      ((hintTreeEvents CR offsets T node seed offset).filter HintTreeEvent.linearWork).length + 2 ≤
        5 * T.nodeCount := by
  induction T with
  | store N => intro node seed offset; simp [hintTreeEvents, List.filter_cons, HintTreeEvent.linearWork, Node.nodeCount]
  | cr N t => intro node seed offset; simp [hintTreeEvents, List.filter_cons, HintTreeEvent.linearWork, Node.nodeCount]
  | direct sch t =>
    intro node seed offset
    rw [hintTreeEvents_direct]
    have hRead : (hintDirectReads sch node offset).filter HintTreeEvent.linearWork = [] := by
      unfold hintDirectReads
      rw [hintFilterFlatten, List.map_ofFn]
      simp [List.filter_map, Function.comp_def, HintTreeEvent.linearWork]
    simp [List.filter_append, hRead, List.filter_map, Function.comp_def, HintTreeEvent.linearWork,
      hintLinearResidual_count, Node.nodeCount]
  | recursive sch t Xs Ys children ih =>
    intro node seed offset
    let cols := hintRecursiveColumnEvents CR offsets sch children node seed offset
    let q := fun s : Fin sch.ℓ =>
      ((hintTreeEvents CR offsets (children s) (hintChildPhysicalIndex children node s)
        (hintChildSchemeIndex children seed s) (offsets (hintChildPhysicalIndex children node s))).filter
        HintTreeEvent.linearWork).length
    have hCols : (((List.ofFn cols).flatten).filter HintTreeEvent.linearWork).length = ∑ s, (q s + 2) := by
      rw [hintFilterFlatten, List.map_ofFn, length_flatten_ofFn]
      exact Finset.sum_congr rfl fun s _ => hintLinearColumn_count CR offsets sch children node seed offset s
    have hBound : (∑ s, (q s + 2)) ≤ 5 * ∑ s, (children s).nodeCount := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun s _ => ih s _ _ _
    rw [hintTreeEvents_recursive]
    change (((List.ofFn cols).flatten ++ (List.range sch.m).map (HintTreeEvent.finishRow node seed) ++
      hintResidualEvents CR node (offset + ∑ s, synLen CR (children s)) sch.N t).filter
      HintTreeEvent.linearWork).length + 2 ≤ _
    have hRows : ((List.range sch.m).map (HintTreeEvent.finishRow node seed)).filter HintTreeEvent.linearWork = [] := by
      simp [List.filter_map, Function.comp_def, HintTreeEvent.linearWork]
    simp only [List.filter_append, List.length_append, hCols, hRows, List.length_nil,
      Nat.add_zero, hintLinearResidual_count, Node.nodeCount, Nat.mul_add, Nat.mul_one]
    omega

private theorem hintLinearWork_sum (events : List HintTreeEvent) (base extra : ℕ) :
    (events.map (fun e => base + (if e.linearWork then extra else 0))).sum =
      base * events.length + extra * (events.filter HintTreeEvent.linearWork).length := by
  induction events with
  | nil => simp
  | cons e es ih =>
    cases h : e.linearWork <;>
      simp [List.filter_cons, h, ih, Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem hintPhaseRunBudget_split (S : CRSourceBundle) (events : List HintTreeEvent) (N : ℕ)
    (budget : ℕ → ℕ) (base extra : ℕ)
    (hCost : ∀ i : Fin events.length, budget i.val ≤ base + (if (events[i.val]'i.isLt).linearWork then extra else 0)) :
    hintPhaseRunBudget S events.length N budget ≤
      (base + 44) * events.length + extra * (events.filter HintTreeEvent.linearWork).length + 29 * N + 67 := by
  rw [hintPhaseRunBudget_sum]
  have hSum : (∑ i ∈ Finset.range events.length, budget i) ≤
      base * events.length + extra * (events.filter HintTreeEvent.linearWork).length := by
    rw [← Fin.sum_univ_eq_sum_range]
    calc
      _ ≤ ∑ i : Fin events.length, (base + (if (events[i.val]'i.isLt).linearWork then extra else 0)) :=
        Finset.sum_le_sum fun i _ => hCost i
      _ = _ := by
        rw [← List.sum_ofFn]
        let cost := fun e : HintTreeEvent => base + (if e.linearWork then extra else 0)
        change (List.ofFn fun i : Fin events.length => cost events[i.val]).sum = _
        have hm := List.ofFn_getElem_eq_map events cost
        exact (congrArg List.sum hm).trans (hintLinearWork_sum events base extra)
  rw [Nat.add_mul]
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintTreeEvents_linearWork_count
#print axioms LinearSetReconciliation327.Main.hintPhaseRunBudget_split
end -- Def_LinearSetReconciliation327_Main_HintEventWorkCount20261120

section -- Def_LinearSetReconciliation327_Main_HintBudgetFollows20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintBudgetFollows (events : List HintTreeEvent) (first count : ℕ)
    (budget : ℕ → ℕ) (cap : HintTreeEvent → ℕ) : Prop :=
  ∀ (i : ℕ), i < count → ∀ e, events[first + i]? = some e → budget i ≤ cap e

theorem HintBudgetFollows.append {events : List HintTreeEvent} {first n m : ℕ}
    {p q : ℕ → ℕ} {cap : HintTreeEvent → ℕ}
    (hp : HintBudgetFollows events first n p cap)
    (hq : HintBudgetFollows events (first + n) m q cap) :
    HintBudgetFollows events first (n + m) (fun i => if i < n then p i else q (i - n)) cap := by
  intro i hi e he
  by_cases h : i < n
  · simpa only [if_pos h] using hp i h e he
  · have hJ : i - n < m := by omega
    have hAt : (first + n) + (i - n) = first + i := by omega
    have he' : events[(first + n) + (i - n)]? = some e := by rw [hAt]; exact he
    simpa only [if_neg h] using hq (i - n) hJ e he'

theorem HintDecoderPhase.append_budget_follows {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header first second n m : ℕ} {A B C : (ℕ → ℕ) → Prop}
    {p : HintDecoderPhase S H D E header first n A B}
    {q : HintDecoderPhase S H D E header second m B C}
    (h : second = first + n) (cap : HintTreeEvent → ℕ)
    (hp : HintBudgetFollows D.events first n p.budget cap)
    (hq : HintBudgetFollows D.events second m q.budget cap) :
    HintBudgetFollows D.events first (n + m) (p.append_at q h).budget cap := by
  subst second
  exact hp.append hq

theorem HintDecoderPhase.adapt_budget_follows {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header first count : ℕ} {A B A' B' : (ℕ → ℕ) → Prop}
    {p : HintDecoderPhase S H D E header first count A B} (hCount : 0 < count)
    (before : ∀ m, A' m → A m) (after : ∀ m, B m → B' m)
    (hA : ∀ m v, A' m → A' (Function.update m (D.control + 2) v))
    (hB : ∀ m v, B' m → B' (Function.update m (D.control + 2) v))
    (cap : HintTreeEvent → ℕ) (hp : HintBudgetFollows D.events first count p.budget cap) :
    HintBudgetFollows D.events first count (p.adapt hCount before after hA hB).budget cap := hp

theorem HintDecoderPhase.existsParam_budget_follows {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header first count : ℕ}
    {α : Type} [Fintype α] [DecidableEq α]
    {A B : α → (ℕ → ℕ) → Prop}
    (p : ∀ a, HintDecoderPhase S H D E header first count (A a) (B a))
    (cap : HintTreeEvent → ℕ) (hp : ∀ a, HintBudgetFollows D.events first count (p a).budget cap) :
    HintBudgetFollows D.events first count (HintDecoderPhase.existsParam p).budget cap := by
  intro i hi e he
  exact HintDecoderPhase.existsParam_budget_le p i (cap e) fun a => hp a i hi e he

theorem HintDecoderPhase.binaryHintParam_budget_follows {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header first count base N : ℕ}
    {A B : (ℕ → ℕ) → Prop}
    (p : ∀ J : Finset ℕ, HintDecoderPhase S H D E header first count
      (fun m => HintBitmap m base N J ∧ A m) B)
    (hCount : 0 < count) (hBase : D.control + 2 < base)
    (hA : ∀ m v, A m → A (Function.update m (D.control + 2) v))
    (hB : ∀ m v, B m → B (Function.update m (D.control + 2) v))
    (cap : HintTreeEvent → ℕ) (hp : ∀ J, HintBudgetFollows D.events first count (p J).budget cap) :
    HintBudgetFollows D.events first count
      (HintDecoderPhase.binaryHintParam p hCount hBase hA hB).budget cap := by
  classical
  exact HintDecoderPhase.existsParam_budget_follows (fun J : Finset (Fin N) => p (J.map Fin.valEmbedding))
    cap (fun _ => hp _)

theorem hintPhaseRunBudget_of_follows (S : CRSourceBundle) (events : List HintTreeEvent) (N : ℕ)
    (budget : ℕ → ℕ) (base extra : ℕ)
    (hCost : HintBudgetFollows events 0 events.length budget
      (fun e => base + (if e.linearWork then extra else 0))) :
    hintPhaseRunBudget S events.length N budget ≤ (base + 44) * events.length +
      extra * (events.filter HintTreeEvent.linearWork).length + 29 * N + 67 := by
  apply hintPhaseRunBudget_split
  intro i
  exact hCost i.val i.isLt _ (by rw [Nat.zero_add]; exact List.getElem?_eq_getElem i.isLt)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPhaseRunBudget_of_follows
end -- Def_LinearSetReconciliation327_Main_HintBudgetFollows20261120

section -- Def_LinearSetReconciliation327_Main_HintBinaryNodeResidual20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintNodeResidual_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node first offset Bc t : ℕ)
    (N : ℕ) (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hW : 0 < E.W)
    (hControl : D.placement.control = D.control)
    (hInfo : (D.placement.info node).universeSize = N)
    (hN : 1 ≤ N) (ht : t ≤ N) (hWord : 16 < 2 ^ E.W)
    (hSlice : HintEventSlice D first (hintResidualEvents (crFamily S) node offset N t)) :
    let L := D.placement
    let A := L.arena node
    let CR := crFamily S
    let leaf := Node.cr N t
    let data := S.data N t
    let words := wordsOf E.W data.R
    let colBase := hintSubtreeColBase Bc leaf
    let items := hintChildUpdateSchedule CR Bc colBase leaf 0 words
    let table := L.residualTable node
    let spill := A.crRegisters + 16
    let spillSize := 2 ^ (data.W + 1) + 1
    let spillEnd := spill + spillSize + crSourceSteps S N t + 1
    D.control + 2 < A.result →
    A.result + N ≤ A.residual →
    A.residual + words + 2 ≤ A.residualBitmap + 1 →
    A.residualBitmap + N < A.crRegisters →
    spillEnd < 2 ^ E.W →
    HintStagePre E E.W data.R offset A.residual →
    table + 3 < 2 ^ E.W →
    E.det (table + 3) = D.control →
    UpSavedLayout E table items →
    E.det (table % 2 ^ E.W) % 2 ^ E.W = items.length →
    (∀ i < N, UpLocalTree CR (upShiftDetEnv E table) i Bc colBase leaf () 0 0 0) →
    data.W + 1 < E.W →
    L.crTable node + 2 ^ data.W < 2 ^ E.W →
    A.residual * E.W + data.R < 2 ^ E.W →
    (A.residual * E.W + data.R) / E.W < spill →
    (hintCRTableBlock data.W data.det).At E (L.crTable node) →
    (∀ p : Fin D.events.length, hintEventDescriptor header D.events (hintEventRecord S H L) p.val +
      (D.events[p.val]).recordLength < 2 ^ E.W) →
    (∀ m m', CRMemFrame A.result spillEnd m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first (1 + N + 1 + 1)
      (fun m => HintBinaryMemory m A.result N ∧ HintFreshWords A.residual words m ∧
        HintFreshWords spill spillSize m ∧ keep m)
      (fun m => HintBinaryMemory m A.result N ∧ keep m) := by
  let L := D.placement
  let A := L.arena node
  let CR := crFamily S
  let leaf := Node.cr N t
  let data := S.data N t
  let words := wordsOf E.W data.R
  let spill := A.crRegisters + 16
  let spillSize := 2 ^ (data.W + 1) + 1
  let spillEnd := spill + spillSize + crSourceSteps S N t + 1
  let fresh := HintFreshWords spill spillSize
  let withSpill := fun m => fresh m ∧ keep m
  dsimp only
  intro hCtrl hRes hBitmap hRegs hSpill hPre hTable hReturn hLayout hCount hLocal hSmall
    hCRSpan hInput hSep hCRTable hDescriptors hFrame hCursor
  change D.control + 2 < A.result at hCtrl
  change A.result + N ≤ A.residual at hRes
  change A.residual + words + 2 ≤ A.residualBitmap + 1 at hBitmap
  change A.residualBitmap + N < A.crRegisters at hRegs
  change spillEnd < 2 ^ E.W at hSpill
  change (∀ m m', CRMemFrame A.result spillEnd m m' → keep m → keep m') at hFrame
  have hSpillEq : spill = A.crRegisters + 16 := rfl
  have hEndEq : spillEnd = spill + spillSize + crSourceSteps S N t + 1 := rfl
  have hSpillLe : spill ≤ spillEnd := by
    rw [hEndEq]
    exact (Nat.le_add_right _ spillSize).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ 1))
  have hSpillFit : spill < 2 ^ E.W := hSpillLe.trans_lt hSpill
  have hCtrlSpill : D.control + 2 < spill := by omega
  have hSmallEnd : A.residual + words + 2 ≤ spill := by omega
  have hPayEnd : A.residual + (words + 2) ≤ 2 ^ E.W := by
    rw [← Nat.add_assoc]
    exact hSmallEnd.trans hSpillFit.le
  have hDest : A.residual < 2 ^ E.W := by omega
  have hResToBit : A.result + N ≤ A.residualBitmap := by omega
  have hResFit : A.result < 2 ^ E.W := by omega
  have hBitEnd : A.residualBitmap + N ≤ 2 ^ E.W := by
    exact (hRegs.trans (hSpillEq ▸ Nat.lt_add_of_pos_right (by decide : 0 < 16))).le.trans hSpillFit.le
  have hBitFit : A.residualBitmap < 2 ^ E.W := by omega
  have hCountFit : N < 2 ^ E.W := by omega
  have hWord1 : 1 < 2 ^ E.W := by omega
  have hWord2 : 2 < 2 ^ E.W := by omega
  have hWord11 : 11 < 2 ^ E.W := by omega
  have hSpillFrame (m m' : ℕ → ℕ) (hf : CRMemFrame A.residual (A.residual + words + 2) m m')
      (hk : withSpill m) : withSpill m' :=
    ⟨fun i hi => (hf _ (Or.inr (by omega))).trans (hk.1 i hi),
      hFrame _ _ (fun a ha => hf a (by
        rcases ha with h | h
        · exact Or.inl (h.trans_le (Nat.le_trans (Nat.le_add_right _ _) hRes))
        · exact Or.inr (hSmallEnd.trans (hSpillLe.trans h)))) hk.2⟩
  have hSpillCursor (m : ℕ → ℕ) (v : ℕ) (hk : withSpill m) :
      withSpill (Function.update m (D.control + 2) v) :=
    ⟨hk.1.update_below _ _ hCtrlSpill, hCursor m v hk.2⟩
  have hTagRecord {i : Fin D.events.length} {e : HintTreeEvent}
      (he : D.events[i.val]? = some e) (j : ℕ) (hj : j ≤ e.recordLength) :
      hintEventDescriptor header D.events (hintEventRecord S H L) i.val + j < 2 ^ E.W := by
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) i.isLt).symm.trans he)
    exact (Nat.add_le_add_left (show j ≤ (D.events[i.val]).recordLength by rw [hEq]; exact hj) _).trans_lt
      (hDescriptors i)
  have hTailLength : (hintResidualEvents CR node offset N t).length = N + 3 :=
    hintResidualEvents_length CR node offset N t
  have hRead (i : ℕ) (hi : i < N + 3) :
      D.events[first + i]? = (hintResidualEvents CR node offset N t)[i]? :=
    hSlice.read i (by rwa [hTailLength])
  have hCopy : D.events[first]? = some (.residualCopy node offset data.R) := by
    have h := (hRead 0 (by omega)).trans (hintResidualEvents_copy CR node offset N t)
    rw [Nat.add_zero] at h
    exact h
  have hToggles (i : ℕ) (hi : i < N) : D.events[first + 1 + i]? = some (.residualToggle node i) := by
    rw [Nat.add_assoc, hRead _ (by omega)]
    exact hintResidualEvents_toggle CR node offset N t i hi
  have hDecode : D.events[first + 1 + N]? = some (.decodeResidual node N t) := by
    rw [Nat.add_assoc, hRead _ (by omega)]
    exact hintResidualEvents_decode CR node offset N t
  have hCorrect : D.events[first + 1 + N + 1]? = some (.correctEstimate node) := by
    simp only [Nat.add_assoc]
    rw [hRead _ (by omega)]
    exact hintResidualEvents_correct CR node offset N t
  let copy := hintResidualCopy_total S H D header node first t offset N E withSpill hWidth hWord2
    hCopy hCtrl hRes hDest hPre
    (fun p hp => hTagRecord (by rw [hp]; exact hCopy) 3 (by simp [HintTreeEvent.recordLength]))
    (by
      intro m m' hf
      have hf' : CRMemFrame A.residual (A.residual + words) m m' := hf
      exact hSpillFrame m m' (fun a ha => hf' a (by rcases ha with h | h <;> omega)))
    hSpillCursor
  let toggle := hintResidualToggle_total S H D header node (first + 1) t Bc N E withSpill
    hControl hToggles hWord hCountFit.le hCtrl hRes hPayEnd hTable hReturn hLayout hCount hLocal
    (by
      intro p hp hb
      have hPos : p.val = first + 1 + (p.val - (first + 1)) := by omega
      exact hTagRecord (hPos ▸ hToggles _ (by omega)) 3 (by simp [HintTreeEvent.recordLength]))
    hSpillFrame hSpillCursor
  let decode := hintResidualDecode_total S H D header node (first + 1 + N) t N E keep
    hControl hWidth hW hN ht hWord11 hDecode hCtrl hRes hResToBit hRegs hSpill hSmall hCRSpan hInput hSep hCRTable
    (fun p hp => hTagRecord (by rw [hp]; exact hDecode) 11 (by simp [HintTreeEvent.recordLength]))
    (by
      intro m m' hf
      have hf' : CRMemFrame A.residualBitmap spillEnd m m' := hf
      exact hFrame m m' (fun a ha => hf' a (by rcases ha with h | h <;> omega)))
    hCursor
  let correct := hintCorrectEstimate_total S H D header node (first + 1 + N + 1) N E keep
    hInfo hCorrect hWord1 hCtrl hResFit hBitFit hCountFit hResToBit hBitEnd
    (fun p hp => hTagRecord (by rw [hp]; exact hCorrect) 2 (by simp [HintTreeEvent.recordLength]))
    (by
      intro m m' hf
      have hf' : CRMemFrame A.result (A.result + N) m m' := hf
      exact hFrame m m' (fun a ha => hf' a (by
        rcases ha with h | h
        · exact Or.inl h
        · exact Or.inr (hResToBit.trans (((Nat.le_add_right _ N).trans (hRegs.le.trans ((Nat.le_add_right _ 16).trans (hSpillLe.trans h))))))))) 
    hCursor
  let updated := copy.append toggle
  have hPos : 0 < 1 := Nat.zero_lt_one
  let readBack : HintDecoderPhase S H D E header (first + 1 + N) 1
      (fun m => HintBinaryMemory m A.result N ∧ HintPackedMemory E.W A.residual data.R m ∧ withSpill m)
      (fun m => HintBinaryMemory m A.result N ∧ HintBinaryMemory m A.residualBitmap N ∧ keep m) :=
    decode.adapt hPos (fun _ h => ⟨h.1, h.2.2⟩) (fun _ h => h)
    (fun m v h => ⟨h.1.update_below v hCtrl, h.2.1.update_below v (by omega),
      hSpillCursor m v h.2.2⟩)
    (fun m v h => ⟨h.1.update_below v hCtrl, h.2.1.update_below v (by omega), hCursor m v h.2.2⟩)
  let recovered := updated.append_at readBack (Nat.add_assoc _ _ _)
  exact recovered.append_at correct (by change first + 1 + N + 1 = first + (1 + N + 1); omega)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintNodeResidual_total
end -- Def_LinearSetReconciliation327_Main_HintBinaryNodeResidual20261120

section -- Def_LinearSetReconciliation327_Main_HintResidualBudget20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem HintDecoderPhase.append_plain_budget_follows {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header first n m : ℕ} {A B C : (ℕ → ℕ) → Prop}
    {p : HintDecoderPhase S H D E header first n A B}
    {q : HintDecoderPhase S H D E header (first + n) m B C} (cap : HintTreeEvent → ℕ)
    (hp : HintBudgetFollows D.events first n p.budget cap)
    (hq : HintBudgetFollows D.events (first + n) m q.budget cap) :
    HintBudgetFollows D.events first (n + m) (p.append q).budget cap := hp.append hq

theorem hintNodeResidual_total_budget_follows (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node first offset Bc t : ℕ)
    (N : ℕ) (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hW : 0 < E.W)
    (hControl : D.placement.control = D.control)
    (hInfo : (D.placement.info node).universeSize = N)
    (hN : 1 ≤ N) (ht : t ≤ N) (hWord : 16 < 2 ^ E.W)
    (hSlice : HintEventSlice D first (hintResidualEvents (crFamily S) node offset N t)) (base extra : ℕ) :
    let L := D.placement
    let A := L.arena node
    let CR := crFamily S
    let leaf := Node.cr N t
    let data := S.data N t
    let words := wordsOf E.W data.R
    let colBase := hintSubtreeColBase Bc leaf
    let items := hintChildUpdateSchedule CR Bc colBase leaf 0 words
    let table := L.residualTable node
    let spill := A.crRegisters + 16
    let spillSize := 2 ^ (data.W + 1) + 1
    let spillEnd := spill + spillSize + crSourceSteps S N t + 1
    ∀
      (hCtrl : D.control + 2 < A.result)
      (hRes : A.result + N ≤ A.residual)
      (hBitmap : A.residual + words + 2 ≤ A.residualBitmap + 1)
      (hRegs : A.residualBitmap + N < A.crRegisters)
      (hSpill : spillEnd < 2 ^ E.W)
      (hPre : HintStagePre E E.W data.R offset A.residual)
      (hTable : table + 3 < 2 ^ E.W)
      (hReturn : E.det (table + 3) = D.control)
      (hLayout : UpSavedLayout E table items)
      (hCount : E.det (table % 2 ^ E.W) % 2 ^ E.W = items.length)
      (hLocal : (∀ i < N, UpLocalTree CR (upShiftDetEnv E table) i Bc colBase leaf () 0 0 0))
      (hSmall : data.W + 1 < E.W)
      (hCRSpan : L.crTable node + 2 ^ data.W < 2 ^ E.W)
      (hResFit : A.residual * E.W + data.R < 2 ^ E.W)
      (hSeparation : (A.residual * E.W + data.R) / E.W < spill)
      (hCRTable : (hintCRTableBlock data.W data.det).At E (L.crTable node))
      (hDescriptor : (∀ p : Fin D.events.length, hintEventDescriptor header D.events (hintEventRecord S H L) p.val +
      (D.events[p.val]).recordLength < 2 ^ E.W))
      (hFrame : (∀ m m', CRMemFrame A.result spillEnd m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (hCopyCost : 17 * data.R + 13 ≤ extra)
      (hToggleCost : 147 * items.length + 24 ≤ base)
      (hDecodeCost : hintCRNodeBudget S N t ≤ extra)
      (hCorrectCost : 11 * N + 11 ≤ extra),
      HintBudgetFollows D.events first (1 + N + 1 + 1) (hintNodeResidual_total S H D E header node first offset Bc t N keep hWidth hW hControl hInfo hN ht hWord hSlice hCtrl hRes hBitmap hRegs hSpill hPre hTable hReturn hLayout hCount hLocal hSmall hCRSpan hResFit hSeparation hCRTable hDescriptor hFrame hCursor).budget
        (fun e => base + (if e.linearWork then extra else 0)) := by
  dsimp only
  intro hCtrl hRes hBitmap hRegs hSpill hPre hTable hReturn hLayout hCount hLocal hSmall
    hCRSpan hResFit hSeparation hCRTable hDescriptor hFrame hCursor hCopyCost hToggleCost hDecodeCost hCorrectCost
  have hRead (i : ℕ) (hi : i < N + 3) :
      D.events[first + i]? = (hintResidualEvents (crFamily S) node offset N t)[i]? :=
    hSlice.read i (by rwa [hintResidualEvents_length])
  unfold hintNodeResidual_total
  apply HintDecoderPhase.append_budget_follows
  · apply HintDecoderPhase.append_budget_follows
    · apply HintDecoderPhase.append_plain_budget_follows
      · intro i hi e he
        have hz : i = 0 := by omega
        subst i
        have hEvent := (hRead 0 (by omega)).trans (hintResidualEvents_copy (crFamily S) node offset N t)
        have hEq := Option.some.inj (he.symm.trans hEvent)
        subst e
        change 17 * (S.data N t).R + 13 ≤ base + extra
        exact hCopyCost.trans (Nat.le_add_left _ _)
      · intro i hi e he
        have hEvent : D.events[(first + 1) + i]? = some (.residualToggle node i) := by
          rw [Nat.add_assoc, hRead _ (by omega)]
          exact hintResidualEvents_toggle (crFamily S) node offset N t i hi
        have hEq := Option.some.inj (he.symm.trans hEvent)
        subst e
        change 147 * (hintChildUpdateSchedule (crFamily S) Bc (hintSubtreeColBase Bc (.cr N t))
          (.cr N t) 0 (wordsOf E.W (S.data N t).R)).length + 24 ≤ base + 0
        simpa only [Nat.add_zero] using hToggleCost
    · apply HintDecoderPhase.adapt_budget_follows
      intro i hi e he
      have hz : i = 0 := by omega
      subst i
      have hEvent : D.events[(first + 1 + N) + 0]? = some (.decodeResidual node N t) := by
        rw [Nat.add_zero, Nat.add_assoc, hRead _ (by omega)]
        exact hintResidualEvents_decode (crFamily S) node offset N t
      have hEq := Option.some.inj (he.symm.trans hEvent)
      subst e
      change hintCRNodeBudget S N t ≤ base + extra
      exact hDecodeCost.trans (Nat.le_add_left _ _)
  · intro i hi e he
    have hz : i = 0 := by omega
    subst i
    have hEvent : D.events[(first + 1 + N + 1) + 0]? = some (.correctEstimate node) := by
      simp only [Nat.add_zero, Nat.add_assoc]
      rw [hRead _ (by omega)]
      exact hintResidualEvents_correct (crFamily S) node offset N t
    have hEq := Option.some.inj (he.symm.trans hEvent)
    subst e
    change 11 * N + 11 ≤ base + extra
    exact hCorrectCost.trans (Nat.le_add_left _ _)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintNodeResidual_total_budget_follows
end -- Def_LinearSetReconciliation327_Main_HintResidualBudget20261120


