-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_15
-- name    : LinearSetReconciliation327_Main_Bundle51_15
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T08:30:50.249403+00:00
-- url     : https://prove2.me/theorems/0982b5fa-82ed-406e-917c-f074e6cc6b34
-- title:
--   LinearSetReconciliation327 鈥?Bundle51_15
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_15` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_09
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_10
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_12
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_13
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_14

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_15
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintBinaryFold20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedBinaryColumn20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedColumnBudget20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRecursiveRowsBudget20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRecursiveFoldBudget20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedBinaryRecursive20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedRecursiveBudget20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDirectBudget20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintNodeResidualPhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedRowTail20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedRecursive20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedDirect20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedTree20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedTreeRoot20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintBinaryFold20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintRecursiveRows_total (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (E : RAMEnv) (header node seed offset first : ℕ)
    (sch : RowScheme) (children : Fin sch.ℓ → Node)
    (J : Finset ℕ) (payloadOffset : ℕ → ℕ) (pending : ℕ → (ℕ → ℕ) → Prop) :
    let A := D.placement.arena node
    let columns := hintRecursiveColumnEvents (crFamily S) payloadOffset sch children node seed offset
    let blocks := List.ofFn columns
    let hints := fun m => HintBitmap m A.hints sch.N J
    let inv := fun i m => hints m ∧
      HintTranscriptBinary sch A.transcript i m ∧ pending i m
    D.control + 2 < A.hints →
    (∀ m v, pending 0 m → pending 0 (Function.update m (D.control + 2) v)) →
    (∀ col : Fin sch.ℓ, HintDecoderPhase S H D E header
      (first + ((blocks.take col.val).flatten).length) (columns col).length
      (inv col.val) (inv (col.val + 1))) →
    HintDecoderPhase S H D E header first blocks.flatten.length
      (fun m => hints m ∧ pending 0 m)
      (fun m => hints m ∧ HintTranscriptBinary sch A.transcript sch.ℓ m ∧ pending sch.ℓ m) := by
  let A := D.placement.arena node
  let columns := hintRecursiveColumnEvents (crFamily S) payloadOffset sch children node seed offset
  let blocks := List.ofFn columns
  let hints := fun m => HintBitmap m A.hints sch.N J
  let inv := fun i m => hints m ∧
    HintTranscriptBinary sch A.transcript i m ∧ pending i m
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
    (fun _ => Iff.rfl)

abbrev HintBinaryColumnPhase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node seed first t : ℕ) (sch : RowScheme)
    (Xs Ys : Fin sch.ℓ → ℕ) (children : Fin sch.ℓ → Node)
    (J : Finset ℕ) (col : Fin sch.ℓ) :=
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
    (∀ m m', (∀ a, (a < L.rowScratch ∨ D.listBase ≤ a) →
      (a < gate ∨ gate + sch.m ≤ a) → (a < lo ∨ hi ≤ a) → m' a = m a) → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintBinarySubtreePhase S H D E header cn cs (first + sch.m + 1 + sch.m) child →
    HintDecoderPhase S H D E header first events.length
      (fun m => (HintBitmap m A.hints sch.N J ∧
        HintTranscriptBinary sch A.transcript col.val m ∧ keep m) ∧
        HintFreshWords B.payload (wordsOf E.W (synLen CR child)) m ∧
        HintNodeFreshTail D cn child.nodeCount m)
      (fun m => HintBitmap m A.hints sch.N J ∧
        HintTranscriptBinary sch A.transcript (col.val + 1) m ∧ keep m)

noncomputable def hintRecursiveFold_total (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (E : RAMEnv) (header node seed first t : ℕ)
    (sch : RowScheme) (Xs Ys : Fin sch.ℓ → ℕ) (children : Fin sch.ℓ → Node)
    (J : Finset ℕ)
    (keep : (ℕ → ℕ) → Prop) :
    let CR := crFamily S
    let A := D.placement.arena node
    let T := Node.recursive sch t Xs Ys children
    let arena := hintArenaStart D.heap D.stride
    let word := D.placement.inputWord node
    let offsets := fun i => D.placement.inputWord i * E.W
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
    (∀ col : Fin sch.ℓ,
      let cn := hintChildPhysicalIndex children node col
      let B := D.placement.arena cn
      B.payload = arena cn ∧ B.payload ≤ B.result ∧
      B.payload + wordsOf E.W (synLen CR (children col)) ≤ arena (cn + (children col).nodeCount)) →
    (∀ m m', HintSubtreeFrame D node T.nodeCount m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    (∀ col : Fin sch.ℓ, HintBinaryColumnPhase S H D E header node seed (start col) t sch Xs Ys children J col) →
    (∀ col : Fin sch.ℓ, HintBinarySubtreePhase S H D E header
      (hintChildPhysicalIndex children node col) (hintChildSchemeIndex children seed col)
      (start col + sch.m + 1 + sch.m) (children col)) →
    HintDecoderPhase S H D E header first blocks.flatten.length
      (fun m => (HintBitmap m A.hints sch.N J ∧ HintNodeFreshTail D node T.nodeCount m) ∧ keep m)
      (fun m => HintBitmap m A.hints sch.N J ∧
        HintTranscriptBinary sch A.transcript sch.ℓ m ∧
        ownFresh m ∧ keep m) := by
  let CR := crFamily S
  let A := D.placement.arena node
  let T := Node.recursive sch t Xs Ys children
  let arena := hintArenaStart D.heap D.stride
  let word := D.placement.inputWord node
  let offsets := fun i => D.placement.inputWord i * E.W
  let blocks := List.ofFn (hintRecursiveColumnEvents CR offsets sch children node seed (word * E.W))
  let start := fun col : Fin sch.ℓ => first + ((blocks.take col.val).flatten).length
  let ownFresh := fun (mem : ℕ → ℕ) => ∀ a, A.result ≤ a → a < arena (node + 1) → mem a = 0
  let childIndex := fun i : ℕ => node + 1 + ((List.ofFn fun s => (children s).nodeCount).take i).sum
  let endAddr := arena (node + T.nodeCount)
  let future := fun (i : ℕ) (mem : ℕ → ℕ) => ∀ a, arena (childIndex i) ≤ a → a < endAddr → mem a = 0
  let pending := fun i m => ownFresh m ∧ future i m ∧ keep m
  let hints := fun m => HintBitmap m A.hints sch.N J
  dsimp only
  intro hControl hScratch hHeap hTran hTranLo hTranEnd hOwnLo hHead
  intro hChildren hKeep hCursor columns calls
  change D.listBase ≤ A.transcript at hTran
  change arena node ≤ A.transcript at hTranLo
  change A.transcript + sch.ℓ * sch.m ≤ A.hints at hTranEnd
  change A.hints + sch.N ≤ A.result at hOwnLo
  change A.result ≤ arena (node + 1) at hHead
  change ∀ m m', HintSubtreeFrame D node T.nodeCount m m' → keep m → keep m' at hKeep
  have hCursorTran : D.control + 2 < A.transcript := by omega
  have hCursorHints : D.control + 2 < A.hints := by omega
  have hCursorOwn : D.control + 2 < A.result := by omega
  have hCursorFuture (i : ℕ) : D.control + 2 < arena (childIndex i) := by
    exact hControl.trans_le (hScratch.trans (hHeap.trans (Nat.le_add_right _ _)))
  have hPendingCursor (i : ℕ) (m : ℕ → ℕ) (v : ℕ) (hm : pending i m) :
      pending i (Function.update m (D.control + 2) v) := by
    obtain ⟨ho, hf, hk⟩ := hm
    refine ⟨?_, ?_, hCursor m v hk⟩
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
  have hRun := hintRecursiveRows_total S H D E header node seed (word * E.W) first sch children J
    offsets pending hCursorHints (hPendingCursor 0) (by
      intro col
      let cn := hintChildPhysicalIndex children node col
      let B := D.placement.arena cn
      let last := cn + (children col).nodeCount
      let gate := A.transcript + col.val * sch.m
      let prev := HintTranscriptBinary sch A.transcript col.val
      let next := HintTranscriptBinary sch A.transcript (col.val + 1)
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
      let p := columns col (pending (col.val + 1))
        (by
          intro m m' hf hm
          obtain ⟨ho, hu, hk⟩ := hm
          have frame : ∀ a, (a < D.placement.rowScratch ∨ D.listBase ≤ a) →
              (a < gate ∨ gate + sch.m ≤ a) → (a < arena cn ∨ arena last ≤ a) → m' a = m a := hf
          refine ⟨?_, ?_, hKeep m m' ?_ hk⟩
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
      · rintro m ⟨hh, ht, ho, hf, hk⟩
        refine ⟨⟨hh, ht, ho, ?_, hk⟩, ?_, ?_⟩
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
    change (hints m ∧ pending 0 m) ↔ ((HintBitmap m A.hints sch.N J ∧ HintNodeFreshTail D node T.nodeCount m) ∧ keep m)
    constructor
    · rintro ⟨hh, ho, hf, hk⟩
      refine ⟨⟨hh, ?_⟩, hk⟩
      intro a ha hb
      by_cases h : a < arena (node + 1)
      · exact ho a ha h
      · exact hf a (by rw [hFirst]; omega) hb
    · rintro ⟨⟨hh, hf⟩, hk⟩
      have hN := hintNodeCount_pos T
      have hHeadEnd : arena (node + 1) ≤ endAddr := hintArenaStart_mono D.heap D.stride (by omega)
      refine ⟨hh, (fun a ha hb => hf a ha (hb.trans_le hHeadEnd)), ?_, hk⟩
      intro a ha hb
      rw [hFirst] at ha
      exact hf a (hHead.trans ha) hb
  · intro m
    change (hints m ∧ HintTranscriptBinary sch A.transcript sch.ℓ m ∧ pending sch.ℓ m) ↔ _
    constructor
    · rintro ⟨hh, ht, ho, _, hk⟩
      exact ⟨hh, ht, ho, hk⟩
    · rintro ⟨hh, ht, ho, hk⟩
      refine ⟨hh, ht, ho, ?_, hk⟩
      intro a ha hb
      rw [hLast] at ha
      exact (Nat.not_lt_of_ge ha hb).elim

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRecursiveFold_total
end -- Def_LinearSetReconciliation327_Main_HintBinaryFold20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedBinaryColumn20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintPlacedColumn_total (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (seedData : (hintSpec R).Seed) (up previous : ℕ → ℕ)
    (W Bc header node seed first N X Y t : ℕ)
    (Xs Ys : Fin (H.scheme N X Y).ℓ → ℕ) (children : Fin (H.scheme N X Y).ℓ → Node)
    (hchildren : ∀ col, IsSchemeTree H (children col))
    (J : Finset ℕ) (col : Fin (H.scheme N X Y).ℓ)
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
    BlockOf R seed (schemeNodes T) →
    HintPlacedSubtree (crFamily S) H D hT node seed →
    (node = 0 → synLen (crFamily S) T ≤ synLen (crFamily S) R) →
    hintArenaStart D.heap D.stride D.infos.length * W < 2 ^ W →
    hintDecoderDetEnd S H D header < 2 ^ W →
    HintEventSlice D first (hintRecursiveColumnEvents (crFamily S) offsets sch children node seed (offsets node) col) →
    HintBinaryColumnPhase S H D E header node seed first t sch Xs Ys children J col := by
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
  exact hintRecursiveColumn_total S H D E header node seed first N X Y t Bc Xs Ys children r J col
    keep rfl hW hWord rfl hInfoN hInfoXY hChild hm hSize hSteps hSeedFit hKFit hStepsFit hBXFit hBYFit
    hCoeffSpace (fun a b c => hCoeff a c b) hPerm hSlice hAM.scratch hAM.list hALo hScratch hTran hPar
    hBa hInputWord (hBWork.le.trans hBM.hints) hBHint hBOut hBLastFit hRoom1 hRoom2 hInputFit hInputSep
    hTable3 hReturn hLayout hCount hLocal
    (fun k => ⟨(hThreshold k).1, ((hThreshold k).2.trans_lt hDet).le⟩)
    (fun k => by rw [← hintEventRecord_length S H L]; exact (hintDecoderEvent_end S H D header k).trans_lt hDet)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedColumn_total
end -- Def_LinearSetReconciliation327_Main_HintPlacedBinaryColumn20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedColumnBudget20261120
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearSetReconciliation327.Main

theorem HintDecoderPhase.cast_count_budget_eq
    {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables} {E : RAMEnv}
    {header first n m : ℕ} {A B : (ℕ → ℕ) → Prop}
    (h : n = m) (p : HintDecoderPhase S H D E header first n A B) :
    ((cast (congrArg (fun i => HintDecoderPhase S H D E header first i A B) h) p)).budget = p.budget := by
  subst m
  rfl

theorem HintDecoderPhase.cast_first_budget_eq
    {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables} {E : RAMEnv}
    {header first next n : ℕ} {A B : (ℕ → ℕ) → Prop}
    (h : first = next) (p : HintDecoderPhase S H D E header first n A B) :
    ((cast (congrArg (fun i => HintDecoderPhase S H D E header i n A B) h) p)).budget = p.budget := by
  subst next
  rfl

def HintBinaryColumnPhase.BudgetFollows {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header node seed first t : ℕ} {sch : RowScheme}
    {Xs Ys : Fin sch.ℓ → ℕ} {children : Fin sch.ℓ → Node} {J : Finset ℕ} {col : Fin sch.ℓ}
    (p : HintBinaryColumnPhase S H D E header node seed first t sch Xs Ys children J col)
    (cap : HintTreeEvent → ℕ) : Prop :=
  let offsets := fun i => D.placement.inputWord i * E.W
  ∀ keep hKeep hCursor call, call.BudgetFollows cap →
    HintBudgetFollows D.events first
      (hintRecursiveColumnEvents (crFamily S) offsets sch children node seed (offsets node) col).length
      (p keep hKeep hCursor call).budget cap

theorem hintPlacedColumn_total_budget_follows (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (seedData : (hintSpec R).Seed) (up previous : ℕ → ℕ)
    (W Bc header node seed first N X Y t : ℕ)
    (Xs Ys : Fin (H.scheme N X Y).ℓ → ℕ) (children : Fin (H.scheme N X Y).ℓ → Node)
    (hchildren : ∀ col, IsSchemeTree H (children col))
    (J : Finset ℕ) (col : Fin (H.scheme N X Y).ℓ)
    (hHeader : 3 < header) (hW : 0 < W) (hWord : 30 < 2 ^ W) (hBc : Bc + 1 < 2 ^ W)
    (hFit : (hintSpec R).Fits W)
    (hSeedFit : seed < 2 ^ W) (hKFit : H.Nmax N X Y < 2 ^ W)
    (hStepsFit : H.ell N X Y < 2 ^ W) (hBXFit : H.BX N X Y < 2 ^ W)
    (hBYFit : H.BY N X Y + 1 < 2 ^ W)
    (hm : H.rows X Y ≤ N) (hSize : (children col).N = (H.scheme N X Y).m)
    (hSteps : 0 < H.ell N X Y)
    (hDims : UpDimsBound (2 ^ W - 1) (children col))
    (hStatic : UpTreeStatic (crFamily S) Bc (children col).N (children col))
    (hChildSeed : hintChildSchemeIndex children seed col + (schemeNodes (children col)).length < 2 ^ W) (U radius base extra : ℕ) :
    let sch := H.scheme N X Y
    let T := Node.recursive sch t Xs Ys children
    let hT : IsSchemeTree H T := .recursive N X Y t Xs Ys children hchildren
    let D := hintDecoderTables S H hR W Bc header
    let L := D.placement
    let E := (hintSpec R).env W (D.det S H up previous header R.N) seedData
    let offsets := fun i => L.inputWord i * W
    ∀
      (hBlock : BlockOf R seed (schemeNodes T))
      (hPlaced : HintPlacedSubtree (crFamily S) H D hT node seed)
      (hRoot : (node = 0 → synLen (crFamily S) T ≤ synLen (crFamily S) R))
      (hMem : hintArenaStart D.heap D.stride D.infos.length * W < 2 ^ W)
      (hDet : hintDecoderDetEnd S H D header < 2 ^ W)
      (hSlice : HintEventSlice D first (hintRecursiveColumnEvents (crFamily S) offsets sch children node seed (offsets node) col))
      (_hRowCost : HintRowTimeBounds S H N X Y t Bc U radius base extra)
      (_hCopyCost : 17 * synLen (crFamily S) (children col) + 13 ≤ extra)
      (_hToggleCost : 147 * (1 + upRest Bc (children col)) + 24 ≤ base)
      (_hXorCost : 11 * sch.m + 11 ≤ extra),
      HintBinaryColumnPhase.BudgetFollows (hintPlacedColumn_total (R := R) S H hR seedData up previous W Bc header node seed first N X Y t Xs Ys children hchildren J col hHeader hW hWord hBc hFit hSeedFit hKFit hStepsFit hBXFit hBYFit hm hSize hSteps hDims hStatic hChildSeed hBlock hPlaced hRoot hMem hDet hSlice)
        (fun e => base + (if e.linearWork then extra else 0)) := by
  dsimp only
  intro hBlock hPlaced hRoot hMem hDet hSlice hRowCost hCopyCost hToggleCost hXorCost
    keep hKeep hCursor call hCall
  with_unfolding_all simp only [hintPlacedColumn_total, id, hintAndRec_value]
  apply hintRecursiveColumn_total_budget_follows
  · exact hRowCost
  · exact hCopyCost
  · rwa [hintChildUpdateSchedule_length]
  · exact hXorCost
  · exact hCall

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedColumn_total_budget_follows
end -- Def_LinearSetReconciliation327_Main_HintPlacedColumnBudget20261120

section -- Def_LinearSetReconciliation327_Main_HintRecursiveRowsBudget20261120
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearSetReconciliation327.Main

theorem HintDecoderPhase.cast_first_budget_follows
    {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables} {E : RAMEnv}
    {header first next n : ℕ} {A B : (ℕ → ℕ) → Prop}
    (h : first = next) (p : HintDecoderPhase S H D E header next n A B) (cap : HintTreeEvent → ℕ)
    (hp : HintBudgetFollows D.events next n p.budget cap) :
    HintBudgetFollows D.events first n
      ((cast (congrArg (fun i => HintDecoderPhase S H D E header i n A B) h.symm) p)).budget cap := by
  subst first
  exact hp

theorem hintRecursiveRows_total_budget_follows (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (E : RAMEnv) (header node seed offset first : ℕ)
    (sch : RowScheme) (children : Fin sch.ℓ → Node)
    (J : Finset ℕ) (payloadOffset : ℕ → ℕ) (pending : ℕ → (ℕ → ℕ) → Prop) (base extra : ℕ) :
    let A := D.placement.arena node
    let columns := hintRecursiveColumnEvents (crFamily S) payloadOffset sch children node seed offset
    let blocks := List.ofFn columns
    let hints := fun m => HintBitmap m A.hints sch.N J
    let inv := fun i m => hints m ∧
      HintTranscriptBinary sch A.transcript i m ∧ pending i m
    ∀
      (hControl : D.control + 2 < A.hints)
      (hCursor : (∀ m v, pending 0 m → pending 0 (Function.update m (D.control + 2) v)))
      (hPhase : (∀ col : Fin sch.ℓ, HintDecoderPhase S H D E header
      (first + ((blocks.take col.val).flatten).length) (columns col).length
      (inv col.val) (inv (col.val + 1))))
      (_hCost : ∀ col : Fin sch.ℓ, HintBudgetFollows D.events
        (first + ((blocks.take col.val).flatten).length) (columns col).length (hPhase col).budget
        (fun e => base + (if e.linearWork then extra else 0))),
      HintBudgetFollows D.events first blocks.flatten.length (hintRecursiveRows_total S H D E header node seed offset first sch children J payloadOffset pending hControl hCursor hPhase).budget
        (fun e => base + (if e.linearWork then extra else 0)) := by
  dsimp only
  intro hControl hCursor hPhase hCost
  let columns := hintRecursiveColumnEvents (crFamily S) payloadOffset sch children node seed offset
  let blocks := List.ofFn columns
  let size := fun i => if hi : i < sch.ℓ then (columns ⟨i, hi⟩).length else 0
  have hSize (i : Fin sch.ℓ) : size i.val = (columns i).length := by simp [size, i.isLt]
  have hPrefix (i : ℕ) (hi : i ≤ sch.ℓ) :
      hintPhasePrefixCount size i = ((blocks.take i).flatten).length :=
    hintPhasePrefixCount_ofFn columns size hSize i hi
  have hAll : hintPhasePrefixCount size sch.ℓ = blocks.flatten.length := by
    rw [hPrefix _ le_rfl, List.take_of_length_le]
    simp [blocks]
  with_unfolding_all simp only [hintRecursiveRows_total, id, HintDecoderPhase.relabel_budget_eq]
  apply HintDecoderPhase.cast_budget_follows (h := hAll.symm)
  apply HintDecoderPhase.concat_budget_follows
  intro i hi
  let col : Fin sch.ℓ := ⟨i, hi⟩
  have hFirst := congrArg (fun p => first + p) (hPrefix i hi.le)
  have hLen : size i = (columns col).length := hSize col
  apply HintDecoderPhase.cast_first_budget_follows (h := hFirst)
  apply HintDecoderPhase.cast_budget_follows (h := hLen)
  exact hCost col

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRecursiveRows_total_budget_follows
end -- Def_LinearSetReconciliation327_Main_HintRecursiveRowsBudget20261120

section -- Def_LinearSetReconciliation327_Main_HintRecursiveFoldBudget20261120
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearSetReconciliation327.Main

theorem hintRecursiveFold_total_budget_follows (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (E : RAMEnv) (header node seed first t : ℕ)
    (sch : RowScheme) (Xs Ys : Fin sch.ℓ → ℕ) (children : Fin sch.ℓ → Node)
    (J : Finset ℕ)
    (keep : (ℕ → ℕ) → Prop) (base extra : ℕ) :
    let CR := crFamily S
    let A := D.placement.arena node
    let T := Node.recursive sch t Xs Ys children
    let arena := hintArenaStart D.heap D.stride
    let word := D.placement.inputWord node
    let offsets := fun i => D.placement.inputWord i * E.W
    let blocks := List.ofFn (hintRecursiveColumnEvents CR offsets sch children node seed (word * E.W))
    let start := fun col : Fin sch.ℓ => first + ((blocks.take col.val).flatten).length
    let ownFresh := fun (mem : ℕ → ℕ) => ∀ a, A.result ≤ a → a < arena (node + 1) → mem a = 0
    ∀
      (hControl : D.control + 2 < D.placement.rowScratch)
      (hScratch : D.placement.rowScratch ≤ D.listBase)
      (hHeap : D.listBase ≤ D.heap)
      (hTran : D.listBase ≤ A.transcript)
      (hTranLo : arena node ≤ A.transcript)
      (hTranEnd : A.transcript + sch.ℓ * sch.m ≤ A.hints)
      (hOwnLo : A.hints + sch.N ≤ A.result)
      (hHead : A.result ≤ arena (node + 1))
      (hChildren : (∀ col : Fin sch.ℓ,
      let cn := hintChildPhysicalIndex children node col
      let B := D.placement.arena cn
      B.payload = arena cn ∧ B.payload ≤ B.result ∧
      B.payload + wordsOf E.W (synLen CR (children col)) ≤ arena (cn + (children col).nodeCount)))
      (hKeep : (∀ m m', HintSubtreeFrame D node T.nodeCount m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (columns : (∀ col : Fin sch.ℓ, HintBinaryColumnPhase S H D E header node seed (start col) t sch Xs Ys children J col))
      (calls : (∀ col : Fin sch.ℓ, HintBinarySubtreePhase S H D E header
      (hintChildPhysicalIndex children node col) (hintChildSchemeIndex children seed col)
      (start col + sch.m + 1 + sch.m) (children col)))
      (_hColumns : ∀ col, (columns col).BudgetFollows (fun e => base + (if e.linearWork then extra else 0)))
      (_hCalls : ∀ col, (calls col).BudgetFollows (fun e => base + (if e.linearWork then extra else 0))),
      HintBudgetFollows D.events first blocks.flatten.length (hintRecursiveFold_total S H D E header node seed first t sch Xs Ys children J keep hControl hScratch hHeap hTran hTranLo hTranEnd hOwnLo hHead hChildren hKeep hCursor columns calls).budget
        (fun e => base + (if e.linearWork then extra else 0)) := by
  dsimp only
  intro hControl hScratch hHeap hTran hTranLo hTranEnd hOwnLo hHead hChildren hKeep hCursor columns calls hColumns hCalls
  with_unfolding_all simp only [hintRecursiveFold_total, id, HintDecoderPhase.relabel_budget_eq]
  apply hintRecursiveRows_total_budget_follows
  intro col
  with_unfolding_all simp only [HintDecoderPhase.adapt_budget_eq, id]
  exact hColumns col _ _ _ _ (hCalls col)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintRecursiveFold_total_budget_follows
end -- Def_LinearSetReconciliation327_Main_HintRecursiveFoldBudget20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedBinaryRecursive20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintPlacedRecursive_total (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (seedData : (hintSpec R).Seed)
    (up previous : ℕ → ℕ) (W Bc header node seed first N X Y t : ℕ)
    (Xs Ys : Fin (H.scheme N X Y).ℓ → ℕ) (children : Fin (H.scheme N X Y).ℓ → Node)
    (hc : ∀ col, IsSchemeTree H (children col))
    (J : Finset ℕ)
    (hHeader : 3 < header) (hW : 0 < W) (hWord : 30 < 2 ^ W) (hBc : Bc + 1 < 2 ^ W)
    (hFit : (hintSpec R).Fits W) (hSeed : seed < 2 ^ W)
    (hK : H.Nmax N X Y < 2 ^ W) (hEll : H.ell N X Y < 2 ^ W)
    (hBX : H.BX N X Y < 2 ^ W) (hBY : H.BY N X Y + 1 < 2 ^ W)
    (hmPos : 0 < H.rows X Y) (hm : H.rows X Y ≤ N) (hSteps : 0 < H.ell N X Y)
    (ht : t ≤ N)
    (hSize : ∀ col, (children col).N = (H.scheme N X Y).m)
    (hDims : ∀ col, UpDimsBound (2 ^ W - 1) (children col))
    (hStatic : ∀ col, UpTreeStatic (crFamily S) Bc (children col).N (children col))
    (hChildSeed : ∀ col, hintChildSchemeIndex children seed col + (schemeNodes (children col)).length < 2 ^ W)
    (hSmall : (S.data N t).W + 1 < W) (hCR : UpCRColumns (crFamily S) Bc N t) :
    let sch := H.scheme N X Y
    let T := Node.recursive sch t Xs Ys children
    let hT : IsSchemeTree H T := .recursive N X Y t Xs Ys children hc
    let D := hintDecoderTables S H hR W Bc header
    let E := (hintSpec R).env W (D.det S H up previous header R.N) seedData
    let offsets := fun i => D.placement.inputWord i * W
    BlockOf R seed (schemeNodes T) →
    HintPlacedSubtree (crFamily S) H D hT node seed →
    (node = 0 → synLen (crFamily S) T ≤ synLen (crFamily S) R) →
    hintArenaStart D.heap D.stride D.infos.length * W < 2 ^ W →
    hintDecoderDetEnd S H D header < 2 ^ W →
    HintEventSlice D first (hintTreeEvents (crFamily S) offsets T node seed (offsets node)) →
    (∀ (col : Fin sch.ℓ) (start : ℕ),
      let C := children col
      let cn := hintChildPhysicalIndex children node col
      let cs := hintChildSchemeIndex children seed col
      HintEventSlice D start (hintTreeEvents (crFamily S) offsets C cn cs (offsets cn)) →
      HintBinarySubtreePhase S H D E header cn cs start C) →
    ∀ keep : (ℕ → ℕ) → Prop,
      (∀ m m', HintSubtreeFrame D node T.nodeCount m m' → keep m → keep m') →
      (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
      HintDecoderPhase S H D E header first (hintTreeEvents (crFamily S) offsets T node seed (offsets node)).length
        (fun m => (HintBitmap m (D.placement.arena node).hints N J ∧ HintNodeFreshTail D node T.nodeCount m) ∧ keep m)
        (fun m => HintBinaryMemory m (D.placement.arena node).result N ∧ keep m) := by
  let sch := H.scheme N X Y
  let CR := crFamily S
  let T := Node.recursive sch t Xs Ys children
  let hT : IsSchemeTree H T := .recursive N X Y t Xs Ys children hc
  let D := hintDecoderTables S H hR W Bc header
  let L := D.placement
  let det := D.det S H up previous header R.N
  let E := (hintSpec R).env W det seedData
  let arena := hintArenaStart D.heap D.stride
  let A := L.arena node
  let word := L.inputWord node
  let offsets := fun i => L.inputWord i * W
  let r := hintKappaAux H R seedData T hT seed
  let blocks := List.ofFn (hintRecursiveColumnEvents CR offsets sch children node seed (offsets node))
  let offset := offsets node + ∑ c, synLen CR (children c)
  dsimp only
  intro hBlock hPlaced hRoot hMem hDet hSlice ih keep hKeep hCursor
  have hAM := hintDecoderTables_placedMemory S H hR hT W Bc header node seed hPlaced hRoot
  have hPay : A.payload = arena node := hAM.payload
  have hALo : arena node ≤ A.transcript := by rw [← hPay]; exact hAM.transcript
  have hALo' : D.listBase ≤ A.transcript := hAM.heap.trans ((Nat.le_add_right _ _).trans hALo)
  have hHead : (schemeNodes R)[seed]? = some T := BlockOf_head hBlock
  have hInfo : L.info node = hintNodeInfo CR hT node seed :=
    HintPlacedSubtree.info S H hR hT W Bc header node seed hPlaced
  have hInfoN : (L.info node).universeSize = N := by rw [hInfo]; rfl
  have hInfoXY : (L.info node).rowParams = some (X, Y) := by rw [hInfo]; rfl
  have hInfoT : (L.info node).residualCapacity = t := by rw [hInfo]; rfl
  have hShape := hintArenaFor_rowOrder S H W (L.info node) (arena node) N X Y t hInfoN hInfoT hInfoXY
  have hTran : A.transcript + sch.ℓ * sch.m ≤ A.hints := by rw [Nat.mul_comm]; exact hShape.1
  have hOwn : A.result ≤ arena (node + 1) :=
    (Nat.le_add_right _ N).trans (hAM.limit.le.trans hAM.own)
  obtain ⟨hCols, hRows, hTail⟩ := hintRecursiveNodeEventSlices CR D offsets sch t Xs Ys children node seed
    (offsets node) first hSlice
  let columns := hintRecursiveFold_total S H D E header node seed first t sch Xs Ys children J keep
    hAM.scratch hAM.list hAM.heap hALo' hALo hTran hAM.result.le hOwn
    (by
      intro col
      let C := children col
      let cn := hintChildPhysicalIndex children node col
      let cs := hintChildSchemeIndex children seed col
      have hp := hPlaced.child col
      have hn : node < cn := by unfold cn hintChildPhysicalIndex; omega
      have hm := hintDecoderTables_placedMemory S H hR (hc col) W Bc header cn cs hp (by intro h; omega)
      let B := L.arena cn
      have hw : L.inputWord cn = B.payload := by
        have h : cn ≠ 0 := by omega
        simp [L, B, HintDecoderPlacement.inputWord, h]
      have hwp : L.inputWord cn + wordsOf W (synLen CR C) ≤ B.transcript := hm.packed
      rw [hw] at hwp
      have h0 : B.hints + C.N < B.result := hm.result
      have h1 : B.result + C.N < B.limit := hm.limit
      have hOut : B.result ≤ B.limit := (Nat.le_add_right _ _).trans h1.le
      exact ⟨hm.payload, hm.transcript.trans (hm.hints.trans ((Nat.le_add_right _ _).trans h0.le)),
        hwp.trans (hm.hints.trans ((Nat.le_add_right _ _).trans (h0.le.trans
          (hOut.trans (hm.own.trans hm.finish)))))⟩)
    hKeep hCursor
    (fun col => hintPlacedColumn_total S H hR seedData up previous W Bc header node seed
      (first + ((blocks.take col.val).flatten).length) N X Y t Xs Ys children hc J col
      hHeader hW hWord hBc hFit hSeed hK hEll hBX hBY hm (hSize col) hSteps (hDims col)
      (hStatic col) (hChildSeed col) hBlock hPlaced hRoot hMem hDet (hCols col))
    (by
      intro col
      let start := first + ((blocks.take col.val).flatten).length
      obtain ⟨_, _, _, hChild, _⟩ := hintRecursiveColumn_slice CR D offsets sch children node seed
        (offsets node) start col (hCols col)
      exact ih col (start + sch.m + 1 + sch.m) hChild)
  obtain ⟨hPerm, hCoeff, _⟩ := hintRowPublic_of_head H R T seedData W det seed N X Y hHead rfl
  have hCoeffSpace : H.rows X Y * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ W :=
    (hintSpec_sizes_of_head R T seed W hHead hFit).2
  have hOffset : offset + (S.data N t).R = word * W + synLen CR T := by
    change word * W + (∑ c, synLen CR (children c)) + (S.data N t).R =
      word * W + ((∑ c, synLen CR (children c)) + (S.data N t).R)
    rw [Nat.add_assoc]
  let tail := hintPlacedRowTail_total S H hR hT seedData up previous W Bc header node seed
    (first + blocks.flatten.length) offset N X Y t r.1 J keep
    hHeader hW hWord hBc hFit hSeed hK hEll hBX hBY hmPos hm hSteps ht hSmall hCR
    hPlaced hInfoN hInfoXY hInfoT hRoot hMem hDet hOffset (fun j q s => hCoeff j s q) hPerm hCoeffSpace
    hRows hTail hKeep hCursor
  have hCount : (hintTreeEvents CR offsets T node seed (offsets node)).length =
      blocks.flatten.length + (sch.m + (1 + sch.N + 1 + 1)) := by
    rw [show T = .recursive sch t Xs Ys children from rfl, hintTreeEvents_recursive]
    simp only [blocks, List.length_append, List.length_map, List.length_range, hintResidualEvents_length]
    omega
  change HintDecoderPhase S H D E header first (hintTreeEvents CR offsets T node seed (offsets node)).length _ _
  rw [hCount]
  exact columns.append tail

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedRecursive_total
end -- Def_LinearSetReconciliation327_Main_HintPlacedBinaryRecursive20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedRecursiveBudget20261120
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearSetReconciliation327.Main

theorem hintPlacedRecursive_total_budget_follows (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (seedData : (hintSpec R).Seed)
    (up previous : ℕ → ℕ) (W Bc header node seed first N X Y t : ℕ)
    (Xs Ys : Fin (H.scheme N X Y).ℓ → ℕ) (children : Fin (H.scheme N X Y).ℓ → Node)
    (hc : ∀ col, IsSchemeTree H (children col))
    (J : Finset ℕ)
    (hHeader : 3 < header) (hW : 0 < W) (hWord : 30 < 2 ^ W) (hBc : Bc + 1 < 2 ^ W)
    (hFit : (hintSpec R).Fits W) (hSeed : seed < 2 ^ W)
    (hK : H.Nmax N X Y < 2 ^ W) (hEll : H.ell N X Y < 2 ^ W)
    (hBX : H.BX N X Y < 2 ^ W) (hBY : H.BY N X Y + 1 < 2 ^ W)
    (hmPos : 0 < H.rows X Y) (hm : H.rows X Y ≤ N) (hSteps : 0 < H.ell N X Y)
    (ht : t ≤ N)
    (hSize : ∀ col, (children col).N = (H.scheme N X Y).m)
    (hDims : ∀ col, UpDimsBound (2 ^ W - 1) (children col))
    (hStatic : ∀ col, UpTreeStatic (crFamily S) Bc (children col).N (children col))
    (hChildSeed : ∀ col, hintChildSchemeIndex children seed col + (schemeNodes (children col)).length < 2 ^ W)
    (hSmall : (S.data N t).W + 1 < W) (hCR : UpCRColumns (crFamily S) Bc N t)
    (U radius : ℕ) (base extra : ℕ) :
    let sch := H.scheme N X Y
    let T := Node.recursive sch t Xs Ys children
    let hT : IsSchemeTree H T := .recursive N X Y t Xs Ys children hc
    let D := hintDecoderTables S H hR W Bc header
    let E := (hintSpec R).env W (D.det S H up previous header R.N) seedData
    let offsets := fun i => D.placement.inputWord i * W
    ∀
      (hBlock : BlockOf R seed (schemeNodes T))
      (hPlaced : HintPlacedSubtree (crFamily S) H D hT node seed)
      (hRoot : (node = 0 → synLen (crFamily S) T ≤ synLen (crFamily S) R))
      (hMem : hintArenaStart D.heap D.stride D.infos.length * W < 2 ^ W)
      (hDet : hintDecoderDetEnd S H D header < 2 ^ W)
      (hSlice : HintEventSlice D first (hintTreeEvents (crFamily S) offsets T node seed (offsets node)))
      (ih : (∀ (col : Fin sch.ℓ) (start : ℕ),
      let C := children col
      let cn := hintChildPhysicalIndex children node col
      let cs := hintChildSchemeIndex children seed col
      HintEventSlice D start (hintTreeEvents (crFamily S) offsets C cn cs (offsets cn)) →
      HintBinarySubtreePhase S H D E header cn cs start C))
      (keep : (ℕ → ℕ) → Prop)
      (hKeep : (∀ m m', HintSubtreeFrame D node T.nodeCount m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (_hCost : HintRowTimeBounds S H N X Y t Bc U radius base extra)
      (_hCopy : ∀ col, 17 * synLen (crFamily S) (children col) + 13 ≤ extra)
      (_hToggle : ∀ col, 147 * (1 + upRest Bc (children col)) + 24 ≤ base)
      (_hXor : 11 * sch.m + 11 ≤ extra)
      (_hKids : ∀ col start hSlice, (ih col start hSlice).BudgetFollows
        (fun e => base + (if e.linearWork then extra else 0))),
      HintBudgetFollows D.events first (hintTreeEvents (crFamily S) offsets T node seed (offsets node)).length (hintPlacedRecursive_total (R := R) S H hR seedData up previous W Bc header node seed first N X Y t Xs Ys children hc J hHeader hW hWord hBc hFit hSeed hK hEll hBX hBY hmPos hm hSteps ht hSize hDims hStatic hChildSeed hSmall hCR hBlock hPlaced hRoot hMem hDet hSlice ih keep hKeep hCursor).budget
        (fun e => base + (if e.linearWork then extra else 0)) := by
  dsimp only
  intro hBlock hPlaced hRoot hMem hDet hSlice ih keep hKeep hCursor hCost hCopy hToggle hXor hKids
  with_unfolding_all simp only [hintPlacedRecursive_total, id, hintAndRec_value]
  apply HintDecoderPhase.cast_budget_follows
  · simp only [hintTreeEvents_recursive, List.length_append, List.length_map, List.length_range, hintResidualEvents_length, TableSpec.env]
    omega
  apply HintDecoderPhase.append_plain_budget_follows
  · apply hintRecursiveFold_total_budget_follows
    · intro col
      apply hintPlacedColumn_total_budget_follows
      · exact hCost
      · exact hCopy col
      · exact hToggle col
      · exact hXor
    · intro col
      with_unfolding_all simp only [id, hintAndRec_value]
      exact hKids col _ _
  · apply hintPlacedRowTail_total_budget_follows
    exact hCost

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedRecursive_total_budget_follows
end -- Def_LinearSetReconciliation327_Main_HintPlacedRecursiveBudget20261120

section -- Def_LinearSetReconciliation327_Main_HintDirectBudget20261120
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LinearSetReconciliation327.Main

theorem hintPlacedDirect_total_budget_follows (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (seedData : (hintSpec R).Seed)
    (up previous : ℕ → ℕ) (W Bc header node seed first N X Y t : ℕ)
    (J : Finset ℕ)
    (hHeader : 3 < header) (hW : 0 < W) (hWord : 30 < 2 ^ W) (hBc : Bc + 1 < 2 ^ W)
    (hFit : (hintSpec R).Fits W) (hSeed : seed < 2 ^ W)
    (hK : H.Nmax N X Y < 2 ^ W) (hEll : H.ell N X Y < 2 ^ W)
    (hBX : H.BX N X Y < 2 ^ W) (hBY : H.BY N X Y + 1 < 2 ^ W)
    (hmPos : 0 < H.rows X Y) (hm : H.rows X Y ≤ N) (hSteps : 0 < H.ell N X Y)
    (ht : t ≤ N)
    (hSmall : (S.data N t).W + 1 < W) (hCR : UpCRColumns (crFamily S) Bc N t)
    (U radius : ℕ) (base extra : ℕ) :
    let sch := H.scheme N X Y
    let T := Node.direct sch t
    let D := hintDecoderTables S H hR W Bc header
    let E := (hintSpec R).env W (D.det S H up previous header R.N) seedData
    let offsets := fun i => D.placement.inputWord i * W
    ∀
      (hBlock : BlockOf R seed (schemeNodes T))
      (hPlaced : HintPlacedSubtree (crFamily S) H D (.direct N X Y t) node seed)
      (hRoot : (node = 0 → synLen (crFamily S) T ≤ synLen (crFamily S) R))
      (hMem : hintArenaStart D.heap D.stride D.infos.length * W < 2 ^ W)
      (hDet : hintDecoderDetEnd S H D header < 2 ^ W)
      (hSlice : HintEventSlice D first (hintTreeEvents (crFamily S) offsets T node seed (offsets node)))
      (keep : (ℕ → ℕ) → Prop)
      (hKeep : (∀ m m', HintSubtreeFrame D node T.nodeCount m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (_hReadCost : 24 ≤ base)
      (_hRowCost : HintRowTimeBounds S H N X Y t Bc U radius base extra),
      HintBudgetFollows D.events first (hintTreeEvents (crFamily S) offsets T node seed (offsets node)).length (hintPlacedDirect_total (R := R) S H hR seedData up previous W Bc header node seed first N X Y t J hHeader hW hWord hBc hFit hSeed hK hEll hBX hBY hmPos hm hSteps ht hSmall hCR hBlock hPlaced hRoot hMem hDet hSlice keep hKeep hCursor).budget
        (fun e => base + (if e.linearWork then extra else 0)) := by
  dsimp only
  intro hBlock hPlaced hRoot hMem hDet hSlice keep hKeep hCursor hReadCost hRowCost
  with_unfolding_all simp only [hintPlacedDirect_total, id, hintAndRec_value]
  apply HintDecoderPhase.cast_budget_follows
  · simp only [hintTreeEvents_direct, hintDirectReads_length, List.length_append, List.length_map,
      List.length_range, hintResidualEvents_length]
    omega
  apply HintDecoderPhase.append_plain_budget_follows
  · apply HintDecoderPhase.relabel_budget_follows
    intro i hi e he
    change 24 ≤ base + (if e.linearWork then extra else 0)
    exact hReadCost.trans (Nat.le_add_right _ _)
  · apply hintPlacedRowTail_total_budget_follows
    exact hRowCost

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedDirect_total_budget_follows
end -- Def_LinearSetReconciliation327_Main_HintDirectBudget20261120

section -- Def_LinearSetReconciliation327_Main_HintNodeResidualPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintNodeResidual_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node first offset Bc t : ℕ)
    (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ) (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hW : 0 < E.W)
    (hControl : D.placement.control = D.control)
    (hInfo : (D.placement.info node).universeSize = sch.N)
    (hx : x ⊆ Finset.range sch.N) (hZ : sch.Z lr x J ≤ t)
    (hN : 1 ≤ sch.N) (ht : t ≤ sch.N) (hWord : 16 < 2 ^ E.W)
    (hSlice : HintEventSlice D first (hintResidualEvents (crFamily S) node offset sch.N t)) :
    let L := D.placement
    let A := L.arena node
    let CR := crFamily S
    let leaf := Node.cr sch.N t
    let data := S.data sch.N t
    let words := wordsOf E.W data.R
    let colBase := hintSubtreeColBase Bc leaf
    let items := hintChildUpdateSchedule CR Bc colBase leaf 0 words
    let table := L.residualTable node
    let spill := A.crRegisters + 16
    let spillSize := 2 ^ (data.W + 1) + 1
    let spillEnd := spill + spillSize + crSourceSteps S sch.N t + 1
    let est := sch.exactEstimate lr x J
    D.control + 2 < A.result →
    A.result + sch.N ≤ A.residual →
    A.residual + words + 2 ≤ A.residualBitmap + 1 →
    A.residualBitmap + sch.N < A.crRegisters →
    spillEnd < 2 ^ E.W →
    HintStagePre E E.W data.R offset A.residual →
    table + 3 < 2 ^ E.W →
    E.det (table + 3) = D.control →
    UpSavedLayout E table items →
    E.det (table % 2 ^ E.W) % 2 ^ E.W = items.length →
    (∀ i < sch.N, UpLocalTree CR (upShiftDetEnv E table) i Bc colBase leaf () 0 0 0) →
    data.W + 1 < E.W →
    L.crTable node + 2 ^ data.W < 2 ^ E.W →
    A.residual * E.W + data.R < 2 ^ E.W →
    (A.residual * E.W + data.R) / E.W < spill →
    (hintCRTableBlock data.W data.det).At E (L.crTable node) →
    (∀ p : Fin D.events.length, hintEventDescriptor header D.events (hintEventRecord S H L) p.val +
      (D.events[p.val]).recordLength < 2 ^ E.W) →
    (∀ m, keep m → ∀ q : Fin data.R, bitAt m E.W 0 (offset + q.val) =
      hintTruth (q.val ∈ CR.sketch sch.N t x)) →
    (∀ m m', CRMemFrame A.result spillEnd m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first (1 + sch.N + 1 + 1)
      (fun m => HintBitmap m A.result sch.N est ∧ HintFreshWords A.residual words m ∧
        HintFreshWords spill spillSize m ∧ keep m)
      (fun m => HintBitmap m A.result sch.N x ∧ keep m) := by
  let L := D.placement
  let A := L.arena node
  let CR := crFamily S
  let leaf := Node.cr sch.N t
  let data := S.data sch.N t
  let words := wordsOf E.W data.R
  let spill := A.crRegisters + 16
  let spillSize := 2 ^ (data.W + 1) + 1
  let spillEnd := spill + spillSize + crSourceSteps S sch.N t + 1
  let est := sch.exactEstimate lr x J
  let fresh := HintFreshWords spill spillSize
  let withSpill := fun m => fresh m ∧ keep m
  dsimp only
  intro hCtrl hRes hBitmap hRegs hSpill hPre hTable hReturn hLayout hCount hLocal hSmall
    hCRSpan hInput hSep hCRTable hDescriptors hBits hFrame hCursor
  change D.control + 2 < A.result at hCtrl
  change A.result + sch.N ≤ A.residual at hRes
  change A.residual + words + 2 ≤ A.residualBitmap + 1 at hBitmap
  change A.residualBitmap + sch.N < A.crRegisters at hRegs
  change spillEnd < 2 ^ E.W at hSpill
  change (∀ m m', CRMemFrame A.result spillEnd m m' → keep m → keep m') at hFrame
  have hSpillEq : spill = A.crRegisters + 16 := rfl
  have hEndEq : spillEnd = spill + spillSize + crSourceSteps S sch.N t + 1 := rfl
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
  have hResToBit : A.result + sch.N ≤ A.residualBitmap := by omega
  have hResFit : A.result < 2 ^ E.W := by omega
  have hBitEnd : A.residualBitmap + sch.N ≤ 2 ^ E.W := by
    exact (hRegs.trans (hSpillEq ▸ Nat.lt_add_of_pos_right (by decide : 0 < 16))).le.trans hSpillFit.le
  have hBitFit : A.residualBitmap < 2 ^ E.W := by omega
  have hCountFit : sch.N < 2 ^ E.W := by omega
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
  have hTailLength : (hintResidualEvents CR node offset sch.N t).length = sch.N + 3 :=
    hintResidualEvents_length CR node offset sch.N t
  have hRead (i : ℕ) (hi : i < sch.N + 3) :
      D.events[first + i]? = (hintResidualEvents CR node offset sch.N t)[i]? :=
    hSlice.read i (by rwa [hTailLength])
  have hCopy : D.events[first]? = some (.residualCopy node offset data.R) := by
    have h := (hRead 0 (by omega)).trans (hintResidualEvents_copy CR node offset sch.N t)
    rw [Nat.add_zero] at h
    exact h
  have hToggles (i : ℕ) (hi : i < sch.N) : D.events[first + 1 + i]? = some (.residualToggle node i) := by
    rw [Nat.add_assoc, hRead _ (by omega)]
    exact hintResidualEvents_toggle CR node offset sch.N t i hi
  have hDecode : D.events[first + 1 + sch.N]? = some (.decodeResidual node sch.N t) := by
    rw [Nat.add_assoc, hRead _ (by omega)]
    exact hintResidualEvents_decode CR node offset sch.N t
  have hCorrect : D.events[first + 1 + sch.N + 1]? = some (.correctEstimate node) := by
    simp only [Nat.add_assoc]
    rw [hRead _ (by omega)]
    exact hintResidualEvents_correct CR node offset sch.N t
  let copy := hintResidualCopy_phase S H D header node first t offset sch lr x J E withSpill hWidth hWord2 hx
    hCopy hCtrl hRes hDest hPre
    (fun p hp => hTagRecord (by rw [hp]; exact hCopy) 3 (by simp [HintTreeEvent.recordLength]))
    (fun m hm => hBits m hm.2)
    (by
      intro m m' hf
      have hf' : CRMemFrame A.residual (A.residual + words) m m' := hf
      exact hSpillFrame m m' (fun a ha => hf' a (by rcases ha with h | h <;> omega)))
    hSpillCursor
  let toggle := hintResidualToggle_phase S H D header node (first + 1) t Bc sch lr x J E withSpill
    hControl hToggles hWord hCountFit.le hCtrl hRes hPayEnd hTable hReturn hLayout hCount hLocal
    (by
      intro p hp hb
      have hPos : p.val = first + 1 + (p.val - (first + 1)) := by omega
      exact hTagRecord (hPos ▸ hToggles _ (by omega)) 3 (by simp [HintTreeEvent.recordLength]))
    hSpillFrame hSpillCursor
  let decode := hintResidualDecode_phase S H D header node (first + 1 + sch.N) t sch lr x J E keep
    hControl hWidth hW hx hZ hN ht hWord11 hDecode hCtrl hRes hResToBit hRegs hSpill hSmall hCRSpan hInput hSep hCRTable
    (fun p hp => hTagRecord (by rw [hp]; exact hDecode) 11 (by simp [HintTreeEvent.recordLength]))
    (by
      intro m m' hf
      have hf' : CRMemFrame A.residualBitmap spillEnd m m' := hf
      exact hFrame m m' (fun a ha => hf' a (by rcases ha with h | h <;> omega)))
    hCursor
  let correct := hintCorrectEstimate_phase S H D header node (first + 1 + sch.N + 1) sch lr x J E keep
    hInfo hCorrect hWord1 hCtrl hResFit hBitFit hCountFit hResToBit hBitEnd
    (fun p hp => hTagRecord (by rw [hp]; exact hCorrect) 2 (by simp [HintTreeEvent.recordLength]))
    (by
      intro m m' hf
      have hf' : CRMemFrame A.result (A.result + sch.N) m m' := hf
      exact hFrame m m' (fun a ha => hf' a (by
        rcases ha with h | h
        · exact Or.inl h
        · exact Or.inr (hResToBit.trans (((Nat.le_add_right _ sch.N).trans (hRegs.le.trans ((Nat.le_add_right _ 16).trans (hSpillLe.trans h))))))))) 
    hCursor
  let updated := copy.append toggle
  let recovered := updated.append_at decode (Nat.add_assoc _ _ _)
  exact recovered.append_at correct (by change first + 1 + sch.N + 1 = first + (1 + sch.N + 1); omega)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintNodeResidual_phase
end -- Def_LinearSetReconciliation327_Main_HintNodeResidualPhase20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedRowTail20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintPlacedRowTail_phase (S : CRSourceBundle) (H : HintParams)
    {R T : Node} (hR : IsSchemeTree H R) (hT : IsSchemeTree H T)
    (seedData : (hintSpec R).Seed) (up previous : ℕ → ℕ)
    (W Bc header node seed first offset N X Y t : ℕ)
    (lr : (H.scheme N X Y).LocalSeed) (r : T.Seed) (x J : Finset ℕ) (keep : (ℕ → ℕ) → Prop)
    (hHeader : 3 < header) (hW : 0 < W) (hWord : 30 < 2 ^ W) (hBc : Bc + 1 < 2 ^ W)
    (hFit : (hintSpec R).Fits W) (hSeed : seed < 2 ^ W)
    (hK : H.Nmax N X Y < 2 ^ W) (hEll : H.ell N X Y < 2 ^ W)
    (hBX : H.BX N X Y < 2 ^ W) (hBY : H.BY N X Y + 1 < 2 ^ W)
    (hmPos : 0 < H.rows X Y) (hm : H.rows X Y ≤ N) (hSteps : 0 < H.ell N X Y)
    (ht : t ≤ N) (hx : x ⊆ Finset.range N) (hZ : (H.scheme N X Y).Z lr x J ≤ t)
    (hSmall : (S.data N t).W + 1 < W) (hCR : UpCRColumns (crFamily S) Bc N t) :
    let D := hintDecoderTables S H hR W Bc header
    let A := D.placement.arena node
    let E := (hintSpec R).env W (D.det S H up previous header R.N) seedData
    let sch := H.scheme N X Y
    let word := D.placement.inputWord node
    let arena := hintArenaStart D.heap D.stride
    let pack := HintMemoryWords W word (hintSketchVector (crFamily S) T r x)
    let ownFresh := fun (mem : ℕ → ℕ) => ∀ a, A.result ≤ a → a < arena (node + 1) → mem a = 0
    HintPlacedSubtree (crFamily S) H D hT node seed →
    (D.placement.info node).universeSize = N → (D.placement.info node).rowParams = some (X, Y) →
    (D.placement.info node).residualCapacity = t →
    (node = 0 → synLen (crFamily S) T ≤ synLen (crFamily S) R) →
    arena D.infos.length * W < 2 ^ W → hintDecoderDetEnd S H D header < 2 ^ W →
    offset + (S.data N t).R = word * W + synLen (crFamily S) T →
    (∀ (j : Fin (H.rows X Y)) (q : Fin (H.Nmax N X Y)) (s : Fin (H.ell N X Y)),
      E.coeff seed (j.val * H.ell N X Y * H.Nmax N X Y + q.val + s.val * H.Nmax N X Y) =
        (lr.2 j s q).val) →
    (∀ i : Fin N, E.permInv seed i.val = (lr.1.symm i).val) →
    H.rows X Y * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ W →
    (∀ q < sch.m, D.events[first + q]? = some (.finishRow node seed q)) →
    HintEventSlice D (first + sch.m) (hintResidualEvents (crFamily S) node offset sch.N t) →
    (∀ m, pack m → ∀ q : Fin (S.data N t).R, bitAt m W 0 (offset + q.val) =
      hintTruth (q.val ∈ (crFamily S).sketch N t x)) →
    (∀ m m', HintSubtreeFrame D node T.nodeCount m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first (sch.m + (1 + sch.N + 1 + 1))
      (fun m => HintBitmap m A.hints N J ∧ HintTranscriptCorrect sch lr x A.transcript (fun _ _ => True) m ∧
        pack m ∧ ownFresh m ∧ keep m)
      (fun m => HintBitmap m A.result N x ∧ keep m) := by
  let D := hintDecoderTables S H hR W Bc header
  let L := D.placement
  let A := L.arena node
  let det := D.det S H up previous header R.N
  let E := (hintSpec R).env W det seedData
  let sch := H.scheme N X Y
  let word := L.inputWord node
  let arena := hintArenaStart D.heap D.stride
  let maxAddr := arena D.infos.length
  let last := arena (node + T.nodeCount)
  let pack := HintMemoryWords W word (hintSketchVector (crFamily S) T r x)
  let ownFresh := fun (mem : ℕ → ℕ) => ∀ a, A.result ≤ a → a < arena (node + 1) → mem a = 0
  let data := S.data N t
  let words := wordsOf W data.R
  let spill := A.crRegisters + 16
  let spillSize := 2 ^ (data.W + 1) + 1
  let tailKeep := fun m => pack m ∧ keep m
  let rowKeep := fun m => HintFreshWords A.residual words m ∧ HintFreshWords spill spillSize m ∧ tailKeep m
  let bitmap := fun m => HintBitmap m A.hints N J
  let transcript := HintTranscriptCorrect sch lr x A.transcript (fun _ _ => True)
  dsimp only
  intro hp hInfoN hInfoXY hInfoT hRoot hMem hDet hOffset hCoeff hPerm hCoeffSpace hRows hSlice hBits hKeep hCursor
  change maxAddr * W < 2 ^ W at hMem
  change hintDecoderDetEnd S H D header < 2 ^ W at hDet
  change offset + data.R = word * W + synLen (crFamily S) T at hOffset
  have hInfo : (L.info node).universeSize = N := hInfoN
  have hMemA := hintDecoderTables_placedMemory S H hR hT W Bc header node seed hp hRoot
  have hSpan : node + T.nodeCount ≤ D.infos.length := hp.span
  have hn : node < D.infos.length := by have := hintNodeCount_pos T; omega
  let i : Fin D.infos.length := ⟨node, hn⟩
  have hLast : last ≤ maxAddr := hintArenaStart_mono D.heap D.stride hSpan
  have hAEnd : A.limit ≤ last := hMemA.own.trans hMemA.finish
  have hAFit : A.limit < 2 ^ W := by
    have hLe : maxAddr ≤ maxAddr * W := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left maxAddr (show 1 ≤ W from hW)
    exact (hAEnd.trans (hLast.trans hLe)).trans_lt hMem
  have hShape := hintArenaFor_rowOrder S H W (L.info node) (arena node) N X Y t hInfoN hInfoT hInfoXY
  change A.transcript + sch.m * sch.ℓ ≤ A.hints ∧ A.hints + N < A.result ∧ A.result + N < A.residual ∧
    A.residual + words + 2 ≤ A.residualBitmap + 1 ∧ A.residualBitmap + N < A.crRegisters ∧
    A.limit = spill + spillSize + crSourceSteps S N t + 1 at hShape
  obtain ⟨hTran, hHint, hRes, hBitmap, hCRReg, hEnd⟩ := hShape
  have hTran' : A.transcript + sch.ℓ * sch.m ≤ A.hints := by rw [Nat.mul_comm]; exact hTran
  have hSpill : A.crRegisters + 16 = spill := rfl
  have hSpillEnd : spill + spillSize ≤ A.limit := by rw [hEnd]; omega
  have hSpillFit : spill + spillSize + crSourceSteps S N t + 1 < 2 ^ W := hEnd ▸ hAFit
  have hSrcSpace : A.transcript ≤ A.result := by omega
  have hN : 1 ≤ N := by omega
  have hRegsSpill : A.crRegisters ≤ spill := hSpill ▸ Nat.le_add_right _ _
  have hResEnd : A.residual + words ≤ A.limit := by
    have h : A.residual + words ≤ A.residualBitmap + 1 :=
      (Nat.le_add_right _ 2).trans hBitmap
    exact h.trans ((Nat.add_le_add_left hN _).trans
      (hCRReg.le.trans (hRegsSpill.trans ((Nat.le_add_right _ _).trans hSpillEnd))))
  have hHeapTran : D.listBase ≤ A.transcript := hMemA.heap.trans
    ((hMemA.payload ▸ Nat.le_add_right _ _ : D.heap ≤ A.payload).trans hMemA.transcript)
  have hCtrl : D.control + 2 < A.transcript := hMemA.scratch.trans_le (hMemA.list.trans hHeapTran)
  have hInfoAt : L.info node = D.infos[i.val] := by
    change D.infos[node]?.getD _ = _
    rw [List.getElem?_eq_getElem hn, Option.getD_some]
  have hWork : hintFinalScratchEnd H L.rowScratch N X Y ≤ D.listBase :=
    hintDecoderTables_rowScratch S H hR W Bc header N X Y sch.ℓ 0 0 (H.Nmax N X Y)
      le_rfl i (hInfoAt ▸ hInfoN) (hInfoAt ▸ hInfoXY)
  have hWorkTran := hWork.trans hHeapTran
  have hWorkFit := (hWorkTran.trans hSrcSpace).trans_lt (by omega : A.result < 2 ^ W)
  obtain ⟨upTable, crTable, thresholds⟩ := hintDecoderTables_rowAux S H hR E up previous W Bc header N X Y t
    hHeader rfl i hInfoN hInfoT hInfoXY
  have hTableEnd : L.residualTable node + hintSubtreeColBase Bc (.cr N t) + upTabLen Bc (.cr N t) < 2 ^ W := by
    have hh := upTable.2.trans_lt hDet
    change L.residualTable node + (hintSubtreeColBase Bc (.cr N t) + upTabLen Bc (.cr N t)) < 2 ^ W at hh
    omega
  have hTable3 : L.residualTable node + 3 < 2 ^ W := by unfold hintSubtreeColBase at hTableEnd; omega
  have hCrSpace : L.crTable node + 2 ^ data.W < 2 ^ W := by
    have hh := crTable.2.trans_lt hDet
    change L.crTable node + (2 ^ data.W + 1) < 2 ^ W at hh
    omega
  have hPackBound : word + wordsOf W (synLen (crFamily S) T) ≤ A.transcript := hMemA.packed
  have hSourceFit : offset + data.R < 2 ^ W := by
    rw [hOffset]
    exact hintWordSpan_lt W _ _ maxAddr hW (hPackBound.trans (hSrcSpace.trans (by omega))) hMem
  have hResidualFit : A.residual * W + data.R < 2 ^ W :=
    hintWordSpan_lt W _ _ maxAddr hW (hResEnd.trans (hAEnd.trans hLast)) hMem
  have hSeparate : (A.residual * W + data.R) / W < spill := by
    rw [Nat.mul_comm A.residual W, Nat.mul_add_div hW]
    have h := Nat.div_le_div_right (c := W) (up_words_cover_budget W data.R hW)
    rw [Nat.mul_comm (wordsOf W data.R), Nat.mul_div_cancel_left _ hW] at h
    change data.R / W ≤ words at h
    omega
  have hStage : HintStagePre E W data.R offset A.residual := by
    refine ⟨by change 1 < 2 ^ W; omega, hW, le_rfl, hSourceFit, by change A.residual + words ≤ 2 ^ W; omega, ?_⟩
    change (offset + data.R) / W < A.residual
    rw [hOffset]
    exact (hMemA.readable hW).trans_le (hSrcSpace.trans ((Nat.le_add_right _ N).trans hRes.le))
  obtain ⟨hLayout, hCount, hReturn, hLocal⟩ := hintResidualTable_placed S H R seedData W det N t Bc
    D.control (L.residualTable node) hW (by omega) hFit (by omega) hCR hBc
    (show words + 1 < 2 ^ W by omega) (show data.R < 2 ^ W by omega) hTableEnd upTable.1
  have hDesc (j : Fin D.events.length) :
      hintEventDescriptor header D.events (hintEventRecord S H L) j.val +
        D.events[j.val].recordLength < 2 ^ W := by
    rw [← hintEventRecord_length S H L]
    exact (hintDecoderEvent_end S H D header j).trans_lt hDet
  have hRowDesc (j : Fin D.events.length) (h0 : first ≤ j.val) (h1 : j.val < first + sch.m) :
      hintEventDescriptor header D.events (hintEventRecord S H L) j.val + 31 ≤ 2 ^ W := by
    have eq : D.events[j.val]? = some (.finishRow node seed (j.val - first)) := by
      nth_rw 1 [show j.val = first + (j.val - first) by omega]
      exact hRows _ (by change j.val - first < sch.m; omega)
    have hj := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) j.isLt).symm.trans eq)
    have hd := hDesc j
    rw [hj] at hd
    exact hd.le
  have hCursorPack (m : ℕ → ℕ) (v : ℕ) (hp : pack m) :
      pack (Function.update m (D.control + 2) v) := by
    intro a ha
    change a < wordsOf W (synLen (crFamily S) T) at ha
    have hc : word + wordsOf W (synLen (crFamily S) T) ≤ D.control + 2 ∨
        D.control + 2 < word := hMemA.outsideCursor
    rw [Function.update_of_ne (by rcases hc with hc | hc <;> omega)]
    exact hp a ha
  have hPackBefore (a : ℕ) (ha : a < wordsOf W (synLen (crFamily S) T)) : word + a < A.result := by omega
  have hOwnFrame (m m' : ℕ → ℕ)
      (hf : ∀ a, (a < L.rowScratch ∨ D.listBase ≤ a) →
        (a < A.result ∨ A.limit ≤ a) → m' a = m a) (hk : keep m) : keep m' := by
    apply hKeep m m' ?_ hk
    intro a hs ho
    have hBase : A.payload = arena node := hMemA.payload
    have hLo : arena node ≤ A.result := by rw [← hBase]; exact hMemA.transcript.trans hSrcSpace
    exact hf a hs (ho.imp (fun h => h.trans_le hLo) (fun h => hAEnd.trans h))
  let rows := hintFinalRows_phase S H D E header N X Y node seed first lr x J rowKeep
    hInfoN hInfoXY rfl hRows hmPos hm hSteps hWord hSeed hK hEll hBX hBY hCoeffSpace hCoeff hPerm
    hMemA.scratch hCtrl hWorkFit hWorkTran hTran' hHint.le
    (show A.result + N ≤ 2 ^ W by omega)
    (fun k => ((thresholds k).2.trans_lt hDet).le) hRowDesc
    (by
      intro m m' hf hk
      have frame : ∀ a, (a < L.rowScratch ∨ hintFinalScratchEnd H L.rowScratch N X Y ≤ a) →
          (a < A.result ∨ A.result + N ≤ a) → m' a = m a := hf
      have hPackedScratch : word + wordsOf W (synLen (crFamily S) T) ≤ L.rowScratch ∨ D.listBase ≤ word :=
        hMemA.outsideScratch
      refine ⟨hk.1.frame (fun q _ => frame _ (Or.inr (by omega)) (Or.inr (by omega))),
        hk.2.1.frame (fun q _ => frame _ (Or.inr (by omega)) (Or.inr (by omega))), ?_, ?_⟩
      · exact hk.2.2.1.frame (fun q hq => frame _
          (hPackedScratch.imp (by omega) (by omega)) (Or.inl (hPackBefore q hq)))
      · exact hOwnFrame m m' (fun a hs ho => frame a (hs.imp id (hWork.trans ·))
          (ho.imp id (by omega))) hk.2.2.2)
    (fun m v h => ⟨h.1.update_below _ _ (by omega), h.2.1.update_below _ _ (by omega),
      hCursorPack m v h.2.2.1, hCursor m v h.2.2.2⟩)
  let residual := hintNodeResidual_phase S H D E header node (first + sch.m) offset Bc t sch lr x J tailKeep
    rfl hW rfl hInfo hx hZ (show 1 ≤ N by omega) ht (by omega : 16 < 2 ^ W) hSlice
    (show D.control + 2 < A.result by omega) hRes.le hBitmap hCRReg hSpillFit hStage
    hTable3 hReturn hLayout hCount hLocal hSmall hCrSpace hResidualFit hSeparate crTable.1 hDesc
    (fun m hk => hBits m hk.1)
    (by
      intro m m' hf hk
      have frame : CRMemFrame A.result A.limit m m' := hEnd ▸ hf
      exact ⟨hk.1.frame (fun q hq => frame _ (Or.inl (hPackBefore q hq))),
        hOwnFrame m m' (fun a _ ha => frame a ha) hk.2⟩)
    (fun m v h => ⟨hCursorPack m v h.1, hCursor m v h.2⟩)
  let complete := rows.append residual
  have hHintsCtrl : D.control + 2 < A.hints := by omega
  have hResultCtrl : D.control + 2 < A.result := by omega
  have hResidualFresh (m : ℕ → ℕ) (hf : ownFresh m) : HintFreshWords A.residual words m := by
    intro q hq
    exact hf (A.residual + q) (by omega) (by
      have he : A.limit ≤ arena (node + 1) := hMemA.own
      omega)
  have hSpillFresh (m : ℕ → ℕ) (hf : ownFresh m) : HintFreshWords spill spillSize m := by
    intro q hq
    exact hf (spill + q) (by omega) (by
      have he : A.limit ≤ arena (node + 1) := hMemA.own
      omega)
  change HintDecoderPhase S H D E header first (sch.m + (1 + sch.N + 1 + 1))
    (fun m => bitmap m ∧ transcript m ∧ pack m ∧ ownFresh m ∧ keep m)
    (fun m => HintBitmap m A.result N x ∧ keep m)
  refine complete.adapt (by omega) ?_ (fun _ h => ⟨h.1, h.2.2⟩) ?_ ?_
  · rintro m ⟨hh, ht, hp, hf, hk⟩
    exact ⟨hh, ht, hResidualFresh m hf, hSpillFresh m hf, hp, hk⟩
  · rintro m v ⟨hh, ht, hp, hf, hk⟩
    refine ⟨hh.update_below _ _ hHintsCtrl, ?_, hCursorPack m v hp, ?_, hCursor m v hk⟩
    · apply ht.frame
      intro j s _
      rw [Function.update_of_ne (by unfold hintTranscriptCell; omega)]
    · intro a ha hb
      change A.result ≤ a at ha
      rw [Function.update_of_ne (Nat.ne_of_gt (hResultCtrl.trans_le ha))]
      exact hf a ha hb
  · rintro m v ⟨hx, hk⟩
    exact ⟨hx.update_below _ _ hResultCtrl, hCursor m v hk⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedRowTail_phase
end -- Def_LinearSetReconciliation327_Main_HintPlacedRowTail20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedRecursive20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintPlacedRecursive_phase (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (seedData : (hintSpec R).Seed)
    (up previous : ℕ → ℕ) (W Bc header node seed first N X Y t : ℕ)
    (Xs Ys : Fin (H.scheme N X Y).ℓ → ℕ) (children : Fin (H.scheme N X Y).ℓ → Node)
    (hc : ∀ col, IsSchemeTree H (children col))
    (x J : Finset ℕ)
    (hHeader : 3 < header) (hW : 0 < W) (hWord : 30 < 2 ^ W) (hBc : Bc + 1 < 2 ^ W)
    (hFit : (hintSpec R).Fits W) (hSeed : seed < 2 ^ W)
    (hK : H.Nmax N X Y < 2 ^ W) (hEll : H.ell N X Y < 2 ^ W)
    (hBX : H.BX N X Y < 2 ^ W) (hBY : H.BY N X Y + 1 < 2 ^ W)
    (hmPos : 0 < H.rows X Y) (hm : H.rows X Y ≤ N) (hSteps : 0 < H.ell N X Y)
    (ht : t ≤ N) (hx : x ⊆ Finset.range N)
    (hSize : ∀ col, (children col).N = (H.scheme N X Y).m)
    (hDims : ∀ col, UpDimsBound (2 ^ W - 1) (children col))
    (hStatic : ∀ col, UpTreeStatic (crFamily S) Bc (children col).N (children col))
    (hChildSeed : ∀ col, hintChildSchemeIndex children seed col + (schemeNodes (children col)).length < 2 ^ W)
    (hSmall : (S.data N t).W + 1 < W) (hCR : UpCRColumns (crFamily S) Bc N t) :
    let sch := H.scheme N X Y
    let T := Node.recursive sch t Xs Ys children
    let hT : IsSchemeTree H T := .recursive N X Y t Xs Ys children hc
    let D := hintDecoderTables S H hR W Bc header
    let E := (hintSpec R).env W (D.det S H up previous header R.N) seedData
    let offsets := fun i => D.placement.inputWord i * W
    let r := hintKappaAux H R seedData T hT seed
    sch.Z r.1 x J ≤ t →
    BlockOf R seed (schemeNodes T) →
    HintPlacedSubtree (crFamily S) H D hT node seed →
    (node = 0 → synLen (crFamily S) T ≤ synLen (crFamily S) R) →
    hintArenaStart D.heap D.stride D.infos.length * W < 2 ^ W →
    hintDecoderDetEnd S H D header < 2 ^ W →
    HintEventSlice D first (hintTreeEvents (crFamily S) offsets T node seed (offsets node)) →
    (∀ (col : Fin sch.ℓ) (start : ℕ),
      let C := children col
      let cn := hintChildPhysicalIndex children node col
      let cs := hintChildSchemeIndex children seed col
      HintEventSlice D start (hintTreeEvents (crFamily S) offsets C cn cs (offsets cn)) →
      HintSubtreePhase S H D E header cn cs start C (r.2 col)
        (sch.exactChildInput r.1 x J col) (sch.exactHint r.1 x J col)) →
    HintSubtreePhase S H D E header node seed first T r x J := by
  let sch := H.scheme N X Y
  let CR := crFamily S
  let T := Node.recursive sch t Xs Ys children
  let hT : IsSchemeTree H T := .recursive N X Y t Xs Ys children hc
  let D := hintDecoderTables S H hR W Bc header
  let L := D.placement
  let det := D.det S H up previous header R.N
  let E := (hintSpec R).env W det seedData
  let arena := hintArenaStart D.heap D.stride
  let A := L.arena node
  let word := L.inputWord node
  let offsets := fun i => L.inputWord i * W
  let r := hintKappaAux H R seedData T hT seed
  let blocks := List.ofFn (hintRecursiveColumnEvents CR offsets sch children node seed (offsets node))
  let offset := offsets node + ∑ c, synLen CR (children c)
  dsimp only
  intro hZ hBlock hPlaced hRoot hMem hDet hSlice ih keep hKeep hCursor
  have hAM := hintDecoderTables_placedMemory S H hR hT W Bc header node seed hPlaced hRoot
  have hPay : A.payload = arena node := hAM.payload
  have hALo : arena node ≤ A.transcript := by rw [← hPay]; exact hAM.transcript
  have hALo' : D.listBase ≤ A.transcript := hAM.heap.trans ((Nat.le_add_right _ _).trans hALo)
  have hHead : (schemeNodes R)[seed]? = some T := BlockOf_head hBlock
  have hInfo : L.info node = hintNodeInfo CR hT node seed :=
    HintPlacedSubtree.info S H hR hT W Bc header node seed hPlaced
  have hInfoN : (L.info node).universeSize = N := by rw [hInfo]; rfl
  have hInfoXY : (L.info node).rowParams = some (X, Y) := by rw [hInfo]; rfl
  have hInfoT : (L.info node).residualCapacity = t := by rw [hInfo]; rfl
  have hShape := hintArenaFor_rowOrder S H W (L.info node) (arena node) N X Y t hInfoN hInfoT hInfoXY
  have hTran : A.transcript + sch.ℓ * sch.m ≤ A.hints := by rw [Nat.mul_comm]; exact hShape.1
  have hOwn : A.result ≤ arena (node + 1) :=
    (Nat.le_add_right _ N).trans (hAM.limit.le.trans hAM.own)
  obtain ⟨hCols, hRows, hTail⟩ := hintRecursiveNodeEventSlices CR D offsets sch t Xs Ys children node seed
    (offsets node) first hSlice
  let columns := hintRecursiveFold_phase S H D E header node seed first t sch Xs Ys children r x J keep
    hAM.scratch hAM.list hAM.heap hALo' hALo hTran hAM.result.le hOwn hAM.packed hAM.outsideScratch hAM.outsideCursor
    (by
      intro col
      let C := children col
      let cn := hintChildPhysicalIndex children node col
      let cs := hintChildSchemeIndex children seed col
      have hp := hPlaced.child col
      have hn : node < cn := by unfold cn hintChildPhysicalIndex; omega
      have hm := hintDecoderTables_placedMemory S H hR (hc col) W Bc header cn cs hp (by intro h; omega)
      let B := L.arena cn
      have hw : L.inputWord cn = B.payload := by
        have h : cn ≠ 0 := by omega
        simp [L, B, HintDecoderPlacement.inputWord, h]
      have hwp : L.inputWord cn + wordsOf W (synLen CR C) ≤ B.transcript := hm.packed
      rw [hw] at hwp
      have h0 : B.hints + C.N < B.result := hm.result
      have h1 : B.result + C.N < B.limit := hm.limit
      have hOut : B.result ≤ B.limit := (Nat.le_add_right _ _).trans h1.le
      exact ⟨hm.payload, hm.transcript.trans (hm.hints.trans ((Nat.le_add_right _ _).trans h0.le)),
        hwp.trans (hm.hints.trans ((Nat.le_add_right _ _).trans (h0.le.trans
          (hOut.trans (hm.own.trans hm.finish)))))⟩)
    hKeep hCursor
    (fun col => hintPlacedColumn_phase S H hR seedData up previous W Bc header node seed
      (first + ((blocks.take col.val).flatten).length) N X Y t Xs Ys children hc x J col
      hHeader hW hWord hBc hFit hSeed hK hEll hBX hBY hm (hSize col) hSteps (hDims col)
      (hStatic col) (hChildSeed col) hBlock hPlaced hRoot hMem hDet (hCols col))
    (by
      intro col
      let start := first + ((blocks.take col.val).flatten).length
      obtain ⟨_, _, _, hChild, _⟩ := hintRecursiveColumn_slice CR D offsets sch children node seed
        (offsets node) start col (hCols col)
      exact ih col (start + sch.m + 1 + sch.m) hChild)
  obtain ⟨hPerm, hCoeff, _⟩ := hintRowPublic_of_head H R T seedData W det seed N X Y hHead rfl
  have hCoeffSpace : H.rows X Y * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ W :=
    (hintSpec_sizes_of_head R T seed W hHead hFit).2
  have hOffset : offset + (S.data N t).R = word * W + synLen CR T := by
    change word * W + (∑ c, synLen CR (children c)) + (S.data N t).R =
      word * W + ((∑ c, synLen CR (children c)) + (S.data N t).R)
    rw [Nat.add_assoc]
  have hBits (m : ℕ → ℕ) (hp : HintMemoryWords W word (hintSketchVector CR T r x) m)
      (q : Fin (S.data N t).R) : bitAt m W 0 (offset + q.val) =
      hintTruth (q.val ∈ CR.sketch N t x) := by
    exact hintRecursivePackedResidual (CR := CR) E m word sch t Xs Ys children r x hW hp q
  let tail := hintPlacedRowTail_phase S H hR hT seedData up previous W Bc header node seed
    (first + blocks.flatten.length) offset N X Y t r.1 r x J keep
    hHeader hW hWord hBc hFit hSeed hK hEll hBX hBY hmPos hm hSteps ht hx hZ hSmall hCR
    hPlaced hInfoN hInfoXY hInfoT hRoot hMem hDet hOffset (fun j q s => hCoeff j s q) hPerm hCoeffSpace
    hRows hTail hBits hKeep hCursor
  have hCount : (hintTreeEvents CR offsets T node seed (offsets node)).length =
      blocks.flatten.length + (sch.m + (1 + sch.N + 1 + 1)) := by
    rw [show T = .recursive sch t Xs Ys children from rfl, hintTreeEvents_recursive]
    simp only [blocks, List.length_append, List.length_map, List.length_range, hintResidualEvents_length]
    omega
  change HintDecoderPhase S H D E header first (hintTreeEvents CR offsets T node seed (offsets node)).length _ _
  rw [hCount]
  exact columns.append tail

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedRecursive_phase
end -- Def_LinearSetReconciliation327_Main_HintPlacedRecursive20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedDirect20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintPlacedDirect_phase (S : CRSourceBundle) (H : HintParams)
    {R : Node} (hR : IsSchemeTree H R) (seedData : (hintSpec R).Seed)
    (up previous : ℕ → ℕ) (W Bc header node seed first N X Y t : ℕ)
    (x J : Finset ℕ)
    (hHeader : 3 < header) (hW : 0 < W) (hWord : 30 < 2 ^ W) (hBc : Bc + 1 < 2 ^ W)
    (hFit : (hintSpec R).Fits W) (hSeed : seed < 2 ^ W)
    (hK : H.Nmax N X Y < 2 ^ W) (hEll : H.ell N X Y < 2 ^ W)
    (hBX : H.BX N X Y < 2 ^ W) (hBY : H.BY N X Y + 1 < 2 ^ W)
    (hmPos : 0 < H.rows X Y) (hm : H.rows X Y ≤ N) (hSteps : 0 < H.ell N X Y)
    (ht : t ≤ N) (hx : x ⊆ Finset.range N)
    (hSmall : (S.data N t).W + 1 < W) (hCR : UpCRColumns (crFamily S) Bc N t) :
    let sch := H.scheme N X Y
    let T := Node.direct sch t
    let D := hintDecoderTables S H hR W Bc header
    let E := (hintSpec R).env W (D.det S H up previous header R.N) seedData
    let offsets := fun i => D.placement.inputWord i * W
    let r := hintKappaAux H R seedData T (.direct N X Y t) seed
    sch.Z r x J ≤ t →
    BlockOf R seed (schemeNodes T) →
    HintPlacedSubtree (crFamily S) H D (.direct N X Y t) node seed →
    (node = 0 → synLen (crFamily S) T ≤ synLen (crFamily S) R) →
    hintArenaStart D.heap D.stride D.infos.length * W < 2 ^ W →
    hintDecoderDetEnd S H D header < 2 ^ W →
    HintEventSlice D first (hintTreeEvents (crFamily S) offsets T node seed (offsets node)) →
    HintSubtreePhase S H D E header node seed first T r x J := by
  let sch := H.scheme N X Y
  let CR := crFamily S
  let T := Node.direct sch t
  let hT : IsSchemeTree H T := .direct N X Y t
  let D := hintDecoderTables S H hR W Bc header
  let L := D.placement
  let det := D.det S H up previous header R.N
  let E := (hintSpec R).env W det seedData
  let arena := hintArenaStart D.heap D.stride
  let maxAddr := arena D.infos.length
  let A := L.arena node
  let word := L.inputWord node
  let offsets := fun i => L.inputWord i * W
  let r := hintKappaAux H R seedData T hT seed
  let readCount := sch.m * sch.ℓ
  let prelude_ := hintDirectReads sch node (word * W)
  let offset := word * W + readCount
  let pack := HintMemoryWords W word (hintSketchVector CR T r x)
  let parentHints := fun m => HintBitmap m A.hints N J
  let transcript := HintTranscriptCorrect sch r x A.transcript (fun _ _ => True)
  let ownFresh := fun (m : ℕ → ℕ) => ∀ a, A.result ≤ a → a < arena (node + 1) → m a = 0
  dsimp only
  intro hZ hBlock hPlaced hRoot hMem hDet hSlice keep hKeep hCursor
  change maxAddr * W < 2 ^ W at hMem
  change hintDecoderDetEnd S H D header < 2 ^ W at hDet
  have hAM := hintDecoderTables_placedMemory S H hR hT W Bc header node seed hPlaced hRoot
  have hSpan : node + 1 ≤ D.infos.length := hPlaced.span
  have hAEnd : A.limit ≤ maxAddr := hAM.own.trans (hintArenaStart_mono D.heap D.stride hSpan)
  have hAFit : A.limit < 2 ^ W := by
    have hLe : maxAddr ≤ maxAddr * W := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left maxAddr (show 1 ≤ W from hW)
    exact (hAEnd.trans hLe).trans_lt hMem
  have hInfo : L.info node = hintNodeInfo CR hT node seed :=
    HintPlacedSubtree.info S H hR hT W Bc header node seed hPlaced
  have hInfoN : (L.info node).universeSize = N := by rw [hInfo]; rfl
  have hInfoXY : (L.info node).rowParams = some (X, Y) := by rw [hInfo]; rfl
  have hInfoT : (L.info node).residualCapacity = t := by rw [hInfo]; rfl
  have hPay : A.payload = arena node := hAM.payload
  have hTranLo : arena node ≤ A.transcript := by rw [← hPay]; exact hAM.transcript
  have hCtrl : D.control + 2 < A.transcript :=
    hAM.scratch.trans_le (hAM.list.trans (hAM.heap.trans ((Nat.le_add_right _ _).trans hTranLo)))
  have hShape := hintArenaFor_rowOrder S H W (L.info node) (arena node) N X Y t hInfoN hInfoT hInfoXY
  have hTran : A.transcript + readCount ≤ A.hints := hShape.1
  have hRes : A.hints + N < A.result := hAM.result
  have hLimit : A.result + N < A.limit := hAM.limit
  have hWordInput : word * W + synLen CR T < 2 ^ W := by
    have hAMEnd : word + wordsOf W (synLen CR T) ≤ A.transcript := hAM.packed
    exact hintWordSpan_lt W _ _ maxAddr hW (hAMEnd.trans (by omega)) hMem
  have hPreLen : prelude_.length = readCount := hintDirectReads_length sch node (word * W)
  have hs : HintEventSlice D first (prelude_ ++ (List.range sch.m).map (HintTreeEvent.finishRow node seed) ++
      hintResidualEvents CR node offset N t) := by
    change HintEventSlice D first (hintTreeEvents CR offsets (.direct sch t) node seed (word * W)) at hSlice
    rw [hintTreeEvents_direct] at hSlice
    exact hSlice
  obtain ⟨hRead, hRows, hTail⟩ := hintNodeEventSlice_rowTail CR sch node seed t first offset prelude_ hs
  rw [hPreLen] at hRows hTail
  have hDesc (pos : Fin D.events.length) :
      hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ W := by
    apply lt_of_le_of_lt (Nat.add_le_add_left ?_ _) ((hintDecoderEvent_end S H D header pos).trans_lt hDet)
    rw [hintEventRecord_length]
    cases D.events[pos.val] <;> simp [HintTreeEvent.recordLength]
  let reads := hintDirectReadAt_phase S H D E header node first word N X Y t r x
    (fun m => parentHints m ∧ ownFresh m ∧ keep m) hInfoXY rfl (show 2 < 2 ^ W by omega) hW hRead
    (show A.transcript + sch.m * sch.ℓ ≤ 2 ^ W by omega) hCtrl hAM.packed (hAM.readable hW)
    hAM.outsideCursor.symm (fun pos _ _ => hDesc pos)
    (by
      intro m m' hf hk
      have frame : CRMemFrame A.transcript (A.transcript + readCount) m m' := hf
      refine ⟨hk.1.frame (fun q _ => frame _ (Or.inr (by omega))), ?_, ?_⟩
      · intro a ha hb
        exact (frame a (Or.inr (by omega))).trans (hk.2.1 a ha hb)
      · apply hKeep m m' ?_ hk.2.2
        intro a _ ha
        change a < arena node ∨ arena (node + 1) ≤ a at ha
        have hi : A.transcript + readCount ≤ arena (node + 1) := by
          have he : A.limit ≤ arena (node + 1) := hAM.own
          omega
        exact frame a (ha.imp (fun h => h.trans_le hTranLo) (fun h => hi.trans h)))
    (fun m v hk => by
      refine ⟨hk.1.update_below _ _ (by omega), ?_, hCursor m v hk.2.2⟩
      intro a ha hb
      rw [Function.update_of_ne (by omega)]
      exact hk.2.1 a ha hb)
    hWordInput.le
  have hHead : (schemeNodes R)[seed]? = some T := BlockOf_head hBlock
  obtain ⟨hPerm, hCoeff, _⟩ := hintRowPublic_of_head H R T seedData W det seed N X Y hHead rfl
  have hCoeffSpace : H.rows X Y * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ W :=
    (hintSpec_sizes_of_head R T seed W hHead hFit).2
  have hOffset : offset + (S.data N t).R = word * W + synLen CR T := by
    change word * W + readCount + (S.data N t).R = word * W + (readCount + (S.data N t).R)
    rw [Nat.add_assoc]
  have hBits (m : ℕ → ℕ) (hp : pack m) (q : Fin (S.data N t).R) :
      bitAt m W 0 (offset + q.val) = hintTruth (q.val ∈ CR.sketch N t x) :=
    hintDirectPackedResidual (CR := CR) E m word sch t r x hW hp q
  let tail := hintPlacedRowTail_phase S H hR hT seedData up previous W Bc header node seed
    (first + readCount) offset N X Y t r r x J keep
    hHeader hW hWord hBc hFit hSeed hK hEll hBX hBY hmPos hm hSteps ht hx hZ hSmall hCR
    hPlaced hInfoN hInfoXY hInfoT hRoot hMem hDet hOffset (fun j q s => hCoeff j s q) hPerm hCoeffSpace
    hRows hTail hBits hKeep hCursor
  have hCount : (hintTreeEvents CR offsets T node seed (offsets node)).length =
      readCount + (sch.m + (1 + sch.N + 1 + 1)) := by
    change (hintTreeEvents CR offsets (.direct sch t) node seed (word * W)).length = _
    rw [hintTreeEvents_direct]
    change (prelude_ ++ (List.range sch.m).map (HintTreeEvent.finishRow node seed) ++
      hintResidualEvents CR node offset sch.N t).length = _
    simp only [List.length_append, List.length_map, List.length_range, hPreLen, hintResidualEvents_length]
    omega
  change HintDecoderPhase S H D E header first (hintTreeEvents CR offsets T node seed (offsets node)).length _ _
  rw [hCount]
  exact (reads.relabel
    (fun m => show (pack m ∧ parentHints m ∧ ownFresh m ∧ keep m) ↔
      (HintSubtreeReady S D W node T r x J m ∧ keep m) by
      change (pack m ∧ parentHints m ∧ ownFresh m ∧ keep m) ↔
        ((pack m ∧ parentHints m ∧ ownFresh m) ∧ keep m)
      tauto)
    (fun m => show (pack m ∧ transcript m ∧ parentHints m ∧ ownFresh m ∧ keep m) ↔
      (parentHints m ∧ transcript m ∧ pack m ∧ ownFresh m ∧ keep m) by tauto)).append tail

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedDirect_phase
end -- Def_LinearSetReconciliation327_Main_HintPlacedDirect20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedTree20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
open HintCanonicalDecode

structure HintRowLimits (S : CRSourceBundle) (H : HintParams) (W Bc N X Y t : ℕ) : Prop where
  keys : H.Nmax N X Y < 2 ^ W
  cols : H.ell N X Y < 2 ^ W
  hx : H.BX N X Y < 2 ^ W
  hy : H.BY N X Y + 1 < 2 ^ W
  rows_pos : 0 < H.rows X Y
  rows_size : H.rows X Y ≤ N
  cols_pos : 0 < H.ell N X Y
  cr : (S.data N t).W + 1 < W
  cr_columns : UpCRColumns (crFamily S) Bc N t

def HintTreeLimits (S : CRSourceBundle) (H : HintParams) (W Bc : ℕ) :
    {T : Node} → IsSchemeTree H T → Prop
  | _, .store _ => True
  | _, .cr N t => (S.data N t).W + 1 < W
  | _, .direct N X Y t => HintRowLimits S H W Bc N X Y t
  | _, .recursive N X Y t _ _ children hc =>
      HintRowLimits S H W Bc N X Y t ∧ ∀ col,
        UpDimsBound (2 ^ W - 1) (children col) ∧
        UpTreeStatic (crFamily S) Bc (children col).N (children col) ∧ HintTreeLimits S H W Bc (hc col)

theorem hintChildSchemeIndex_end {sch : RowScheme} (children : Fin sch.ℓ → Node)
    (Xs Ys : Fin sch.ℓ → ℕ) (t seed : ℕ) (col : Fin sch.ℓ) :
    hintChildSchemeIndex children seed col + (schemeNodes (children col)).length ≤
      seed + (schemeNodes (.recursive sch t Xs Ys children)).length := by
  let counts := List.ofFn fun i => (schemeNodes (children i)).length
  have h := take_sum_add_getElem_le counts col.val (schemeNodes (children col)).length
    (getElem?_ofFn' _ col)
  rw [schemeNodes_recursive, List.length_append, List.length_singleton, flatten_length_eq_sum]
  change seed + 1 + (counts.take col.val).sum + (schemeNodes (children col)).length ≤ seed + (1 + counts.sum)
  omega

theorem hintValid_size {N X Y : ℕ} {x J : Finset ℕ} (h : Node.Valid N X Y x J) :
    x.card ≤ min N (X + Y) := by
  obtain ⟨hx, _, hj, hd⟩ := h
  have hcover : x ⊆ J ∪ (x \ J) := by
    intro i hi
    by_cases hI : i ∈ J
    · exact Finset.mem_union_left _ hI
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi, hI⟩)
  apply le_min
  · simpa using Finset.card_le_card hx
  · exact (Finset.card_le_card hcover).trans
      ((Finset.card_union_le J (x \ J)).trans (Nat.add_le_add hj hd))

theorem hintValid_exactChild (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (s : Fin sch.ℓ) (X Y : ℕ) (hX : sch.U lr x J s ≤ X) (hY : sch.V lr x J s ≤ Y) :
    Node.Valid sch.m X Y (sch.exactChildInput lr x J s) (sch.exactHint lr x J s) := by
  exact ⟨symmDiff_subset_range (column_subset_range sch lr x s) (rowsWhere_subset_range sch _),
    rowsWhere_subset_range sch _, (exactHint_card sch lr x J s).trans_le hX,
    (exactChild_diff_hint_card sch lr x J s).trans_le hY⟩

noncomputable def hintDecodePlacedTree_phase (S : CRSourceBundle) (H : HintParams)
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
    ∀ (node seed first X Y : ℕ) (x J : Finset ℕ),
      let r := hintKappaAux H R seedData T hT seed
      0 < T.N → Node.WF T X Y → Node.Valid T.N X Y x J → Node.AllBounds T r x J →
      BlockOf R seed (schemeNodes T) → seed + (schemeNodes T).length ≤ (schemeNodes R).length →
      HintPlacedSubtree CR H D hT node seed →
      (node = 0 → synLen CR T ≤ synLen CR R) →
      HintEventSlice D first (hintTreeEvents CR offsets T node seed (offsets node)) →
      HintSubtreePhase S H D E header node seed first T r x J := by
  let CR := crFamily S
  let D := hintDecoderTables S H hR W Bc header
  let E := (hintSpec R).env W (D.det S H up previous header R.N) seedData
  let offsets := fun i => D.placement.inputWord i * W
  dsimp only
  intro hMem hDet
  induction hT with
  | store N =>
    intro _ node seed first X Y x J hN hWF hValid hBounds hBlock hSeed hp hRoot hs
    exact hintPlacedStore_phase S H hR E W Bc header node seed first N x J rfl hW
      (by omega) hp hRoot hMem hDet hs
  | cr N t =>
    intro hSmall node seed first X Y x J hN hWF hValid hBounds hBlock hSeed hp hRoot hs
    have hw : t ≤ N ∧ min N (X + Y) ≤ t := hWF
    exact hintPlacedCR_phase S H hR E up previous W Bc header node seed first N t x J hHeader rfl hW
      (by omega) hSmall hN hw.1 hValid.1 ((hintValid_size hValid).trans hw.2) rfl hp hRoot hMem hDet hs
  | direct N X Y t =>
    intro h row seed first Xcap Ycap x J hN hWF hValid hBounds hBlock hSeed hp hRoot hs
    have h : HintRowLimits S H W Bc N X Y t := h
    have hSeed' : seed < 2 ^ W := by omega
    exact hintPlacedDirect_phase S H hR seedData up previous W Bc header row seed first N X Y t x J
      hHeader hW hWord hBc hFit hSeed' h.keys h.cols h.hx h.hy h.rows_pos h.rows_size h.cols_pos
      hWF hValid.1 h.cr h.cr_columns hBounds hBlock hp hRoot hMem hDet hs
  | recursive N X Y t Xs Ys children hc ih =>
    intro h node seed first Xcap Ycap x J hN hWF hValid hBounds hBlock hSeed hp hRoot hs
    let sch := H.scheme N X Y
    let T := Node.recursive sch t Xs Ys children
    let hT : IsSchemeTree H T := .recursive N X Y t Xs Ys children hc
    let r := hintKappaAux H R seedData T hT seed
    change HintRowLimits S H W Bc N X Y t ∧ ∀ c,
      UpDimsBound (2 ^ W - 1) (children c) ∧
      UpTreeStatic CR Bc (children c).N (children c) ∧ HintTreeLimits S H W Bc (hc c) at h
    change t ≤ N ∧ ∀ c, (children c).N = sch.m ∧ Node.WF (children c) (Xs c) (Ys c) at hWF
    change sch.Z r.1 x J ≤ t ∧ ∀ c, sch.U r.1 x J c ≤ Xs c ∧ sch.V r.1 x J c ≤ Ys c ∧
      Node.AllBounds (children c) (r.2 c) (sch.exactChildInput r.1 x J c) (sch.exactHint r.1 x J c) at hBounds
    have hSeed' : seed < 2 ^ W := by omega
    have hKidSeed (col : Fin sch.ℓ) :
        hintChildSchemeIndex children seed col + (schemeNodes (children col)).length ≤ (schemeNodes R).length :=
      (hintChildSchemeIndex_end children Xs Ys t seed col).trans hSeed
    refine hintPlacedRecursive_phase S H hR seedData up previous W Bc header node seed first N X Y t Xs Ys children hc
      x J hHeader hW hWord hBc hFit hSeed' h.1.keys h.1.cols h.1.hx h.1.hy
      h.1.rows_pos h.1.rows_size h.1.cols_pos hWF.1 hValid.1 (fun c => (hWF.2 c).1)
      (fun c => (h.2 c).1) (fun c => (h.2 c).2.1) (fun c => (hKidSeed c).trans_lt hSeeds)
      h.1.cr h.1.cr_columns hBounds.1 hBlock hp hRoot hMem hDet hs ?_
    intro col start
    dsimp only
    intro hChildSlice
    let cn := hintChildPhysicalIndex children node col
    let cs := hintChildSchemeIndex children seed col
    have hCN : 0 < (children col).N := (hWF.2 col).1.symm ▸ h.1.rows_pos
    have hCValid : Node.Valid (children col).N (Xs col) (Ys col)
        (sch.exactChildInput r.1 x J col) (sch.exactHint r.1 x J col) := by
      rw [(hWF.2 col).1]
      exact hintValid_exactChild sch r.1 x J col _ _ (hBounds.2 col).1 (hBounds.2 col).2.1
    have hCBlock : BlockOf R cs (schemeNodes (children col)) := BlockOf_child hBlock col
    have hCPlaced := HintPlacedSubtree.child hp col
    have hNZ : cn ≠ 0 := by unfold cn hintChildPhysicalIndex; omega
    exact ih col (h.2 col).2.2 cn cs start (Xs col) (Ys col) _ _ hCN (hWF.2 col).2 hCValid
      (hBounds.2 col).2.2 hCBlock (hKidSeed col) hCPlaced (fun hz => (hNZ hz).elim) hChildSlice

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecodePlacedTree_phase
end -- Def_LinearSetReconciliation327_Main_HintPlacedTree20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedTreeRoot20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintDecoderLimits (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (W Bc header : ℕ) : Prop where
  anchor : 3 < header
  width : 0 < W
  word : 30 < 2 ^ W
  bc : Bc + 1 < 2 ^ W
  fits : (hintSpec T).Fits W
  seeds : (schemeNodes T).length < 2 ^ W
  memory : let D := hintDecoderTables S H hT W Bc header
    hintArenaStart D.heap D.stride D.infos.length * W < 2 ^ W
  table : hintDecoderDetEnd S H (hintDecoderTables S H hT W Bc header) header < 2 ^ W
  nodes : HintTreeLimits S H W Bc hT

theorem hintDecoderTables_events (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (W Bc header : ℕ) :
    let D := hintDecoderTables S H hT W Bc header
    D.events = hintTreeEvents (crFamily S) (fun i => D.placement.inputWord i * W) T 0 0 0 := by
  dsimp only
  let D := hintDecoderTables S H hT W Bc header
  have hOffsets : (fun i => D.placement.inputWord i * W) =
      (fun i => if i = 0 then 0 else (D.placement.arena i).payload * W) := by
    funext i
    by_cases hi : i = 0 <;> simp [HintDecoderPlacement.inputWord, hi]
  rw [hOffsets]
  rfl

noncomputable def hintPlacedTreeRoot_phase (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (seedData : (hintSpec T).Seed) (up previous : ℕ → ℕ)
    (W Bc header X Y : ℕ) (x J : Finset ℕ) (hLimits : HintDecoderLimits S H hT W Bc header)
    (hN : 0 < T.N) (hWF : Node.WF T X Y) (hValid : Node.Valid T.N X Y x J)
    (hBounds : Node.AllBounds T (hintKappaAux H T seedData T hT 0) x J) :
    let D := hintDecoderTables S H hT W Bc header
    let E := (hintSpec T).env W (D.det S H up previous header T.N) seedData
    let r := hintKappaAux H T seedData T hT 0
    HintDecoderPhase S H D E header 0 D.events.length
      (HintSubtreeReady S D W 0 T r x J)
      (fun m => HintBitmap m (D.placement.arena 0).result T.N x) := by
  let D := hintDecoderTables S H hT W Bc header
  let E := (hintSpec T).env W (D.det S H up previous header T.N) seedData
  let r := hintKappaAux H T seedData T hT 0
  have hs : HintEventSlice D 0 (hintTreeEvents (crFamily S) (fun i => D.placement.inputWord i * W) T 0 0
      (D.placement.inputWord 0 * W)) := by
    rw [show D.placement.inputWord 0 = 0 from rfl, Nat.zero_mul]
    exact HintEventSlice.root S H hT W Bc header
  let p := hintDecodePlacedTree_phase S H hT seedData up previous W Bc header hLimits.anchor hLimits.width
    hLimits.word hLimits.bc hLimits.fits hLimits.seeds T hT hLimits.memory hLimits.table hLimits.nodes
    0 0 0 X Y x J hN hWF hValid hBounds (blockOf_self T) (by simp)
    (HintPlacedSubtree.root S H hT W Bc header) (fun _ => le_rfl) hs
    (fun _ => True) (by simp) (by simp)
  change HintDecoderPhase S H D E header 0 D.events.length _ _
  have he : D.events = hintTreeEvents (crFamily S) (fun i => D.placement.inputWord i * W) T 0 0
      (D.placement.inputWord 0 * W) := by
    rw [show D.placement.inputWord 0 = 0 from rfl, Nat.zero_mul]
    exact hintDecoderTables_events S H hT W Bc header
  rw [he]
  exact p.relabel (fun _ => ⟨And.left, fun h => ⟨h, trivial⟩⟩) (fun _ => ⟨And.left, fun h => ⟨h, trivial⟩⟩)

theorem hintPlacedTree_start_correct (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (seedData : (hintSpec T).Seed) (up previous : ℕ → ℕ)
    (W Bc header X Y : ℕ) (x : Finset ℕ) (J : List ℕ) (hLimits : HintDecoderLimits S H hT W Bc header)
    (hN : 0 < T.N) (hWF : Node.WF T X Y) (hValid : Node.Valid T.N X Y x J.toFinset)
    (hBounds : Node.AllBounds T (hintKappaAux H T seedData T hT 0) x J.toFinset)
    (hDistinct : J.Nodup) (hHints : ∀ j ∈ J, j < T.N) :
    let D := hintDecoderTables S H hT W Bc header
    let E := (hintSpec T).env W (D.det S H up previous header T.N) seedData
    let r := hintKappaAux H T seedData T hT 0
    let y := hintSketchVector (crFamily S) T r x
    let phase := hintPlacedTreeRoot_phase S H hT seedData up previous W Bc header X Y x J.toFinset hLimits
      hN hWF hValid hBounds
    ∃ out, HaltsWithin (hintNativeProgram S) E (hintPhaseRunBudget S D.events.length T.N phase.budget)
      (decoderStart W y J) out ∧ OutputsSupport out (crInput T.N x) := by
  let D := hintDecoderTables S H hT W Bc header
  let A := D.placement.arena 0
  let arena := hintArenaStart D.heap D.stride
  let E := (hintSpec T).env W (D.det S H up previous header T.N) seedData
  let r := hintKappaAux H T seedData T hT 0
  let M := synLen (crFamily S) T
  let y := hintSketchVector (crFamily S) T r x
  let phase := hintPlacedTreeRoot_phase S H hT seedData up previous W Bc header X Y x J.toFinset hLimits
    hN hWF hValid hBounds
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
  exact hintRunPlacedPhase S H D E header T.N up previous y (crInput T.N x) J _ _ phase
    hLimits.anchor rfl (show 15 < 2 ^ W by have := hLimits.word; omega) hLimits.width hLimits.table
    hDistinct hHints hNFit hWords (show wordsOf W M + T.N ≤ A.hints by omega) hSep
    (show A.hints + T.N < 2 ^ W by omega) hBase (show A.result < 2 ^ W by omega)
    (show A.result + T.N ≤ 2 ^ W by omega)
    (by
      intro m hHintsMap hFrame
      have frame (a : ℕ) (ha : a < A.hints ∨ A.hints + T.N < a)
          (h0 : a ≠ D.control) (h1 : a ≠ D.control + 1) : m a = (decoderStart W y J).mem a :=
        hFrame a ha h0 h1
      change HintMemoryWords W 0 y m ∧ HintBitmap m A.hints T.N J.toFinset ∧ HintNodeFreshTail D 0 T.nodeCount m
      refine ⟨?_, hHintsMap, ?_⟩
      · intro q hq
        change q < wordsOf W M at hq
        rw [Nat.zero_add, frame q (Or.inl (by omega)) (by omega) (by omega)]
        exact hintDecoderStart_packed W y J q hq
      · intro a ha _
        change A.result ≤ a at ha
        rw [frame a (Or.inr (by omega)) (by omega) (by omega)]
        exact hintDecoderStart_fresh W y J _ (by change wordsOf W M + J.length ≤ a; omega))
    (fun m hm => by rw [crInput_support T.N x hValid.1]; exact hm)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPlacedTree_start_correct
end -- Def_LinearSetReconciliation327_Main_HintPlacedTreeRoot20261120


