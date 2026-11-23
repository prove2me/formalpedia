-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintPlacedBinaryTree20261120
-- name    : LinearSetReconciliation327_Main_HintPlacedBinaryTree20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-23T08:40:48.820917+00:00
-- url     : https://prove2.me/theorems/2f7cb8ba-591c-47cd-8f3a-7d9ec203b9c1
-- title:
--   LinearSetReconciliation327 鈥?HintPlacedBinaryTree (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintPlacedBinaryTree20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_14
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_15

/-! Bundled module: LinearSetReconciliation327_Main_HintPlacedBinaryTree20261120
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedBinaryTree20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintPlacedBinaryTree20261120
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
end -- Def_LinearSetReconciliation327_Main_HintPlacedBinaryTree20261120


