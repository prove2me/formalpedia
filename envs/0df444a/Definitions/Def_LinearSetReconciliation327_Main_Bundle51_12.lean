-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_12
-- name    : LinearSetReconciliation327_Main_Bundle51_12
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T16:06:53.623799+00:00
-- url     : https://prove2.me/theorems/eb9759c9-617c-4011-b9df-aaf3918c15af
-- title:
--   LinearSetReconciliation327 鈥?Bundle51_12
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_12` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_09
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_10
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_11
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_11a

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_12
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintDirectRootGeometry20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedAuxBounds20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDirectWordBounds20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRecursiveCompose20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintBinaryDirectAt20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPrimitiveBudget20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDecoderStart20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRunPlacedPhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRecursiveColumnSlice20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRecursiveColumnAssemble20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedSubtree20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintSubtreeArena20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintColumnFrames20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintSubtreeFrame20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintUpdateAuxBounds20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintNodeGeometry20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintSubtreeReady20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPhaseEndpoints20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPhaseExists20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintChildTableReady20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPrepareChildPhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRecursiveColumnPhase20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintDirectRootGeometry20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintDirectRoot_arena (S : CRSourceBundle) (H : HintParams) (N X Y t W Bc header : ℕ) :
    let sch := H.scheme N X Y
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    let M := synLen (crFamily S) (.direct sch t)
    let data := S.data N t
    D.placement.arena 0 = hintNodeArena (D.listBase + N) W M 1 sch.m sch.ℓ N data.R data.W (crSourceSteps S N t) :=
  rfl

theorem hintFinalScratchEnd_add (H : HintParams) (start N X Y : ℕ) :
    hintFinalScratchEnd H start N X Y = start + hintFinalScratchEnd H 0 N X Y := by
  simp only [hintFinalScratchEnd, hintRowWorkspace, hintGaussDenseArea, Nat.zero_add, Nat.add_assoc]

theorem hintDirectRoot_scratch (S : CRSourceBundle) (H : HintParams) (N X Y t W Bc header : ℕ) :
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    hintFinalScratchEnd H D.placement.rowScratch N X Y = D.listBase := by
  let D := hintDecoderTables S H (.direct N X Y t) W Bc header
  let I := hintNodeInfo (P := H) (crFamily S) (.direct N X Y t) 0 0
  change hintFinalScratchEnd H D.placement.rowScratch N X Y =
    D.placement.rowScratch + ([hintRowScratchSize H I] : List ℕ).foldl max 0
  rw [hintFinalScratchEnd_add, List.foldl_cons, List.foldl_nil, zero_max]
  rfl

theorem hintDirectRoot_geometry (S : CRSourceBundle) (H : HintParams)
    (N X Y t W Bc header : ℕ) (hW : 0 < W) :
    let sch := H.scheme N X Y
    let D := hintDecoderTables S H (.direct N X Y t) W Bc header
    let A := D.placement.arena 0
    let M := synLen (crFamily S) (.direct sch t)
    let data := S.data N t
    D.placement.control = D.control ∧
    D.control = wordsOf W M + N ∧
    D.control + 2 < D.placement.rowScratch ∧
    D.placement.rowScratch ≤ D.listBase ∧
    D.listBase + N ≤ A.transcript ∧
    M / W < A.transcript ∧
    A.transcript + sch.ℓ * sch.m ≤ A.hints ∧
    A.hints + N < A.result ∧
    A.result + N < A.residual ∧
    A.residual + (wordsOf W data.R + 2) ≤ A.residualBitmap + 1 ∧
    A.residualBitmap + N < A.crRegisters ∧
    A.limit = A.crRegisters + 16 + (2 ^ (data.W + 1) + 1) + crSourceSteps S N t + 1 := by
  let sch := H.scheme N X Y
  let D := hintDecoderTables S H (.direct N X Y t) W Bc header
  let M := synLen (crFamily S) (.direct sch t)
  let data := S.data N t
  let start := D.listBase + N
  have hArena : D.placement.arena 0 =
      hintNodeArena start W M 1 sch.m sch.ℓ N data.R data.W (crSourceSteps S N t) :=
    hintDirectRoot_arena S H N X Y t W Bc header
  have hControl : D.control + 2 < D.placement.rowScratch := by
    change D.control + 2 < D.control + 3
    omega
  have hScratch : D.placement.rowScratch ≤ D.listBase := by
    rw [← hintDirectRoot_scratch S H N X Y t W Bc header, hintFinalScratchEnd_add]
    exact Nat.le_add_right _ _
  have hBefore := hintNodeArena_input_before start W M 1 sch.m sch.ℓ N data.R data.W (crSourceSteps S N t)
    hW 0 (Nat.zero_le _)
  have hBefore' : M / W < (D.placement.arena 0).transcript := by
    rw [hArena]
    simpa only [Nat.zero_mul, Nat.zero_add] using hBefore
  dsimp only
  refine ⟨rfl, rfl, hControl, hScratch, ?_, hBefore', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change start ≤ (D.placement.arena 0).transcript
    rw [hArena]
    simp only [hintNodeArena]
    omega
  · change (D.placement.arena 0).transcript + sch.ℓ * sch.m ≤ (D.placement.arena 0).hints
    rw [hArena]
    simp [hintNodeArena, Nat.mul_comm sch.ℓ sch.m]
  · rw [hArena]
    simp only [hintNodeArena]
    omega
  · rw [hArena]
    simp only [hintNodeArena]
    omega
  · change (D.placement.arena 0).residual + (wordsOf W data.R + 2) ≤
      (D.placement.arena 0).residualBitmap + 1
    rw [hArena]
    simp only [hintNodeArena]
    omega
  · rw [hArena]
    simp only [hintNodeArena]
    omega
  · rw [hArena]
    rfl

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectRoot_geometry
end -- Def_LinearSetReconciliation327_Main_HintDirectRootGeometry20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedAuxBounds20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintDetBlockOffset_end (blocks : List HintDetBlock) (j : Fin blocks.length) :
    hintDetBlockOffset blocks j.val + blocks[j.val].length ≤ (blocks.map HintDetBlock.length).sum := by
  let lengths := blocks.map HintDetBlock.length
  have hj : j.val < lengths.length := by simp [lengths]
  have hLen : lengths[j.val] = blocks[j.val].length := by simp [lengths]
  have h := hintTakeSum_mono lengths (Nat.succ_le_of_lt hj)
  rw [hintTakeSum_succ lengths j.val hj, hLen, List.take_of_length_le le_rfl] at h
  simpa only [lengths, hintDetBlockOffset, ← List.map_take] using h

noncomputable def hintDecoderDetEnd (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header : ℕ) : ℕ :=
  hintEventDescriptor header D.events (hintEventRecord S H D.placement) D.events.length +
    (D.aux.map HintDetBlock.length).sum

theorem hintDecoderEvent_end (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header : ℕ) (j : Fin D.events.length) :
    hintEventDescriptor header D.events (hintEventRecord S H D.placement) j.val +
      (hintEventRecord S H D.placement D.events[j.val]).length ≤ hintDecoderDetEnd S H D header := by
  have h := hintEventDescriptor_end header D.events (hintEventRecord S H D.placement) j
  exact h.trans (Nat.le_add_right _ _)

theorem hintDecoderTables_aux_end (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (W Bc header : ℕ) :
    let D := hintDecoderTables S H hT W Bc header
    ∀ n : Fin D.infos.length, ∀ j : Fin (D.nodeAux S H Bc n.val).length,
      D.auxAddress S H Bc header n.val j.val + (D.nodeAux S H Bc n.val)[j.val].length ≤
        hintDecoderDetEnd S H D header := by
  dsimp only
  let D := hintDecoderTables S H hT W Bc header
  intro n j
  have hAux : D.aux = List.ofFn (fun i : Fin D.infos.length => hintJoinDetBlocks (D.nodeAux S H Bc i.val)) := rfl
  have hLength : D.aux.length = D.infos.length := by rw [hAux, List.length_ofFn]
  let p : Fin D.aux.length := ⟨n.val, hLength.symm ▸ n.isLt⟩
  have hAt : D.aux[p.val] = hintJoinDetBlocks (D.nodeAux S H Bc n.val) := by
    have h := List.getElem_ofFn (f := fun i : Fin D.infos.length => hintJoinDetBlocks (D.nodeAux S H Bc i.val))
      (i := n.val) (by simp only [List.length_ofFn]; exact n.isLt)
    simp only [hAux]
    exact h
  have hInner := hintDetBlockOffset_end (D.nodeAux S H Bc n.val) j
  have hOuter := hintDetBlockOffset_end D.aux p
  rw [hAt] at hOuter
  change hintDetBlockOffset D.aux n.val + ((D.nodeAux S H Bc n.val).map HintDetBlock.length).sum ≤
    (D.aux.map HintDetBlock.length).sum at hOuter
  change D.auxAddress S H Bc header n.val j.val + (D.nodeAux S H Bc n.val)[j.val].length ≤
    hintDecoderDetEnd S H D header
  unfold HintDecoderTables.auxAddress hintAuxAddress hintDecoderDetEnd
  omega

theorem hintDecoderTables_rowAux (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (E : RAMEnv) (up previous : ℕ → ℕ)
    (W Bc header N X Y t : ℕ) (hHeader : 3 < header)
    (hDet : E.det = (hintDecoderTables S H hT W Bc header).det S H up previous header T.N) :
    let D := hintDecoderTables S H hT W Bc header
    let L := D.placement
    let R := (S.data N t).R
    let data := S.data N t
    let update := hintSubtreeBlock (crFamily S) W D.control Bc (.cr N t) 0 (wordsOf W R)
    let cr := hintCRTableBlock data.W data.det
    ∀ node : Fin D.infos.length,
      (L.info node.val).universeSize = N → (L.info node.val).residualCapacity = t →
      (L.info node.val).rowParams = some (X, Y) →
      (update.At E (L.residualTable node.val) ∧
        L.residualTable node.val + update.length ≤ hintDecoderDetEnd S H D header) ∧
      (cr.At E (L.crTable node.val) ∧ L.crTable node.val + cr.length ≤ hintDecoderDetEnd S H D header) ∧
      (∀ j : Fin (H.rows X Y),
        let block := hintWaitDetBlock (H.Nmax N X Y) (rowLen N (H.rows X Y) j.val)
          (H.BY N X Y) (H.ell N X Y) (H.c N X Y)
        block.At E (L.threshold node.val j.val) ∧
          L.threshold node.val j.val + block.length ≤ hintDecoderDetEnd S H D header) := by
  dsimp only
  let D := hintDecoderTables S H hT W Bc header
  let L := D.placement
  let data := S.data N t
  let update := hintSubtreeBlock (crFamily S) W D.control Bc (.cr N t) 0 (wordsOf W data.R)
  let cr := hintCRTableBlock data.W data.det
  let wait := fun j : ℕ => hintWaitDetBlock (H.Nmax N X Y) (rowLen N (H.rows X Y) j)
    (H.BY N X Y) (H.ell N X Y) (H.c N X Y)
  intro node hSize hCapacity hXY
  change (L.info node.val).universeSize = N at hSize
  change (L.info node.val).residualCapacity = t at hCapacity
  change (L.info node.val).rowParams = some (X, Y) at hXY
  have hPair : ((L.info node.val).universeSize, (L.info node.val).residualCapacity) = (N, t) :=
    Prod.ext hSize hCapacity
  have hR := congrArg (fun p : ℕ × ℕ => (S.data p.1 p.2).R) hPair
  have hW := congrArg (fun p : ℕ × ℕ => (S.data p.1 p.2).W) hPair
  have hD := congrArg (fun p : ℕ × ℕ => (S.data p.1 p.2).det) hPair
  dsimp only at hR hW hD
  let head := hintSubtreeBlock (crFamily S) W D.control Bc (L.info node.val).subtree
    (L.info node.val).seedIndex (L.arena node.val).saveOffset
  have hBlocks : D.nodeAux S H Bc node.val =
      head :: update :: cr :: (List.range (H.rows X Y)).map wait := by
    unfold HintDecoderTables.nodeAux
    change (let info := L.info node.val
      let a := L.arena node.val
      hintNodeAuxBlocks S H W D.control Bc info a) = _
    simp [hintNodeAuxBlocks, hSize, hCapacity, hXY, head, update, cr, wait, data, hR, hW, hD]
  have hAt (i : Fin (D.nodeAux S H Bc node.val).length) :
      (D.nodeAux S H Bc node.val)[i.val].At E (D.auxAddress S H Bc header node.val i.val) ∧
        D.auxAddress S H Bc header node.val i.val + (D.nodeAux S H Bc node.val)[i.val].length ≤
          hintDecoderDetEnd S H D header :=
    ⟨hintDecoderTables_aux_At S H hT E up previous W Bc header hHeader hDet node i,
      hintDecoderTables_aux_end S H hT W Bc header node i⟩
  have hAddr (j : ℕ) := hintDecoderTables_aux_addresses S H hT W Bc header node.val j
  refine ⟨?_, ?_, ?_⟩
  · let i : Fin (D.nodeAux S H Bc node.val).length := ⟨1, by rw [hBlocks]; simp⟩
    have hIt : (D.nodeAux S H Bc node.val)[i.val] = update := by simp only [hBlocks, i] <;> rfl
    have h := hAt i
    rw [hIt] at h
    rw [(hAddr 0).2.1]
    exact h
  · let i : Fin (D.nodeAux S H Bc node.val).length := ⟨2, by rw [hBlocks]; simp⟩
    have hIt : (D.nodeAux S H Bc node.val)[i.val] = cr := by simp only [hBlocks, i] <;> rfl
    have h := hAt i
    rw [hIt] at h
    rw [(hAddr 0).2.2.1]
    exact h
  · intro j
    let i : Fin (D.nodeAux S H Bc node.val).length := ⟨3 + j.val, by rw [hBlocks]; simp; omega⟩
    have hIt : (D.nodeAux S H Bc node.val)[i.val] = wait j.val := by
      have hi : i.val = j.val + 1 + 1 + 1 := by dsimp only [i]; omega
      simp only [hBlocks, hi, List.getElem_cons_succ, List.getElem_map, List.getElem_range]
    have h := hAt i
    rw [hIt] at h
    rw [(hAddr j.val).2.2.2]
    exact h

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_aux_end
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_rowAux
end -- Def_LinearSetReconciliation327_Main_HintPlacedAuxBounds20261120

section -- Def_LinearSetReconciliation327_Main_HintDirectWordBounds20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintDirectWordBounds (S : CRSourceBundle) (H : HintParams)
    (N X Y t W Bc header : ℕ) : Prop where
  word : 30 < 2 ^ W
  bc : Bc + 1 < 2 ^ W
  keys : H.Nmax N X Y < 2 ^ W
  cols : H.ell N X Y < 2 ^ W
  hx : H.BX N X Y < 2 ^ W
  hy : H.BY N X Y + 1 < 2 ^ W
  coeff : H.rows X Y * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ W
  cr : (S.data N t).W + 1 < W
  input : synLen (crFamily S) (.direct (H.scheme N X Y) t) < 2 ^ W
  det : hintDecoderDetEnd S H (hintDecoderTables S H (.direct N X Y t) W Bc header) header < 2 ^ W
  mem : ((hintDecoderTables S H (.direct N X Y t) W Bc header).placement.arena 0).limit < 2 ^ W
  residual : ((hintDecoderTables S H (.direct N X Y t) W Bc header).placement.arena 0).residual * W +
    (S.data N t).R < 2 ^ W

noncomputable def HintDecoderPhase.append_at {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header first second n m : ℕ} {A B C : (ℕ → ℕ) → Prop}
    (p : HintDecoderPhase S H D E header first n A B)
    (q : HintDecoderPhase S H D E header second m B C)
    (h : second = first + n) :
    HintDecoderPhase S H D E header first (n + m) A C :=
  p.append (h ▸ q)

end LinearSetReconciliation327.Main
end -- Def_LinearSetReconciliation327_Main_HintDirectWordBounds20261120

section -- Def_LinearSetReconciliation327_Main_HintRecursiveCompose20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintEventSlice (D : HintDecoderTables) (first : ℕ) (events : List HintTreeEvent) : Prop :=
  ∃ before after : List HintTreeEvent, before.length = first ∧ D.events = before ++ events ++ after

theorem HintEventSlice.read {D : HintDecoderTables} {first : ℕ} {events : List HintTreeEvent}
    (h : HintEventSlice D first events) (i : ℕ) (hi : i < events.length) :
    D.events[first + i]? = events[i]? := by
  obtain ⟨before, after, hFirst, hEvents⟩ := h
  rw [← hFirst, hEvents, List.append_assoc]
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact List.getElem?_append_left hi

theorem HintEventSlice.left {D : HintDecoderTables} {first : ℕ} {a b : List HintTreeEvent}
    (h : HintEventSlice D first (a ++ b)) : HintEventSlice D first a := by
  obtain ⟨before, after, hLen, hList⟩ := h
  exact ⟨before, b ++ after, hLen, by simpa only [List.append_assoc] using hList⟩

theorem HintEventSlice.right {D : HintDecoderTables} {first : ℕ} {a b : List HintTreeEvent}
    (h : HintEventSlice D first (a ++ b)) : HintEventSlice D (first + a.length) b := by
  obtain ⟨before, after, hLen, hList⟩ := h
  exact ⟨before ++ a, after, by rw [List.length_append, hLen],
    by simpa only [List.append_assoc] using hList⟩

theorem HintEventSlice.flatten {D : HintDecoderTables} {first : ℕ} {blocks : List (List HintTreeEvent)}
    (h : HintEventSlice D first blocks.flatten) (j : ℕ) (hj : j < blocks.length) :
    HintEventSlice D (first + (blocks.take j).flatten.length) blocks[j] := by
  induction blocks generalizing first j with
  | nil => simp at hj
  | cons block blocks ih =>
    cases j with
    | zero =>
      simpa only [List.take_zero, List.flatten_nil, List.length_nil, Nat.add_zero, List.getElem_cons_zero]
        using h.left
    | succ j =>
      have hj' : j < blocks.length := Nat.lt_of_succ_lt_succ hj
      simpa only [List.take_succ_cons, List.flatten_cons, List.length_append, Nat.add_assoc,
        List.getElem_cons_succ] using ih h.right j hj'

def hintPhasePrefixCount (size : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => hintPhasePrefixCount size i + size i

theorem hintFlattenTake_length_succ {α : Type} (blocks : List (List α)) (i : ℕ)
    (hi : i < blocks.length) :
    ((blocks.take (i + 1)).flatten).length = ((blocks.take i).flatten).length + blocks[i].length := by
  induction blocks generalizing i with
  | nil => simp at hi
  | cons block blocks ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.take_succ_cons, List.flatten_cons, List.length_append, List.getElem_cons_succ]
      rw [ih i (Nat.lt_of_succ_lt_succ hi), Nat.add_assoc]

theorem hintPhasePrefixCount_ofFn {m : ℕ} (events : Fin m → List HintTreeEvent)
    (size : ℕ → ℕ) (hSize : ∀ i : Fin m, size i.val = (events i).length) :
    ∀ j ≤ m, hintPhasePrefixCount size j = ((List.ofFn events).take j).flatten.length := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    let i : Fin m := ⟨j, by omega⟩
    have hj' : j < (List.ofFn events).length := by rw [List.length_ofFn]; omega
    rw [hintPhasePrefixCount, ih (by omega), hSize i, hintFlattenTake_length_succ _ _ hj']
    rw [List.getElem_ofFn]

noncomputable def HintDecoderPhase.empty {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header first : ℕ}
    (inv : (ℕ → ℕ) → Prop)
    (cursor : ∀ m v, inv m → inv (Function.update m (D.control + 2) v)) :
    HintDecoderPhase S H D E header first 0 inv inv :=
  ⟨fun _ => 0, fun _ => inv, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => cursor,
    fun i hi => (Nat.not_lt_zero i hi).elim⟩

noncomputable def HintDecoderPhase.concat {S : CRSourceBundle} {H : HintParams}
    {D : HintDecoderTables} {E : RAMEnv} {header first m : ℕ}
    (size : ℕ → ℕ) (inv : ℕ → (ℕ → ℕ) → Prop)
    (start : ∀ mem v, inv 0 mem → inv 0 (Function.update mem (D.control + 2) v))
    (phase : ∀ i < m, HintDecoderPhase S H D E header (first + hintPhasePrefixCount size i)
      (size i) (inv i) (inv (i + 1))) :
    HintDecoderPhase S H D E header first (hintPhasePrefixCount size m) (inv 0) (inv m) := by
  induction m with
  | zero => exact HintDecoderPhase.empty (inv 0) start
  | succ m ih =>
    exact (ih (fun i hi => phase i (Nat.lt_succ_of_lt hi))).append (phase m (Nat.lt_succ_self m))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintEventSlice.flatten
#print axioms LinearSetReconciliation327.Main.hintPhasePrefixCount_ofFn
#print axioms LinearSetReconciliation327.Main.HintDecoderPhase.concat
end -- Def_LinearSetReconciliation327_Main_HintRecursiveCompose20261120

section -- Def_LinearSetReconciliation327_Main_HintBinaryDirectAt20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintDirectReadAt_total (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node first word N X Y t : ℕ)
    (keep : (ℕ → ℕ) → Prop)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hWidth : E.W = D.placement.width) (hWord : 2 < 2 ^ E.W) (hW : 0 < E.W)
    (hSlice : HintEventSlice D first (hintDirectReads (H.scheme N X Y) node (word * E.W))) :
    let sch := H.scheme N X Y
    let A := D.placement.arena node
    let M := synLen (crFamily S) (.direct sch t)
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
      keep
      (fun m => HintTranscriptBinary sch A.transcript sch.ℓ m ∧ keep m) := by
  let sch := H.scheme N X Y
  let CR := crFamily S
  let A := D.placement.arena node
  let M := synLen CR (.direct sch t)
  let inv := fun i m =>
    (∀ (j : Fin sch.m) (s : Fin sch.ℓ), j.val * sch.ℓ + s.val < i →
      m (hintTranscriptCell A.transcript sch.m j.val s.val) < 2) ∧ keep m
  dsimp only
  intro hFit hControlHigh _ hInputBefore _ hDescriptors hKeep hKeepCursor hInput
  change D.control + 2 < A.transcript at hControlHigh
  refine ⟨fun _ => 24, inv, ?_, ?_, ?_, ?_⟩
  · intro m
    exact ⟨And.right, fun h => ⟨fun j s h => (Nat.not_lt_zero _ h).elim, h⟩⟩
  · intro m
    exact ⟨fun h => ⟨fun j s _ => h.1 j s (hintPairOffset_lt j s), h.2⟩,
      fun h => ⟨fun j s _ => h.1 j s s.isLt, h.2⟩⟩
  · intro i m v hm
    rcases hm with ⟨hT, hK⟩
    refine ⟨?_, hKeepCursor m v hK⟩
    intro j s hs
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
    obtain ⟨hT, hK⟩ := hInv
    let desc := hintEventDescriptor header D.events (hintEventRecord S H D.placement) j.val
    have hTable (row col offset : ℕ) (h : D.events[j.val] = .directBit node row col offset) :
        (hintDirectBitBlock E.W A.transcript sch.m row col offset).At E desc := by
      rw [h] at hRecord
      simp only [hintEventRecord, hInfoXY, Option.getD_some] at hRecord
      rw [hWidth]
      exact hRecord
    let dest := hintTranscriptCell A.transcript sch.m row.val col.val
    let offset := word * E.W + row.val * sch.ℓ + col.val
    have hPre := hintDirectBit_pre (CR := CR) E sch t word A.transcript row col hW hWord hInput hInputBefore hFit
    have hSlot := HintUnpackTable.of_block E desc dest offset 1 (hTable _ _ _ hEq)
      hWord (hDescriptors j (by omega) (by omega)) (Nat.lt_of_succ_le hPre.destination)
      (Nat.lt_of_succ_le hPre.offset_span) hPre.count_fit
    have hRun := hintUnpackAction_sem (hintNativeProgram S) E state desc dest offset 1 base
      hSlot hArg hPre hAt hPc
    change Sem (hintNativeProgram S) E base (base + 22) state _
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hb, hf⟩
    have hCell := hintPairOffset_lt col row
    rw [Nat.mul_comm sch.ℓ sch.m] at hCell
    have hFrame : CRMemFrame A.transcript (A.transcript + sch.m * sch.ℓ) state.mem out.mem := by
      intro a ha
      apply hf
      unfold dest hintTranscriptCell
      rcases ha with h | h <;> omega
    refine ⟨by simpa using hk, ⟨?_, hKeep _ _ hFrame hK⟩, hc.trans hCtx, ?_⟩
    · intro row' col' hRead
      by_cases h : hintTranscriptCell A.transcript sch.m row'.val col'.val = dest
      · rw [h, ← Nat.add_zero dest, hb 0 (by decide)]
        unfold bitAt
        exact Nat.mod_lt _ (by decide)
      · rw [hf _ (by omega)]
        apply hT row' col'
        have hIndex : i = row.val * sch.ℓ + col.val := hRC
        have hNe : row'.val * sch.ℓ + col'.val ≠ i := by
          intro hEqIndex
          have hSwap : hintTranscriptCell 0 sch.ℓ col'.val row'.val =
              hintTranscriptCell 0 sch.ℓ col.val row.val := by
            simpa only [hintTranscriptCell, Nat.zero_add, ← hIndex] using hEqIndex
          obtain ⟨hc', hr'⟩ := (hintTranscriptCell_eq_iff 0 col' col row' row).mp hSwap
          subst col'
          subst row'
          exact h rfl
        omega
    · intro a _ ha
      exact hFrame a (Or.inl (ha.trans_lt hControlHigh))

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDirectReadAt_total
end -- Def_LinearSetReconciliation327_Main_HintBinaryDirectAt20261120

section -- Def_LinearSetReconciliation327_Main_HintPrimitiveBudget20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintChildCopy_total_budget (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node childNode first word : ℕ) (sch : RowScheme) (t : ℕ)
    (Xs Ys : Fin sch.ℓ → ℕ) (children : Fin sch.ℓ → Node)
    (col : Fin sch.ℓ)
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
    ∀
      (hEvent : D.events[first]? = some (.childCopy node col.val childNode offset count))
      (hControl : D.control + 2 < dest)
      (hAddress : dest < 2 ^ E.W)
      (hInput : word * E.W + synLen CR (.recursive sch t Xs Ys children) < 2 ^ E.W)
      (hDest : dest + words ≤ 2 ^ E.W)
      (hSeparate : (word * E.W + synLen CR (.recursive sch t Xs Ys children)) / E.W < dest)
      (hDescriptor : (∀ pos : Fin D.events.length, pos.val = first →
          hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame dest (dest + words) m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (i : ℕ),
      (hintChildCopy_total S H D E header node childNode first word sch t Xs Ys children col keep hWidth hWord hW
        hEvent hControl hAddress hInput hDest hSeparate hDescriptor hKeep hCursor).budget i = 17 * count + 13 := by
  intros
  rfl

theorem hintChildToggle_total_budget (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node child seed col first X Y Bc workStart sav : ℕ)
    (T : Node) (r : T.Seed)
    (keep : (ℕ → ℕ) → Prop)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
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
    ∀
      (hCtrl : D.control + 2 < gate)
      (hBefore : gate + T.N ≤ dest)
      (hPay : dest + (sav + 2) ≤ 2 ^ E.W)
      (hGap : words ≤ workStart)
      (hRoom : UpSaveRoom workStart sav T)
      (hDet : detBase + 3 < 2 ^ E.W)
      (hReturn : E.det (detBase + 3) = D.control)
      (hLayout : UpSavedLayout E detBase items)
      (hCount : E.det (detBase % 2 ^ E.W) % 2 ^ E.W = items.length)
      (hLocal : (∀ i < T.N, UpLocalTree CR (upShiftDetEnv E detBase) i Bc colBase T r seed 0 0))
      (hDescriptor : (∀ p : Fin D.events.length, first ≤ p.val → p.val < first + T.N →
          hintEventDescriptor header D.events (hintEventRecord S H L) p.val + 3 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame dest (dest + sav + 2) m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (i : ℕ),
      (hintChildToggle_total S H D E header node child seed col first X Y Bc workStart sav T r keep hInfoXY hEvent hWord hSize
        hCtrl hBefore hPay hGap hRoom hDet hReturn hLayout hCount hLocal hDescriptor hKeep hCursor).budget i = 147 * items.length + 24 := by
  intros
  rfl

theorem hintRecoverColumn_total_budget (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node child first N X Y : ℕ)
    (col : Fin (H.scheme N X Y).ℓ) (keep : (ℕ → ℕ) → Prop)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hEvent : D.events[first]? = some (.recoverColumn node col.val child)) :
    let L := D.placement
    let sch := H.scheme N X Y
    let transcript := (L.arena node).transcript
    let dest := transcript + col.val * sch.m
    let source := (L.arena child).result
    ∀
      (hWord : 1 < 2 ^ E.W)
      (hCtrl : D.control + 2 < transcript)
      (hCtrlSrc : D.control + 2 < source)
      (hDest : dest < 2 ^ E.W)
      (hSource : source < 2 ^ E.W)
      (hSize : sch.m < 2 ^ E.W)
      (hDestEnd : dest + sch.m ≤ 2 ^ E.W)
      (hSourceEnd : source + sch.m ≤ 2 ^ E.W)
      (hSep : (dest + sch.m ≤ source ∨ source + sch.m ≤ dest))
      (hDescriptor : (∀ pos : Fin D.events.length, pos.val = first →
          hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 2 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame dest (dest + sch.m) m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (i : ℕ),
      (hintRecoverColumn_total S H D E header node child first N X Y col keep hInfoXY hEvent
        hWord hCtrl hCtrlSrc hDest hSource hSize hDestEnd hSourceEnd hSep hDescriptor hKeep hCursor).budget i = 11 * sch.m + 11 := by
  intros
  rfl

theorem hintResidualCopy_total_budget (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first t offset : ℕ) (N : ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hWidth : E.W = D.placement.width) (hWord : 2 < 2 ^ E.W)
    (hEvent : D.events[first]? = some (.residualCopy node offset (S.data N t).R)) :
    let L := D.placement
    let A := L.arena node
    let count := (S.data N t).R
    let words := wordsOf E.W count
    ∀
      (hControl : D.control + 2 < A.result)
      (hSeparate : A.result + N ≤ A.residual)
      (hAddress : A.residual < 2 ^ E.W)
      (hPre : HintStagePre E E.W count offset A.residual)
      (hDescriptor : (∀ pos : Fin D.events.length, pos.val = first →
          hintEventDescriptor header D.events (hintEventRecord S H L) pos.val + 3 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame A.residual (A.residual + words) m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (i : ℕ),
      (hintResidualCopy_total S H D header node first t offset N E keep hWidth hWord hEvent
        hControl hSeparate hAddress hPre hDescriptor hKeep hCursor).budget i = 17 * count + 13 := by
  intros
  rfl

theorem hintResidualToggle_total_budget (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first t Bc : ℕ) (N : ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hControl : D.placement.control = D.control)
    (hEvent : ∀ q < N, D.events[first + q]? = some (.residualToggle node q))
    (hWord : 16 < 2 ^ E.W) (hSize : N ≤ 2 ^ E.W) :
    let L := D.placement
    let A := L.arena node
    let CR := crFamily S
    let leaf := Node.cr N t
    let words := wordsOf E.W (synLen CR leaf)
    let colBase := hintSubtreeColBase Bc leaf
    let items := hintChildUpdateSchedule CR Bc colBase leaf 0 words
    let detBase := L.residualTable node
    ∀
      (hCtrl : D.control + 2 < A.result)
      (hBefore : A.result + N ≤ A.residual)
      (hPay : A.residual + (words + 2) ≤ 2 ^ E.W)
      (hDet : detBase + 3 < 2 ^ E.W)
      (hReturn : E.det (detBase + 3) = D.control)
      (hLayout : UpSavedLayout E detBase items)
      (hCount : E.det (detBase % 2 ^ E.W) % 2 ^ E.W = items.length)
      (hLocal : (∀ i < N, UpLocalTree CR (upShiftDetEnv E detBase) i Bc colBase leaf () 0 0 0))
      (hDescriptor : (∀ p : Fin D.events.length, first ≤ p.val → p.val < first + N →
          hintEventDescriptor header D.events (hintEventRecord S H L) p.val + 3 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame A.residual (A.residual + words + 2) m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (i : ℕ),
      (hintResidualToggle_total S H D header node first t Bc N E keep hControl hEvent hWord hSize
        hCtrl hBefore hPay hDet hReturn hLayout hCount hLocal hDescriptor hKeep hCursor).budget i = 147 * items.length + 24 := by
  intros
  rfl

theorem hintResidualDecode_total_budget (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
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
    ∀
      (hCtrl : D.control + 2 < A.result)
      (hPayload : A.result + N ≤ A.residual)
      (hBefore : A.result + N ≤ A.residualBitmap)
      (hOut : A.residualBitmap + N < A.crRegisters)
      (hEnd : spillEnd < 2 ^ E.W)
      (hSM : w + 1 < E.W)
      (hTable : L.crTable node + 2 ^ w < 2 ^ E.W)
      (hIn : A.residual * E.W + (S.data N t).R < 2 ^ E.W)
      (hInSep : (A.residual * E.W + (S.data N t).R) / E.W < spill)
      (hCRTable : (hintCRTableBlock w (S.data N t).det).At E (L.crTable node))
      (hDesc : (∀ p : Fin D.events.length, p.val = first →
          hintEventDescriptor header D.events (hintEventRecord S H L) p.val + 11 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame A.residualBitmap spillEnd m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (i : ℕ),
      (hintResidualDecode_total S H D header node first t N E keep hControl hWidth hW hN ht hWord hEvent
        hCtrl hPayload hBefore hOut hEnd hSM hTable hIn hInSep hCRTable hDesc hKeep hCursor).budget i = hintCRNodeBudget S N t := by
  intros
  rfl

theorem hintCorrectEstimate_total_budget (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first : ℕ) (N : ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hInfo : (D.placement.info node).universeSize = N)
    (hEvent : D.events[first]? = some (.correctEstimate node)) :
    let A := D.placement.arena node
    ∀
      (hWord : 1 < 2 ^ E.W)
      (hCtrl : D.control + 2 < A.result)
      (hDest : A.result < 2 ^ E.W)
      (hSource : A.residualBitmap < 2 ^ E.W)
      (hSize : N < 2 ^ E.W)
      (hSep : A.result + N ≤ A.residualBitmap)
      (hEnd : A.residualBitmap + N ≤ 2 ^ E.W)
      (hDescriptor : (∀ p : Fin D.events.length, p.val = first →
          hintEventDescriptor header D.events (hintEventRecord S H D.placement) p.val + 2 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame A.result (A.result + N) m m' → keep m → keep m'))
      (hCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (i : ℕ),
      (hintCorrectEstimate_total S H D header node first N E keep hInfo hEvent
        hWord hCtrl hDest hSource hSize hSep hEnd hDescriptor hKeep hCursor).budget i = 11 * N + 11 := by
  intros
  rfl

theorem hintDirectReadAt_total_budget (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header node first word N X Y t : ℕ)
    (keep : (ℕ → ℕ) → Prop)
    (hInfoXY : (D.placement.info node).rowParams = some (X, Y))
    (hWidth : E.W = D.placement.width) (hWord : 2 < 2 ^ E.W) (hW : 0 < E.W)
    (hSlice : HintEventSlice D first (hintDirectReads (H.scheme N X Y) node (word * E.W))) :
    let sch := H.scheme N X Y
    let A := D.placement.arena node
    let M := synLen (crFamily S) (.direct sch t)
    ∀
      (hFit : A.transcript + sch.m * sch.ℓ ≤ 2 ^ E.W)
      (hControlHigh : D.control + 2 < A.transcript)
      (hSep : word + wordsOf E.W M ≤ A.transcript)
      (hInputBefore : (word * E.W + M) / E.W < A.transcript)
      (hControlOutside : (D.control + 2 < word ∨ word + wordsOf E.W M ≤ D.control + 2))
      (hDescriptors : (∀ pos : Fin D.events.length, first ≤ pos.val → pos.val < first + sch.m * sch.ℓ →
          hintEventDescriptor header D.events (hintEventRecord S H D.placement) pos.val + 3 < 2 ^ E.W))
      (hKeep : (∀ m m', CRMemFrame A.transcript (A.transcript + sch.m * sch.ℓ) m m' → keep m → keep m'))
      (hKeepCursor : (∀ m v, keep m → keep (Function.update m (D.control + 2) v)))
      (hInput : word * E.W + M ≤ 2 ^ E.W)
      (i : ℕ),
      (hintDirectReadAt_total S H D E header node first word N X Y t keep hInfoXY hWidth hWord hW hSlice
        hFit hControlHigh hSep hInputBefore hControlOutside hDescriptors hKeep hKeepCursor hInput).budget i = 24 := by
  intros
  rfl

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintChildToggle_total_budget
#print axioms LinearSetReconciliation327.Main.hintResidualDecode_total_budget
#print axioms LinearSetReconciliation327.Main.hintDirectReadAt_total_budget
end -- Def_LinearSetReconciliation327_Main_HintPrimitiveBudget20261120

section -- Def_LinearSetReconciliation327_Main_HintDecoderStart20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintLength_le_of_valid (J : List ℕ) (N : ℕ)
    (hDistinct : J.Nodup) (hInside : ∀ a ∈ J, a < N) : J.length ≤ N := by
  have hSub : J.toFinset ⊆ Finset.range N := by
    intro a ha
    exact Finset.mem_range.mpr (hInside a (List.mem_toFinset.mp ha))
  have hCard := Finset.card_le_card hSub
  simpa only [List.toFinset_card_of_nodup hDistinct, Finset.card_range] using hCard

theorem hintDecoderStart_word (E : RAMEnv) {M : ℕ} (y : Fin M → ZMod 2) (J : List ℕ)
    (hW : 0 < E.W) (hWords : wordsOf E.W M < 2 ^ E.W) (hLength : J.length < 2 ^ E.W)
    (hJ : ∀ a ∈ J, a < 2 ^ E.W) : UpWordState E (decoderStart E.W y J) := by
  constructor
  · intro r
    simp only [decoderStart, initState]
    split_ifs <;> first | exact hWords | exact hLength | exact Nat.two_pow_pos E.W
  · intro a
    simp only [decoderStart, initState, hintMem]
    split_ifs with ha
    · exact packMem_lt E.W hW y a
    · rw [List.getD_eq_getElem?_getD]
      cases hh : J[a - wordsOf E.W M]? with
      | none => exact Nat.two_pow_pos E.W
      | some k => exact hJ k (List.mem_of_getElem? hh)

theorem hintDecoderStart_packed (W : ℕ) {M : ℕ} (y : Fin M → ZMod 2) (J : List ℕ) :
    ∀ a < wordsOf W M, (decoderStart W y J).mem a = packMem W y a := by
  intro a ha
  simp [decoderStart, initState, hintMem, ha]

theorem hintDecoderStart_hintList (W : ℕ) {M : ℕ} (y : Fin M → ZMod 2) (J : List ℕ) :
    ∀ i (hi : i < J.length), (decoderStart W y J).mem (wordsOf W M + i) = J[i] := by
  intro i hi
  have h : ¬ wordsOf W M + i < wordsOf W M := by omega
  simp [decoderStart, initState, hintMem, h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem hintDecoderStart_fresh (W : ℕ) {M : ℕ} (y : Fin M → ZMod 2) (J : List ℕ) :
    ∀ a, wordsOf W M + J.length ≤ a → (decoderStart W y J).mem a = 0 := by
  intro a ha
  have h : ¬ a < wordsOf W M := by omega
  simp [decoderStart, initState, hintMem, h, List.getD_eq_getElem?_getD,
    List.getElem?_eq_none (by omega : J.length ≤ a - wordsOf W M)]

theorem hintDecoderStart_stamp_bits (E : RAMEnv) {M : ℕ} (y : Fin M → ZMod 2) (J : List ℕ)
    (N q : ℕ) (hN : N < 2 ^ E.W)
    (hDistinct : J.Nodup) (hInside : ∀ a ∈ J, a < N) :
    hintStampValue E ((decoderStart E.W y J).regs 1) (min ((decoderStart E.W y J).regs 2) N)
      (decoderStart E.W y J).mem q = hintTruth (q ∈ J.toFinset) := by
  have hLen := hintLength_le_of_valid J N hDistinct hInside
  change hintStampValue E (wordsOf E.W M) (min J.length N) (decoderStart E.W y J).mem q = _
  rw [Nat.min_eq_left hLen]
  unfold hintStampValue
  apply hintTruth_congr
  rw [List.mem_toFinset, List.mem_iff_getElem]
  have hAt (j : ℕ) (hj : j < J.length) :
      (decoderStart E.W y J).mem (wordsOf E.W M + j) % 2 ^ E.W = J[j] := by
    rw [hintDecoderStart_hintList E.W y J j hj,
      Nat.mod_eq_of_lt ((hInside _ (List.getElem_mem hj)).trans hN)]
  constructor
  · rintro ⟨j, hj, he⟩
    exact ⟨j, hj, (hAt j hj).symm.trans he⟩
  · rintro ⟨j, hj, he⟩
    exact ⟨j, hj, (hAt j hj).trans he⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderStart_word
#print axioms LinearSetReconciliation327.Main.hintDecoderStart_fresh
#print axioms LinearSetReconciliation327.Main.hintDecoderStart_stamp_bits
end -- Def_LinearSetReconciliation327_Main_HintDecoderStart20261120

section -- Def_LinearSetReconciliation327_Main_HintRunPlacedPhase20261120
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
end -- Def_LinearSetReconciliation327_Main_HintRunPlacedPhase20261120

section -- Def_LinearSetReconciliation327_Main_HintRecursiveColumnSlice20261120
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
end -- Def_LinearSetReconciliation327_Main_HintRecursiveColumnSlice20261120

section -- Def_LinearSetReconciliation327_Main_HintRecursiveColumnAssemble20261120
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
end -- Def_LinearSetReconciliation327_Main_HintRecursiveColumnAssemble20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedSubtree20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintPlacedSubtree (CR : CRFamily) (H : HintParams)
    (D : HintDecoderTables) {T : Node} (hT : IsSchemeTree H T) (node seed : ℕ) : Prop where
  span : node + T.nodeCount ≤ D.infos.length
  read : ∀ i < T.nodeCount, D.infos[node + i]? = (hintNodeInfos CR hT node seed)[i]?

theorem hintNodeCount_pos (T : Node) : 0 < T.nodeCount := by
  cases T <;> simp [Node.nodeCount]

theorem HintPlacedSubtree.root (S : CRSourceBundle) (H : HintParams)
    {T : Node} (hT : IsSchemeTree H T) (W Bc header : ℕ) :
    HintPlacedSubtree (crFamily S) H (hintDecoderTables S H hT W Bc header) hT 0 0 := by
  constructor
  · change 0 + T.nodeCount ≤ (hintNodeInfos (crFamily S) hT 0 0).length
    rw [hintNodeInfos_length, Nat.zero_add]
  · intro i _
    change (hintNodeInfos (crFamily S) hT 0 0)[0 + i]? = _
    rw [Nat.zero_add]

theorem HintPlacedSubtree.child {CR : CRFamily} {H : HintParams} {D : HintDecoderTables}
    {N X Y t node seed : ℕ} {Xs Ys : Fin (H.scheme N X Y).ℓ → ℕ}
    {children : Fin (H.scheme N X Y).ℓ → Node} {hchild : ∀ s, IsSchemeTree H (children s)}
    (parent : HintPlacedSubtree CR H D (.recursive N X Y t Xs Ys children hchild) node seed)
    (col : Fin (H.scheme N X Y).ℓ) :
    HintPlacedSubtree CR H D (hchild col) (hintChildPhysicalIndex children node col)
      (hintChildSchemeIndex children seed col) := by
  let T := Node.recursive (H.scheme N X Y) t Xs Ys children
  let start := ((List.ofFn fun i => (children i).nodeCount).take col.val).sum
  have hEnd : node + 1 + start + (children col).nodeCount ≤ node + T.nodeCount := by
    rw [show T.nodeCount = 1 + ∑ i, (children i).nodeCount from rfl, ← Nat.add_assoc]
    exact hintChildPhysicalIndex_end children node col
  have hSpan : node + T.nodeCount ≤ D.infos.length := parent.span
  constructor
  · exact hEnd.trans hSpan
  · intro i hi
    have hInside : 1 + start + i < T.nodeCount := by omega
    change D.infos[node + 1 + start + i]? =
      (hintNodeInfos CR (hchild col) (hintChildPhysicalIndex children node col)
        (hintChildSchemeIndex children seed col))[i]?
    rw [show node + 1 + start + i = node + (1 + start + i) by omega, parent.read _ hInside]
    exact hintNodeInfos_child CR N X Y t Xs Ys children hchild node seed col i hi

theorem HintPlacedSubtree.head {CR : CRFamily} {H : HintParams} {D : HintDecoderTables}
    {T : Node} {hT : IsSchemeTree H T} {node seed : ℕ}
    (h : HintPlacedSubtree CR H D hT node seed) :
    D.infos[node]? = some (hintNodeInfo CR hT node seed) := by
  have hr := h.read 0 (hintNodeCount_pos T)
  rw [Nat.add_zero] at hr
  have h0 : (hintNodeInfos CR hT node seed)[0]? = some (hintNodeInfo CR hT node seed) := by
    cases hT <;> rfl
  exact hr.trans h0

theorem HintPlacedSubtree.info (S : CRSourceBundle) (H : HintParams)
    {R T : Node} (hR : IsSchemeTree H R) (hT : IsSchemeTree H T) (W Bc header node seed : ℕ) :
    let D := hintDecoderTables S H hR W Bc header
    HintPlacedSubtree (crFamily S) H D hT node seed →
    D.placement.info node = hintNodeInfo (crFamily S) hT node seed := by
  dsimp only
  intro h
  change ((hintDecoderTables S H hR W Bc header).infos[node]?).getD _ = _
  rw [h.head, Option.getD_some]

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintPlacedSubtree.child
#print axioms LinearSetReconciliation327.Main.HintPlacedSubtree.info
end -- Def_LinearSetReconciliation327_Main_HintPlacedSubtree20261120

section -- Def_LinearSetReconciliation327_Main_HintSubtreeArena20261120
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
end -- Def_LinearSetReconciliation327_Main_HintSubtreeArena20261120

section -- Def_LinearSetReconciliation327_Main_HintColumnFrames20261120
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
end -- Def_LinearSetReconciliation327_Main_HintColumnFrames20261120

section -- Def_LinearSetReconciliation327_Main_HintSubtreeFrame20261120
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
end -- Def_LinearSetReconciliation327_Main_HintSubtreeFrame20261120

section -- Def_LinearSetReconciliation327_Main_HintUpdateAuxBounds20261120
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
end -- Def_LinearSetReconciliation327_Main_HintUpdateAuxBounds20261120

section -- Def_LinearSetReconciliation327_Main_HintNodeGeometry20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintNodeInfo_sizes (CR : CRFamily) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (node seed : ℕ) :
    (hintNodeInfo CR hT node seed).universeSize = T.N ∧
    (hintNodeInfo CR hT node seed).payloadBits = synLen CR T ∧
    (hintNodeInfo CR hT node seed).schemes = (schemeNodes T).length := by
  cases hT <;> exact ⟨rfl, rfl, rfl⟩

theorem hintArenaFor_workspace (S : CRSourceBundle) (H : HintParams) (W : ℕ)
    (info : HintNodeInfo) (start : ℕ) :
    let A := hintArenaFor S H W info start
    A.payload = start ∧ A.workStart = wordsOf W info.payloadBits + 1 ∧
    A.saveOffset = A.workStart + 2 * info.schemes ∧ A.transcript = A.payload + A.saveOffset + 2 := by
  unfold hintArenaFor
  cases info.rowParams with
  | none => cases info.isCR <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | some a => cases a; cases info.isCR <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem hintArenaFor_rowOrder (S : CRSourceBundle) (H : HintParams) (W : ℕ)
    (info : HintNodeInfo) (start N X Y t : ℕ)
    (hN : info.universeSize = N) (hT : info.residualCapacity = t) (hXY : info.rowParams = some (X, Y)) :
    let A := hintArenaFor S H W info start
    let data := S.data N t
    A.transcript + H.rows X Y * H.ell N X Y ≤ A.hints ∧
      A.hints + N < A.result ∧ A.result + N < A.residual ∧
      A.residual + wordsOf W data.R + 2 ≤ A.residualBitmap + 1 ∧
      A.residualBitmap + N < A.crRegisters ∧
      A.limit = A.crRegisters + 16 + (2 ^ (data.W + 1) + 1) + crSourceSteps S N t + 1 := by
  have hPair : (info.universeSize, info.residualCapacity) = (N, t) := Prod.ext hN hT
  have hR := congrArg (fun p : ℕ × ℕ => (S.data p.1 p.2).R) hPair
  have hW := congrArg (fun p : ℕ × ℕ => (S.data p.1 p.2).W) hPair
  dsimp only at hR hW
  have hArea : hintArenaFor S H W info start =
      hintNodeArena start W info.payloadBits info.schemes (H.rows X Y) (H.ell N X Y) N
        (S.data N t).R (S.data N t).W (crSourceSteps S N t) := by
    simp only [hintArenaFor, hN, hT, hXY, Option.isSome_some, Bool.or_true, if_true, hR, hW]
  dsimp only
  rw [hArea]
  dsimp only [hintNodeArena]
  exact ⟨le_rfl, by omega, by omega, by omega, by omega, rfl⟩

theorem hintDecoderTables_localInput (S : CRSourceBundle) (H : HintParams)
    {R T : Node} (hR : IsSchemeTree H R) (hT : IsSchemeTree H T) (W Bc header node seed : ℕ) :
    let D := hintDecoderTables S H hR W Bc header
    let A := D.placement.arena node
    let word := D.placement.inputWord node
    HintPlacedSubtree (crFamily S) H D hT node seed →
    wordsOf W (synLen (crFamily S) T) ≤ A.workStart ∧
      UpSaveRoom A.workStart A.saveOffset T ∧
      A.payload + A.saveOffset + 2 = A.transcript ∧
      word + wordsOf W (synLen (crFamily S) T) ≤ A.transcript ∧
      (0 < W → (word * W + synLen (crFamily S) T) / W < A.transcript) := by
  dsimp only
  intro hPlaced
  let D := hintDecoderTables S H hR W Bc header
  let A := D.placement.arena node
  let word := D.placement.inputWord node
  let M := synLen (crFamily S) T
  let info := D.placement.info node
  have hInfo : info = hintNodeInfo (crFamily S) hT node seed :=
    HintPlacedSubtree.info S H hR hT W Bc header node seed hPlaced
  obtain ⟨_, hBits, hSchemes⟩ := hintNodeInfo_sizes (crFamily S) H hT node seed
  have hBits' : info.payloadBits = M := hInfo ▸ hBits
  have hSchemes' : info.schemes = (schemeNodes T).length := hInfo ▸ hSchemes
  obtain ⟨_, hp, hs, ht⟩ := hintArenaFor_workspace S H W info (hintArenaStart D.heap D.stride node)
  change A.workStart = wordsOf W info.payloadBits + 1 at hp
  change A.saveOffset = A.workStart + 2 * info.schemes at hs
  have hWork : A.workStart = wordsOf W M + 1 := by rwa [hBits'] at hp
  have hSav : A.saveOffset = A.workStart + 2 * (schemeNodes T).length := by rwa [hSchemes'] at hs
  have hTran : A.transcript = A.payload + A.saveOffset + 2 := ht
  have hw : word ≤ A.payload := by
    dsimp only [word, HintDecoderPlacement.inputWord]
    split
    · exact Nat.zero_le _
    · exact le_rfl
  change wordsOf W M ≤ A.workStart ∧ UpSaveRoom A.workStart A.saveOffset T ∧
    A.payload + A.saveOffset + 2 = A.transcript ∧ word + wordsOf W M ≤ A.transcript ∧
    (0 < W → (word * W + M) / W < A.transcript)
  refine ⟨by omega, hSav.ge, hTran.symm, by omega, ?_⟩
  intro hW
  rw [Nat.mul_comm word W, Nat.mul_add_div hW]
  have hCover := Nat.div_le_div_right (c := W) (up_words_cover_budget W M hW)
  rw [Nat.mul_comm (wordsOf W M), Nat.mul_div_cancel_left _ hW] at hCover
  omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_localInput
#print axioms LinearSetReconciliation327.Main.hintArenaFor_rowOrder
end -- Def_LinearSetReconciliation327_Main_HintNodeGeometry20261120

section -- Def_LinearSetReconciliation327_Main_HintSubtreeReady20261120
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
end -- Def_LinearSetReconciliation327_Main_HintSubtreeReady20261120

section -- Def_LinearSetReconciliation327_Main_HintPhaseEndpoints20261120
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
end -- Def_LinearSetReconciliation327_Main_HintPhaseEndpoints20261120

section -- Def_LinearSetReconciliation327_Main_HintPhaseExists20261120
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
end -- Def_LinearSetReconciliation327_Main_HintPhaseExists20261120

section -- Def_LinearSetReconciliation327_Main_HintChildTableReady20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintChildUpdateSchedule_mem (CR : CRFamily) (Bc colBase : ℕ)
    (T : Node) (seed sav : ℕ) (it : UpIt)
    (hi : it ∈ hintChildUpdateSchedule CR Bc colBase T seed sav) :
    it ∈ upSched CR Bc colBase T seed 0 0 sav [] ∨
      it ∈ upSched CR Bc colBase T 0 0 0 sav [] := by
  rw [hintChildUpdateSchedule, List.mem_cons] at hi
  rcases hi with h | h
  · subst it
    right
    rw [upSched_decomp, upHead_zero]
    simp
  · left
    rw [upSched_decomp]
    simp only [List.mem_append] at h
    simp only [List.nil_append, List.mem_append]
    tauto

theorem hintChildTable_ready (S : CRSourceBundle) (H : HintParams) (R T : Node)
    (hT : IsSchemeTree H T) (seedData : (hintSpec R).Seed) (W : ℕ) (det : ℕ → ℕ)
    (Bc control detBase seed sav : ℕ) (hW : 0 < W) (hWord : 16 < 2 ^ W)
    (hFit : (hintSpec R).Fits W)
    (hDims : UpDimsBound (2 ^ W - 1) T) (hStatic : UpTreeStatic (crFamily S) Bc T.N T)
    (hBlock : BlockOf R seed (schemeNodes T))
    (hSeed : seed + (schemeNodes T).length < 2 ^ W) (hBc : Bc + 1 < 2 ^ W) :
    let E := (hintSpec R).env W det seedData
    let CR := crFamily S
    let colBase := hintSubtreeColBase Bc T
    let items := hintChildUpdateSchedule CR Bc colBase T seed sav
    sav + 1 < 2 ^ W →
    synLen CR T < 2 ^ W →
    detBase + colBase + upTabLen Bc T < 2 ^ W →
    (hintSubtreeBlock CR W control Bc T seed sav).At E detBase →
    UpSavedLayout E detBase items ∧
      E.det (detBase % 2 ^ W) % 2 ^ W = items.length ∧ E.det (detBase + 3) = control ∧
      ∀ i < T.N, UpLocalTree CR (upShiftDetEnv E detBase) i Bc colBase T
        (hintKappaAux H R seedData T hT seed) seed 0 0 := by
  let E := (hintSpec R).env W det seedData
  let CR := crFamily S
  let colBase := hintSubtreeColBase Bc T
  let items := hintChildUpdateSchedule CR Bc colBase T seed sav
  dsimp only
  intro hSav hBits hSpace hAt
  change synLen CR T < 2 ^ W at hBits
  change detBase + colBase + upTabLen Bc T < 2 ^ W at hSpace
  have hEnd : colBase + upTabLen Bc T < 2 ^ W := by omega
  have hTotal : detBase + (colBase + upTabLen Bc T) ≤ 2 ^ W := by omega
  have hFields : ∀ it ∈ items, ∀ f < 16, it.fld f < 2 ^ W := by
    have hAll (k : ℕ) (hk : k ≤ seed) :
        ∀ it ∈ upSched CR Bc colBase T k 0 0 sav [], ∀ f < 16, it.fld f < 2 ^ W := by
      intro it hi f hf
      have hF := upSched_fields_le CR Bc colBase (2 ^ W - 1) (by omega) (by omega)
        T k 0 0 sav [] hDims (by omega : k + (schemeNodes T).length ≤ 2 ^ W - 1)
        (by change 0 + synLen CR T ≤ 2 ^ W - 1; omega)
        (by change colBase + 0 + upTabLen Bc T ≤ 2 ^ W - 1; omega)
        (by omega) (by simp) it hi f hf
      omega
    intro it hi
    rcases hintChildUpdateSchedule_mem CR Bc colBase T seed sav it hi with hp | hp
    · exact hAll seed (Nat.le_refl _) it hp
    · exact hAll 0 (Nat.zero_le _) it hp
  have hValid : ∀ it ∈ items, UpItemKind it ∧ it.sav + 1 < 2 ^ W := by
    intro it hi
    rcases hintChildUpdateSchedule_mem CR Bc colBase T seed sav it hi with hp | hp
    · exact upSched_valid_records CR Bc colBase T seed 0 0 sav W hSav hBc it hp
    · exact upSched_valid_records CR Bc colBase T 0 0 0 sav W hSav hBc it hp
  have hSpecs := hintSubtreeBlock_specs CR E control Bc T seed sav detBase hAt hEnd hTotal
    hFields (fun it hi => (hValid it hi).1) (fun it hi _ => (hValid it hi).2)
  refine ⟨hSpecs.1, hSpecs.2.1, hSpecs.2.2, ?_⟩
  intro i _
  have hBase : 4 < colBase := by unfold colBase hintSubtreeColBase; omega
  have hAt' : ∀ q < colBase + upTabLen Bc T,
      det (detBase + q) = hintSubtreeDet W control colBase items (upTabFun CR Bc T 0) q := hAt
  exact hintSubtreeLocal_of_placed CR H R T hT seedData W det detBase control Bc colBase T.N i seed
    items (upTabFun CR Bc T 0) (by omega) hW hFit hBase
    (Nat.le_trans hDims.universe (Nat.sub_le _ _)) hBlock hStatic
    (upTabFullTree_self CR Bc T 0) hEnd hBits hTotal hAt'

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintChildTable_ready
end -- Def_LinearSetReconciliation327_Main_HintChildTableReady20261120

section -- Def_LinearSetReconciliation327_Main_HintPrepareChildPhase20261120
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
end -- Def_LinearSetReconciliation327_Main_HintPrepareChildPhase20261120

section -- Def_LinearSetReconciliation327_Main_HintRecursiveColumnPhase20261120
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
end -- Def_LinearSetReconciliation327_Main_HintRecursiveColumnPhase20261120


