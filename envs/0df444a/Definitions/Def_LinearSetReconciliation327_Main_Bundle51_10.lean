-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Bundle51_10
-- name    : LinearSetReconciliation327_Main_Bundle51_10
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T14:25:30.000793+00:00
-- url     : https://prove2.me/theorems/74b11c52-91da-49cd-9e27-603de07d5ff5
-- title:
--   LinearSetReconciliation327 — Bundle51_10
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_Bundle51_10` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintDecodeBridge20261120
import Definitions.Def_LinearSetReconciliation327_Main_HintSubtreeDet20261120
import Definitions.Def_LinearSetReconciliation327_Main_Bundle51_09

/-! Bundled module: LinearSetReconciliation327_Main_Bundle51_10
    Members (declaration text copied byte-identically, dependency order):
      * Definitions.Def_LinearSetReconciliation327_Main_HintEventRecord20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintTreeDet20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintAuxDet20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintNodeAux20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDecoderTableLayout20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedRoot20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintScheduledActions20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDecoderPhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintResidualExact20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPlacedResidual20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintResidualTailPhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintDecoderArenaFit20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintChildSpan20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintChildCopyPhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintChildTogglePhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintTranscriptTrace20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintRecoverColumnPhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintResidualPrefixPhase20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintFinishRowExact20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPredictRowExact20261120
      * Definitions.Def_LinearSetReconciliation327_Main_HintPredictPlaced20261120
    Only `import` lines were merged; every member body is wrapped in its own
    `section ... end` so that per-file `set_option`s stay scoped. -/

section -- Def_LinearSetReconciliation327_Main_HintEventRecord20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

structure HintDecoderPlacement where
  width : ℕ
  control : ℕ
  rowScratch : ℕ
  info : ℕ → HintNodeInfo
  arena : ℕ → HintNodeArena
  threshold : ℕ → ℕ → ℕ
  updateTable : ℕ → ℕ
  residualTable : ℕ → ℕ
  crTable : ℕ → ℕ

def HintDecoderPlacement.inputWord (L : HintDecoderPlacement) (node : ℕ) : ℕ :=
  if node = 0 then 0 else (L.arena node).payload

noncomputable def hintRowEventBlock (H : HintParams) (L : HintDecoderPlacement)
    (node seed row prefixLen output abstentions : ℕ) : HintDetBlock :=
  let info := L.info node
  let N := info.universeSize
  let (X, Y) := info.rowParams.getD (0, 0)
  let A := L.arena node
  let K := H.Nmax N X Y
  let BY := H.BY N X Y
  let m := H.rows X Y
  let S := hintRowWorkspace L.rowScratch prefixLen K BY seed row (H.ell N X Y) K
  let F := S.fields (rowLen N m row) m A.hints (A.transcript + row)
    (H.BX N X Y) BY (L.threshold node row) output abstentions
  hintRowDetBlock S.parent (F.value S.gauss)

noncomputable def hintCREventBlock (S : CRSourceBundle) (L : HintDecoderPlacement)
    (node offset destination N t : ℕ) : HintDetBlock :=
  let data := S.data N t
  let A := hintCRArea data.W offset (L.arena node).crRegisters (L.crTable node) 0 destination L.control
  hintCRCallBlock A L.width data.W data.R (crSourceSteps S N t) N

noncomputable def hintEventRecord (S : CRSourceBundle) (H : HintParams) (L : HintDecoderPlacement) :
    HintTreeEvent → HintDetBlock
  | .store node offset count => hintUnpackDetBlock (L.arena node).result offset L.width count
  | .directBit node row col offset =>
      let (X, Y) := (L.info node).rowParams.getD (0, 0)
      hintDirectBitBlock L.width (L.arena node).transcript (H.rows X Y) row col offset
  | .childCopy _ _ child offset count => hintUnpackDetBlock (L.arena child).payload offset L.width count
  | .residualCopy node offset count => hintUnpackDetBlock (L.arena node).residual offset L.width count
  | .predict node seed col row =>
      let info := L.info node
      let (X, Y) := info.rowParams.getD (0, 0)
      let child := info.children[col]?.getD 0
      hintRowEventBlock H L node seed row col
        ((L.arena node).transcript + col * H.rows X Y) (L.arena child).hints
  | .finishRow node seed row =>
      let info := L.info node
      let (X, Y) := info.rowParams.getD (0, 0)
      hintRowEventBlock H L node seed row (H.ell info.universeSize X Y) (L.arena node).result 0
  | .childToggle parent col child _ coord =>
      let (X, Y) := (L.info parent).rowParams.getD (0, 0)
      hintGateBlock ((L.arena parent).transcript + col * H.rows X Y + coord) coord
        (L.updateTable child) (L.arena child).payload
  | .residualToggle node coord =>
      hintGateBlock ((L.arena node).result + coord) coord (L.residualTable node) (L.arena node).residual
  | .recoverColumn parent col child =>
      let (X, Y) := (L.info parent).rowParams.getD (0, 0)
      hintColumnAddBlock ((L.arena parent).transcript + col * H.rows X Y)
        (L.arena child).result (H.rows X Y)
  | .correctEstimate node =>
      hintColumnAddBlock (L.arena node).result (L.arena node).residualBitmap (L.info node).universeSize
  | .decodeLeaf node offset N t => hintCREventBlock S L node offset (L.arena node).result N t
  | .decodeResidual node N t =>
      hintCREventBlock S L node ((L.arena node).residual * L.width) (L.arena node).residualBitmap N t

def HintTreeEvent.recordLength : HintTreeEvent → ℕ
  | .store .. | .directBit .. | .childCopy .. | .residualCopy ..
  | .childToggle .. | .residualToggle .. => 4
  | .predict .. | .finishRow .. => 31
  | .recoverColumn .. | .correctEstimate .. => 3
  | .decodeLeaf .. | .decodeResidual .. => 12

theorem hintEventRecord_length (S : CRSourceBundle) (H : HintParams) (L : HintDecoderPlacement)
    (e : HintTreeEvent) : (hintEventRecord S H L e).length = e.recordLength := by
  cases e <;> rfl

theorem hintEventRecord_nonempty (S : CRSourceBundle) (H : HintParams) (L : HintDecoderPlacement)
    (e : HintTreeEvent) : 0 < (hintEventRecord S H L e).length := by
  rw [hintEventRecord_length]
  cases e <;> simp [HintTreeEvent.recordLength]

theorem hintCREventBlock_descriptor (S : CRSourceBundle) (L : HintDecoderPlacement)
    (node offset destination N t descriptor : ℕ) :
    hintCREventBlock S L node offset destination N t =
      hintCRCallBlock
        (hintCRArea (S.data N t).W offset (L.arena node).crRegisters (L.crTable node) descriptor destination L.control)
        L.width (S.data N t).W (S.data N t).R (crSourceSteps S N t) N := by
  rfl

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintEventRecord_nonempty
#print axioms LinearSetReconciliation327.Main.hintCREventBlock_descriptor
end -- Def_LinearSetReconciliation327_Main_HintEventRecord20261120

section -- Def_LinearSetReconciliation327_Main_HintTreeDet20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintEventDescriptor (header : ℕ) (events : List HintTreeEvent)
    (record : HintTreeEvent → HintDetBlock) (j : ℕ) : ℕ :=
  header + 16 + 2 * events.length + hintDetBlockOffset (events.map record) j

def hintTreeEntries (header : ℕ) (events : List HintTreeEvent)
    (record : HintTreeEvent → HintDetBlock) : List (ℕ × ℕ) :=
  List.ofFn fun j : Fin events.length =>
    (events[j.val].tag, hintEventDescriptor header events record j.val)

def hintTreeDetBlocks (previous : ℕ → ℕ) (header control hintMap resultMap listBase N : ℕ)
    (events : List HintTreeEvent) (record : HintTreeEvent → HintDetBlock) (aux : List HintDetBlock) :
    List HintDetBlock :=
  hintRootDetBlock previous control hintMap resultMap listBase (header + 16) events.length N ::
    hintDispatchDetBlock (hintTreeEntries header events record) :: (events.map record ++ aux)

theorem hintTreeEntries_length (header : ℕ) (events : List HintTreeEvent)
    (record : HintTreeEvent → HintDetBlock) :
    (hintTreeEntries header events record).length = events.length := by
  simp [hintTreeEntries]

theorem hintEventDescriptor_end (header : ℕ) (events : List HintTreeEvent)
    (record : HintTreeEvent → HintDetBlock) (j : Fin events.length) :
    hintEventDescriptor header events record j.val + (record events[j.val]).length ≤
      header + 16 + 2 * events.length + hintDetBlockOffset (events.map record) events.length := by
  let lengths := (events.map record).map HintDetBlock.length
  have hLen : lengths.length = events.length := by simp [lengths]
  have hj : j.val < lengths.length := by rw [hLen]; exact j.isLt
  have h := hintTakeSum_succ lengths j.val hj
  have hv : lengths[j.val] = (record events[j.val]).length := by simp [lengths]
  have hLe := hintTakeSum_mono lengths (Nat.succ_le_of_lt j.isLt)
  rw [h, hv] at hLe
  simp only [lengths, ← List.map_take] at hLe
  simp only [hintEventDescriptor, hintDetBlockOffset, ← List.map_take]
  omega

theorem hintTreeDet_record (E : RAMEnv) (up previous : ℕ → ℕ)
    (header control hintMap resultMap listBase N : ℕ)
    (events : List HintTreeEvent) (record : HintTreeEvent → HintDetBlock) (aux : List HintDetBlock)
    (hDet : E.det = hintAssembledDet up header
      (hintTreeDetBlocks previous header control hintMap resultMap listBase N events record aux))
    (hHeader : 3 < header) (j : Fin events.length) :
    (record events[j.val]).At E (hintEventDescriptor header events record j.val) := by
  let blocks := hintTreeDetBlocks previous header control hintMap resultMap listBase N events record aux
  have hIndex : j.val + 2 < blocks.length := by
    have hj := j.isLt
    simp only [blocks, hintTreeDetBlocks, List.length_cons, List.length_append, List.length_map]
    omega
  have hRecord : blocks[j.val + 2] = record events[j.val] := by
    have h : j.val < (events.map record).length := by simpa using j.isLt
    simp [blocks, hintTreeDetBlocks, List.getElem_append_left h]
  have hOffset : hintDetBlockOffset blocks (j.val + 2) =
      16 + 2 * events.length + hintDetBlockOffset (events.map record) j.val := by
    have hj : j.val ≤ (events.map record).length := by simpa using j.isLt.le
    simp [blocks, hintTreeDetBlocks, hintDetBlockOffset, hintRootDetBlock, hintDispatchDetBlock,
      hintTreeEntries_length, List.take_append_of_le_length hj, Nat.add_assoc]
  have hAt := hintAssembledDet_block E up header blocks hDet hHeader (j.val + 2) hIndex
  rw [hRecord, hOffset] at hAt
  simpa only [hintEventDescriptor, Nat.add_assoc] using hAt

theorem hintTreeDet_fixed (E : RAMEnv) (up previous : ℕ → ℕ)
    (header control hintMap resultMap listBase N : ℕ)
    (events : List HintTreeEvent) (record : HintTreeEvent → HintDetBlock) (aux : List HintDetBlock)
    (hDet : E.det = hintAssembledDet up header
      (hintTreeDetBlocks previous header control hintMap resultMap listBase N events record aux))
    (hHeader : 3 < header) :
    (hintRootDetBlock previous control hintMap resultMap listBase (header + 16) events.length N).At E header ∧
    (hintDispatchDetBlock (hintTreeEntries header events record)).At E (header + 16) := by
  let blocks := hintTreeDetBlocks previous header control hintMap resultMap listBase N events record aux
  constructor
  · exact hintAssembledDet_block E up header blocks hDet hHeader 0 (by simp [blocks, hintTreeDetBlocks])
  · exact hintAssembledDet_block E up header blocks hDet hHeader 1 (by simp [blocks, hintTreeDetBlocks])

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintTreeDet_record
end -- Def_LinearSetReconciliation327_Main_HintTreeDet20261120

section -- Def_LinearSetReconciliation327_Main_HintAuxDet20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintDetBlockRead_append_right (front tail : List HintDetBlock) (offset : ℕ) :
    hintDetBlockRead (front ++ tail) ((front.map HintDetBlock.length).sum + offset) =
      hintDetBlockRead tail offset := by
  induction front with
  | nil => simp
  | cons block front ih =>
      simp only [List.cons_append, List.map_cons, List.sum_cons, hintDetBlockRead]
      have hSkip : ¬ block.length + (front.map HintDetBlock.length).sum + offset < block.length := by omega
      rw [if_neg hSkip, show block.length + (front.map HintDetBlock.length).sum + offset - block.length =
        (front.map HintDetBlock.length).sum + offset by omega]
      exact ih

def hintAuxAddress (header : ℕ) (events : List HintTreeEvent)
    (record : HintTreeEvent → HintDetBlock) (aux : List HintDetBlock) (i : ℕ) : ℕ :=
  hintEventDescriptor header events record events.length + hintDetBlockOffset aux i

theorem hintTreeDet_aux (E : RAMEnv) (up previous : ℕ → ℕ)
    (header control hintMap resultMap listBase N : ℕ)
    (events : List HintTreeEvent) (record : HintTreeEvent → HintDetBlock) (aux : List HintDetBlock)
    (hDet : E.det = hintAssembledDet up header
      (hintTreeDetBlocks previous header control hintMap resultMap listBase N events record aux))
    (hHeader : 3 < header) (i : Fin aux.length) :
    aux[i.val].At E (hintAuxAddress header events record aux i.val) := by
  let front := [hintRootDetBlock previous control hintMap resultMap listBase (header + 16) events.length N,
    hintDispatchDetBlock (hintTreeEntries header events record)] ++ events.map record
  have hLen : hintEventDescriptor header events record events.length =
      header + (front.map HintDetBlock.length).sum := by
    simp [hintEventDescriptor, hintDetBlockOffset, front, hintRootDetBlock, hintDispatchDetBlock,
      hintTreeEntries_length, Nat.add_assoc]
    rw [List.take_of_length_le (by simp)]
  intro j hj
  rw [hDet, hintAuxAddress, hLen]
  change hintAssembledDet up header (front ++ aux)
      (header + (front.map HintDetBlock.length).sum + hintDetBlockOffset aux i.val + j) = _
  have h3 : header + (front.map HintDetBlock.length).sum + hintDetBlockOffset aux i.val + j ≠ 3 := by omega
  have hBefore : ¬ header + (front.map HintDetBlock.length).sum + hintDetBlockOffset aux i.val + j < header := by omega
  have hSub : header + (front.map HintDetBlock.length).sum + hintDetBlockOffset aux i.val + j - header =
      (front.map HintDetBlock.length).sum + (hintDetBlockOffset aux i.val + j) := by omega
  rw [hintAssembledDet, if_neg h3, if_neg hBefore, hSub, hintDetBlockRead_append_right]
  exact hintDetBlockRead_at aux i.val i.isLt j hj

theorem hintTreeDet_dispatch (E : RAMEnv) (up previous : ℕ → ℕ)
    (header control hintMap resultMap listBase N : ℕ)
    (events : List HintTreeEvent) (record : HintTreeEvent → HintDetBlock) (aux : List HintDetBlock)
    (hDet : E.det = hintAssembledDet up header
      (hintTreeDetBlocks previous header control hintMap resultMap listBase N events record aux))
    (hHeader : 3 < header) (hWord : 6 < 2 ^ E.W)
    (hSpace : hintEventDescriptor header events record events.length ≤ 2 ^ E.W)
    (hNonempty : ∀ j : Fin events.length, 0 < (record events[j.val]).length) :
    HintDispatchTable E (header + 16) (hintTreeEntries header events record) := by
  have hTables := hintTreeDet_fixed E up previous header control hintMap resultMap listBase N
    events record aux hDet hHeader
  apply HintDispatchTable.of_block E _ _ hTables.2
  · rw [hintTreeEntries_length]
    unfold hintEventDescriptor at hSpace
    omega
  · intro j
    have hj : j.val < events.length := by simpa only [hintTreeEntries_length] using j.isLt
    let k : Fin events.length := ⟨j.val, hj⟩
    have hAt : (hintTreeEntries header events record)[j.val] =
        (events[k.val].tag, hintEventDescriptor header events record k.val) := by
      simp [hintTreeEntries, k]
    rw [hAt]
    refine ⟨?_, ?_⟩
    · generalize events[k.val] = e
      cases e <;> simp only [HintTreeEvent.tag, Prod.fst] <;> omega
    · have hEnd := (hintEventDescriptor_end header events record k).trans hSpace
      have hLen := hNonempty k
      omega

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintTreeDet_aux
#print axioms LinearSetReconciliation327.Main.hintTreeDet_dispatch
end -- Def_LinearSetReconciliation327_Main_HintAuxDet20261120

section -- Def_LinearSetReconciliation327_Main_HintNodeAux20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintChildUpdateSchedule_length (CR : CRFamily) (Bc colBase : ℕ)
    (T : Node) (seed sav : ℕ) :
    (hintChildUpdateSchedule CR Bc colBase T seed sav).length = 1 + upRest Bc T := by
  have h := upSched_length CR Bc colBase T seed 0 0 sav []
  rw [upSched_decomp] at h
  simp only [List.nil_append, List.length_append, List.length_nil, Nat.add_zero] at h
  simp only [hintChildUpdateSchedule, List.length_cons, List.length_append]
  omega

def hintSubtreeColBase (Bc : ℕ) (T : Node) : ℕ := 8 + 16 * (1 + upRest Bc T)

noncomputable def hintSubtreeBlock (CR : CRFamily) (W control Bc : ℕ)
    (T : Node) (seed sav : ℕ) : HintDetBlock :=
  let firstColumn := hintSubtreeColBase Bc T
  let items := hintChildUpdateSchedule CR Bc firstColumn T seed sav
  ⟨firstColumn + upTabLen Bc T, hintSubtreeDet W control firstColumn items (upTabFun CR Bc T 0)⟩

theorem hintSubtreeBlock_specs (CR : CRFamily) (E : RAMEnv)
    (control Bc : ℕ) (T : Node) (seed sav detBase : ℕ)
    (hAt : (hintSubtreeBlock CR E.W control Bc T seed sav).At E detBase)
    (hEnd : hintSubtreeColBase Bc T + upTabLen Bc T < 2 ^ E.W)
    (hSpace : detBase + (hintSubtreeColBase Bc T + upTabLen Bc T) ≤ 2 ^ E.W)
    (hFields : ∀ it ∈ hintChildUpdateSchedule CR Bc (hintSubtreeColBase Bc T) T seed sav,
      ∀ f < 16, it.fld f < 2 ^ E.W)
    (hKinds : ∀ it ∈ hintChildUpdateSchedule CR Bc (hintSubtreeColBase Bc T) T seed sav, UpItemKind it)
    (hSaves : ∀ it ∈ hintChildUpdateSchedule CR Bc (hintSubtreeColBase Bc T) T seed sav,
      2 ≤ it.mode → it.sav + 1 < 2 ^ E.W) :
    let items := hintChildUpdateSchedule CR Bc (hintSubtreeColBase Bc T) T seed sav
    UpSavedLayout E detBase items ∧ E.det (detBase % 2 ^ E.W) % 2 ^ E.W = items.length ∧
      E.det (detBase + 3) = control := by
  apply hintSubtreeDet_specs E detBase control (hintSubtreeColBase Bc T) (upTabLen Bc T) _
    (upTabFun CR Bc T 0) _ hEnd hSpace hAt hFields hKinds hSaves
  rw [hintChildUpdateSchedule_length]
  exact le_rfl

def hintEmptyDetBlock : HintDetBlock := ⟨0, fun _ => 0⟩

noncomputable def hintNodeAuxBlocks (S : CRSourceBundle) (H : HintParams)
    (W control Bc : ℕ) (node : HintNodeInfo) (A : HintNodeArena) : List HintDetBlock :=
  let N := node.universeSize
  let t := node.residualCapacity
  let data := S.data N t
  let up := hintSubtreeBlock (crFamily S) W control Bc node.subtree node.seedIndex A.saveOffset
  let residual := if node.rowParams.isSome then
    hintSubtreeBlock (crFamily S) W control Bc (.cr N t) 0 (wordsOf W data.R)
    else hintEmptyDetBlock
  let cr := if node.isCR || node.rowParams.isSome then hintCRTableBlock data.W data.det else hintEmptyDetBlock
  let wait := match node.rowParams with
    | none => []
    | some (X, Y) => (List.range (H.rows X Y)).map fun j =>
        hintWaitDetBlock (H.Nmax N X Y) (rowLen N (H.rows X Y) j) (H.BY N X Y)
          (H.ell N X Y) (H.c N X Y)
  up :: residual :: cr :: wait

def hintJoinDetBlocks (blocks : List HintDetBlock) : HintDetBlock :=
  ⟨(blocks.map HintDetBlock.length).sum, hintDetBlockRead blocks⟩

theorem hintJoinDetBlocks_at (E : RAMEnv) (address : ℕ)
    (blocks : List HintDetBlock) (hAt : (hintJoinDetBlocks blocks).At E address)
    (i : Fin blocks.length) :
    blocks[i.val].At E (address + hintDetBlockOffset blocks i.val) := by
  intro j hj
  let lengths := blocks.map HintDetBlock.length
  have hIndex : i.val < lengths.length := by simp [lengths]
  have hTake := hintTakeSum_succ lengths i.val hIndex
  have hv : lengths[i.val] = blocks[i.val].length := by simp [lengths]
  have hEnd := hintTakeSum_mono lengths (Nat.succ_le_of_lt hIndex)
  rw [List.take_of_length_le le_rfl, hTake, hv] at hEnd
  simp only [lengths, ← List.map_take] at hEnd
  change hintDetBlockOffset blocks i.val + blocks[i.val].length ≤ (blocks.map HintDetBlock.length).sum at hEnd
  rw [Nat.add_assoc, hAt _ (by change _ < (blocks.map HintDetBlock.length).sum; omega)]
  exact hintDetBlockRead_at blocks i.val i.isLt j hj

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintSubtreeBlock_specs
#print axioms LinearSetReconciliation327.Main.hintJoinDetBlocks_at
end -- Def_LinearSetReconciliation327_Main_HintNodeAux20261120

section -- Def_LinearSetReconciliation327_Main_HintDecoderTableLayout20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def hintArenaFor (S : CRSourceBundle) (H : HintParams) (W : ℕ)
    (info : HintNodeInfo) (start : ℕ) : HintNodeArena :=
  let N := info.universeSize
  let t := info.residualCapacity
  let (rows, steps) := match info.rowParams with
    | none => (0, 0)
    | some (X, Y) => (H.rows X Y, H.ell N X Y)
  let (R, w, time) := if info.isCR || info.rowParams.isSome then
    ((S.data N t).R, (S.data N t).W, crSourceSteps S N t)
    else (0, 0, 0)
  hintNodeArena start W info.payloadBits info.schemes rows steps N R w time

noncomputable def hintRowScratchSize (H : HintParams) (info : HintNodeInfo) : ℕ :=
  match info.rowParams with
  | none => 0
  | some (X, Y) =>
      let N := info.universeSize
      let a := H.ell N X Y
      let K := H.Nmax N X Y
      (hintRowWorkspace 0 a K (H.BY N X Y) 0 0 a K).gauss.pivotRow + a

structure HintDecoderTables where
  placement : HintDecoderPlacement
  control : ℕ
  listBase : ℕ
  heap : ℕ
  stride : ℕ
  infos : List HintNodeInfo
  events : List HintTreeEvent
  aux : List HintDetBlock

noncomputable def hintDecoderTables (S : CRSourceBundle) (H : HintParams) {T : Node}
    (hT : IsSchemeTree H T) (width Bc header : ℕ) : HintDecoderTables :=
  let CR := crFamily S
  let infos := hintNodeInfos CR hT 0 0
  let info := fun node => infos[node]?.getD ⟨0, 0, 0, 0, none, [], false, .store 0, 0⟩
  let control := wordsOf width (synLen CR T) + T.N
  let rowScratch := control + 3
  let listBase := rowScratch + (infos.map (hintRowScratchSize H)).foldl max 0
  let heap := listBase + T.N
  let stride := (infos.map fun i => (hintArenaFor S H width i 0).limit).foldl max 0
  let arena := fun node => hintArenaFor S H width (info node) (hintArenaStart heap stride node)
  let offsets := fun node => if node = 0 then 0 else (arena node).payload * width
  let events := hintTreeEvents CR offsets T 0 0 0
  let blocks := fun node => hintNodeAuxBlocks S H width control Bc (info node) (arena node)
  let aux := List.ofFn fun i : Fin infos.length => hintJoinDetBlocks (blocks i.val)
  let firstAux := header + 16 + 2 * events.length + (events.map HintTreeEvent.recordLength).sum
  let auxAddress := fun node i => firstAux + hintDetBlockOffset aux node + hintDetBlockOffset (blocks node) i
  let L : HintDecoderPlacement := ⟨width, control, rowScratch, info, arena,
    fun node row => auxAddress node (3 + row), fun node => auxAddress node 0,
    fun node => auxAddress node 1, fun node => auxAddress node 2⟩
  ⟨L, control, listBase, heap, stride, infos, events, aux⟩

noncomputable def HintDecoderTables.blocks (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (previous : ℕ → ℕ) (header N : ℕ) : List HintDetBlock :=
  let A := D.placement.arena 0
  hintTreeDetBlocks previous header D.control A.hints A.result D.listBase N D.events
    (hintEventRecord S H D.placement) D.aux

noncomputable def HintDecoderTables.det (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (up previous : ℕ → ℕ) (header N : ℕ) : ℕ → ℕ :=
  hintAssembledDet up header (D.blocks S H previous header N)

theorem hintEventRecords_end (S : CRSourceBundle) (H : HintParams) (L : HintDecoderPlacement)
    (header : ℕ) (events : List HintTreeEvent) :
    hintEventDescriptor header events (hintEventRecord S H L) events.length =
      header + 16 + 2 * events.length + (events.map HintTreeEvent.recordLength).sum := by
  unfold hintEventDescriptor hintDetBlockOffset
  rw [List.take_of_length_le (by simp)]
  simp only [List.map_map, Function.comp_def, hintEventRecord_length]

noncomputable def HintDecoderTables.nodeAux (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (Bc node : ℕ) : List HintDetBlock :=
  hintNodeAuxBlocks S H D.placement.width D.control Bc (D.placement.info node) (D.placement.arena node)

noncomputable def HintDecoderTables.auxAddress (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (Bc header node index : ℕ) : ℕ :=
  hintAuxAddress header D.events (hintEventRecord S H D.placement) D.aux node +
    hintDetBlockOffset (D.nodeAux S H Bc node) index

theorem hintDecoderTables_aux_At (S : CRSourceBundle) (H : HintParams)
    {T : Node} (hT : IsSchemeTree H T) (E : RAMEnv) (up previous : ℕ → ℕ)
    (width Bc header : ℕ) (hHeader : 3 < header)
    (hDet : E.det = (hintDecoderTables S H hT width Bc header).det S H up previous header T.N) :
    let D := hintDecoderTables S H hT width Bc header
    ∀ node : Fin D.infos.length, ∀ index : Fin (D.nodeAux S H Bc node.val).length,
      (D.nodeAux S H Bc node.val)[index.val].At E (D.auxAddress S H Bc header node.val index.val) := by
  dsimp only
  let D := hintDecoderTables S H hT width Bc header
  intro node index
  change (D.nodeAux S H Bc node.val)[index.val].At E (D.auxAddress S H Bc header node.val index.val)
  have hAux : D.aux = List.ofFn (fun i : Fin D.infos.length => hintJoinDetBlocks (D.nodeAux S H Bc i.val)) := rfl
  have hLength : D.aux.length = D.infos.length := by rw [hAux, List.length_ofFn]
  let n : Fin D.aux.length := ⟨node.val, hLength.symm ▸ node.isLt⟩
  have hRecord := hintTreeDet_aux E up previous header D.control (D.placement.arena 0).hints
    (D.placement.arena 0).result D.listBase T.N D.events (hintEventRecord S H D.placement) D.aux hDet hHeader n
  have hAt : D.aux[n.val] = hintJoinDetBlocks (D.nodeAux S H Bc node.val) := by
    have h := List.getElem_ofFn (f := fun i : Fin D.infos.length => hintJoinDetBlocks (D.nodeAux S H Bc i.val))
      (i := node.val) (by simp only [List.length_ofFn]; exact node.isLt)
    simp only [hAux]
    exact h
  rw [hAt] at hRecord
  exact hintJoinDetBlocks_at E _ _ hRecord index

theorem hintDecoderTables_event_At (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (E : RAMEnv) (up previous : ℕ → ℕ) (header N : ℕ)
    (hHeader : 3 < header) (hDet : E.det = D.det S H up previous header N)
    (i : Fin D.events.length) :
    (hintEventRecord S H D.placement D.events[i.val]).At E
      (hintEventDescriptor header D.events (hintEventRecord S H D.placement) i.val) :=
  hintTreeDet_record E up previous header D.control (D.placement.arena 0).hints (D.placement.arena 0).result
    D.listBase N D.events (hintEventRecord S H D.placement) D.aux hDet hHeader i

theorem hintDecoderTables_aux_addresses (S : CRSourceBundle) (H : HintParams)
    {T : Node} (hT : IsSchemeTree H T) (width Bc header node row : ℕ) :
    let D := hintDecoderTables S H hT width Bc header
    D.placement.updateTable node = D.auxAddress S H Bc header node 0 ∧
    D.placement.residualTable node = D.auxAddress S H Bc header node 1 ∧
    D.placement.crTable node = D.auxAddress S H Bc header node 2 ∧
    D.placement.threshold node row = D.auxAddress S H Bc header node (3 + row) := by
  dsimp only [HintDecoderTables.auxAddress, hintAuxAddress]
  rw [hintEventRecords_end]
  exact ⟨rfl, rfl, rfl, rfl⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_aux_At
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_event_At
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_aux_addresses
end -- Def_LinearSetReconciliation327_Main_HintDecoderTableLayout20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedRoot20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintDecoderTables_header (S : CRSourceBundle) (H : HintParams)
    (D : HintDecoderTables) (E : RAMEnv) (up previous : ℕ → ℕ) (header N : ℕ)
    (hHeader : 3 < header) (hDet : E.det = D.det S H up previous header N)
    (hWord : 15 < 2 ^ E.W)
    (hDetSpace : header + 16 + 2 * D.events.length + (D.events.map HintTreeEvent.recordLength).sum < 2 ^ E.W)
    (hControl : D.control + 2 < 2 ^ E.W)
    (hHint : (D.placement.arena 0).hints + N < 2 ^ E.W)
    (hResult : (D.placement.arena 0).result < 2 ^ E.W)
    (hList : D.listBase < 2 ^ E.W) :
    let A := D.placement.arena 0
    let record := hintEventRecord S H D.placement
    HintRootHeader E header D.control A.hints A.result D.listBase (header + 16) D.events.length N ∧
      HintDispatchTable E (header + 16) (hintTreeEntries header D.events record) := by
  let A := D.placement.arena 0
  let record := hintEventRecord S H D.placement
  have hFixed := hintTreeDet_fixed E up previous header D.control A.hints A.result D.listBase N
    D.events record D.aux hDet hHeader
  have hAnchor : E.det 3 = header := by
    rw [hDet]
    exact hintAssembledDet_anchor up header (D.blocks S H previous header N)
  refine ⟨HintRootHeader.of_block E previous header D.control A.hints A.result D.listBase (header + 16)
    D.events.length N hAnchor hFixed.1 hWord (by omega) hControl hHint (by omega) (by omega)
    hResult hList, ?_⟩
  apply hintTreeDet_dispatch E up previous header D.control A.hints A.result D.listBase N D.events
    record D.aux hDet hHeader (by omega)
  · rw [hintEventRecords_end]
    exact hDetSpace.le
  · intro j
    exact hintEventRecord_nonempty S H D.placement _

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_header
end -- Def_LinearSetReconciliation327_Main_HintPlacedRoot20261120

section -- Def_LinearSetReconciliation327_Main_HintScheduledActions20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem HintDispatchData.of_frame {control table count index : ℕ} {state out : RAMState}
    (before : HintDispatchData control table count index state)
    (context : out.regs 14 = control)
    (frame : ∀ a, control ≤ a → a ≤ control + 2 → out.mem a = state.mem a) :
    HintDispatchData control table count index out :=
  ⟨context, (frame control le_rfl (by omega)).trans before.table_pointer,
    (frame (control + 1) (by omega) (by omega)).trans before.size,
    (frame (control + 2) (by omega) le_rfl).trans before.cursor⟩

theorem hintLocatedActions_of_events (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (up previous : ℕ → ℕ) (header N : ℕ)
    (budget : ℕ → ℕ) (I : ℕ → (ℕ → ℕ) → Prop) (hHeader : 3 < header)
    (hDet : E.det = D.det S H up previous header N)
    (hExec : ∀ (j : Fin D.events.length) (act : Stmt) (base : ℕ) (state : RAMState),
      let event := D.events[j.val]
      let desc := hintEventDescriptor header D.events (hintEventRecord S H D.placement) j.val
      (hintNativeActions S)[event.tag]? = some act →
      base = hintActionEntry (hintNativeActions S) 75 event.tag →
      At (hintNativeProgram S) base (act.compile base) →
      state.pc = base → state.regs 6 = desc → state.regs 14 = D.control →
      UpWordState E state → I j.val state.mem → (hintEventRecord S H D.placement event).At E desc →
      Sem (hintNativeProgram S) E base (base + act.len) state (fun k out =>
        k ≤ budget j.val ∧ I (j.val + 1) out.mem ∧ out.regs 14 = D.control ∧
        ∀ a, D.control ≤ a → a ≤ D.control + 2 → out.mem a = state.mem a)) :
    HintLocatedActions (hintNativeProgram S) E D.control (header + 16) 75 (hintNativeActions S)
      (hintTreeEntries header D.events (hintEventRecord S H D.placement)) budget I := by
  let record := hintEventRecord S H D.placement
  let entries := hintTreeEntries header D.events record
  intro i act base state hSelect hEntry hAt hPc hArg _ hData hWord hInv
  have hI : i.val < D.events.length := by
    simpa only [entries, hintTreeEntries_length] using i.isLt
  let j : Fin D.events.length := ⟨i.val, hI⟩
  have hEntryAt : entries[i.val] = (D.events[j.val].tag, hintEventDescriptor header D.events record j.val) := by
    simp [entries, hintTreeEntries, j]
  change (hintNativeActions S)[entries[i.val].1]? = some act at hSelect
  change base = hintActionEntry (hintNativeActions S) 75 entries[i.val].1 at hEntry
  change state.regs 6 = entries[i.val].2 at hArg
  rw [hEntryAt] at hSelect hEntry hArg
  have hRecord := hintDecoderTables_event_At S H D E up previous header N hHeader hDet j
  apply Sem.mono (hExec j act base state hSelect hEntry hAt hPc hArg hData.context hWord hInv hRecord)
  rintro k out ⟨hk, hI, hContext, hFrame⟩
  exact ⟨hk, hI, hData.of_frame hContext hFrame⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintLocatedActions_of_events
end -- Def_LinearSetReconciliation327_Main_HintScheduledActions20261120

section -- Def_LinearSetReconciliation327_Main_HintDecoderPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintEventStep (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables) (E : RAMEnv)
    (header : ℕ) (j : Fin D.events.length) (budget : ℕ)
    (pre post : (ℕ → ℕ) → Prop) : Prop :=
  ∀ (act : Stmt) (base : ℕ) (state : RAMState),
    let event := D.events[j.val]
    let desc := hintEventDescriptor header D.events (hintEventRecord S H D.placement) j.val
    (hintNativeActions S)[event.tag]? = some act →
    base = hintActionEntry (hintNativeActions S) 75 event.tag →
    At (hintNativeProgram S) base (act.compile base) →
    state.pc = base → state.regs 6 = desc → state.regs 14 = D.control →
    UpWordState E state → pre state.mem → (hintEventRecord S H D.placement event).At E desc →
    Sem (hintNativeProgram S) E base (base + act.len) state (fun k out =>
      k ≤ budget ∧ post out.mem ∧ out.regs 14 = D.control ∧
      ∀ a, D.control ≤ a → a ≤ D.control + 2 → out.mem a = state.mem a)

theorem HintEventStep.mono {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header : ℕ} {j : Fin D.events.length} {time time' : ℕ}
    {before after pre post : (ℕ → ℕ) → Prop}
    (hStep : HintEventStep S H D E header j time before after)
    (hTime : time ≤ time') (hPre : ∀ m, pre m → before m) (hPost : ∀ m, after m → post m) :
    HintEventStep S H D E header j time' pre post := by
  intro act base state
  dsimp only
  intro hSelect hEntry hAt hPc hArg hCtx hWord hInv hRecord
  apply Sem.mono (hStep act base state hSelect hEntry hAt hPc hArg hCtx hWord (hPre _ hInv) hRecord)
  rintro k out ⟨hk, hOut, hc, hFrame⟩
  exact ⟨hk.trans hTime, hPost _ hOut, hc, hFrame⟩

structure HintDecoderPhase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (E : RAMEnv) (header first count : ℕ) (before after : (ℕ → ℕ) → Prop) where
  budget : ℕ → ℕ
  inv : ℕ → (ℕ → ℕ) → Prop
  start : ∀ m, inv 0 m ↔ before m
  stop : ∀ m, inv count m ↔ after m
  cursor : ∀ i m v, inv i m → inv i (Function.update m (D.control + 2) v)
  step : ∀ i < count, ∀ j : Fin D.events.length, j.val = first + i →
    HintEventStep S H D E header j (budget i) (inv i) (inv (i + 1))

noncomputable def HintDecoderPhase.append {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header first n m : ℕ} {A B C : (ℕ → ℕ) → Prop}
    (p : HintDecoderPhase S H D E header first n A B)
    (q : HintDecoderPhase S H D E header (first + n) m B C) :
    HintDecoderPhase S H D E header first (n + m) A C := by
  classical
  let inv := fun i a => if i < n then p.inv i a else q.inv (i - n) a
  let budget := fun i => if i < n then p.budget i else q.budget (i - n)
  refine ⟨budget, inv, ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases h : 0 < n
    · simpa only [inv, if_pos h] using p.start a
    · have he : n = 0 := by omega
      have hp : B a ↔ A a := (p.stop a).symm.trans (by simpa only [he] using p.start a)
      simpa only [inv, if_neg h, Nat.zero_sub] using (q.start a).trans hp
  · intro a
    have hn : ¬ n + m < n := by omega
    simpa only [inv, if_neg hn, Nat.add_sub_cancel_left] using q.stop a
  · intro i a v ha
    by_cases hi : i < n
    · simp only [inv, if_pos hi] at ha ⊢
      exact p.cursor i a v ha
    · simp only [inv, if_neg hi] at ha ⊢
      exact q.cursor (i - n) a v ha
  · intro i hi j hj
    by_cases hLeft : i < n
    · have hRun := p.step i hLeft j hj
      apply hRun.mono (by simp [budget, hLeft])
      · intro a h
        simpa only [inv, if_pos hLeft] using h
      · intro a h
        by_cases hNext : i + 1 < n
        · simpa only [inv, if_pos hNext] using h
        · have he : i + 1 = n := by omega
          rw [he] at h ⊢
          simp only [inv, lt_self_iff_false, if_false, Nat.sub_self]
          exact (q.start a).mpr ((p.stop a).mp h)
    · have hRight : i - n < m := by omega
      have hIdx : j.val = first + n + (i - n) := by omega
      have hRun := q.step (i - n) hRight j hIdx
      apply hRun.mono (by simp [budget, hLeft])
      · intro a h
        simpa only [inv, if_neg hLeft] using h
      · intro a h
        have hNext : ¬ i + 1 < n := by omega
        have he : i + 1 - n = i - n + 1 := by omega
        simpa only [inv, if_neg hNext, he] using h

theorem HintDecoderPhase.actions {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header : ℕ} {A B : (ℕ → ℕ) → Prop}
    (p : HintDecoderPhase S H D E header 0 D.events.length A B)
    (up previous : ℕ → ℕ) (N : ℕ) (hHeader : 3 < header)
    (hDet : E.det = D.det S H up previous header N) :
    HintLocatedActions (hintNativeProgram S) E D.control (header + 16) 75 (hintNativeActions S)
      (hintTreeEntries header D.events (hintEventRecord S H D.placement)) p.budget p.inv := by
  apply hintLocatedActions_of_events S H D E up previous header N p.budget p.inv hHeader hDet
  intro j
  exact p.step j.val j.isLt j (Nat.zero_add _).symm

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintDecoderPhase.append
#print axioms LinearSetReconciliation327.Main.HintDecoderPhase.actions
end -- Def_LinearSetReconciliation327_Main_HintDecoderPhase20261120

section -- Def_LinearSetReconciliation327_Main_HintResidualExact20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintCRSketchVector_native (S : CRSourceBundle) (N t : ℕ)
    (r : (Node.cr N t).Seed) (x : Finset ℕ) (hx : x ⊆ Finset.range N) :
    hintSketchVector (crFamily S) (.cr N t) r x = (S.data N t).H (crInput N x) := by
  classical
  funext q
  have h := hintCRBit_eq S N t x hx q
  have hB : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  change (if q.val ∈ (crFamily S).sketch N t x then 1 else 0) = (S.data N t).H (crInput N x) q
  rcases hB ((S.data N t).H (crInput N x) q) with h0 | h1
  · rw [h0] at h ⊢
    have hNot : q.val ∉ (crFamily S).sketch N t x := by
      intro hYes
      simp [hintTruth, hYes] at h
    simp [hNot]
  · rw [h1] at h ⊢
    have hYes : q.val ∈ (crFamily S).sketch N t x := by
      by_contra hNot
      simp [hintTruth, hNot] at h
    simp [hYes]

theorem hintExactEstimate_subset (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ) :
    sch.exactEstimate lr x J ⊆ Finset.range sch.N := by
  intro i hi
  unfold RowScheme.exactEstimate RowScheme.assembled assemble at hi
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_range.mpr u.isLt

theorem hintResidual_input (S : CRSourceBundle) (sch : RowScheme) (lr : sch.LocalSeed)
    (x J : Finset ℕ) (t : ℕ) (r : (Node.cr sch.N t).Seed)
    (hx : x ⊆ Finset.range sch.N) (hZ : sch.Z lr x J ≤ t) :
    let residual := symmDiff x (sch.exactEstimate lr x J)
    (Finset.univ.filter fun i : Fin sch.N => crInput sch.N residual i = 1).card ≤ t ∧
      hintSketchVector (crFamily S) (.cr sch.N t) r x +
          hintSketchVector (crFamily S) (.cr sch.N t) r (sch.exactEstimate lr x J) =
        (S.data sch.N t).H (crInput sch.N residual) := by
  let est := sch.exactEstimate lr x J
  let res := symmDiff x est
  have hEst : est ⊆ Finset.range sch.N := hintExactEstimate_subset sch lr x J
  have hRes : res ⊆ Finset.range sch.N := by
    intro i hi
    rcases Finset.mem_symmDiff.mp hi with ⟨h, _⟩ | ⟨h, _⟩
    · exact hx h
    · exact hEst h
  refine ⟨?_, ?_⟩
  · rw [crInput_card sch.N res hRes]
    exact hZ
  · exact (hintSketchVector_xor (crFamily S) (.cr sch.N t) r x est).symm.trans
      (hintCRSketchVector_native S sch.N t r res hRes)
 
theorem hintColumnRecovered (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ) (s : Fin sch.ℓ) :
    symmDiff (sch.exactP lr x J s) (sch.exactChildInput lr x J s) = sch.column lr x s :=
  hintPlusResidual _ _

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintResidual_input
#print axioms LinearSetReconciliation327.Main.hintColumnRecovered
end -- Def_LinearSetReconciliation327_Main_HintResidualExact20261120

section -- Def_LinearSetReconciliation327_Main_HintPlacedResidual20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintUpdate_prefix_step (CR : CRFamily) (T : Node) (r : T.Seed)
    (selected : Finset ℕ) (y : Fin (synLen CR T) → ZMod 2) (i : Fin T.N)
    (P : Program) (E : RAMEnv) (state : RAMState)
    (seed base descriptor gate detBase payBase control Bc colBase workStart sav : ℕ)
    (tbl : HintToggleGateTable E descriptor gate i.val detBase payBase control)
    (hArg : state.regs 6 = descriptor) (hWord : UpWordState E state)
    (hAt : At P base (hintToggleGateAction.compile base)) (hPc : state.pc = base)
    (hGate : state.mem gate = hintTruth (i.val ∈ selected))
    (hPayEnd : payBase + (sav + 2) ≤ 2 ^ E.W)
    (hGap : wordsOf E.W (synLen CR T) ≤ workStart)
    (h16 : 16 < 2 ^ E.W) (hN : T.N ≤ 2 ^ E.W)
    (hPayload : ∀ q < wordsOf E.W (synLen CR T), state.mem (payBase + q) =
      packMem E.W (y + hintSketchVector CR T r (selected ∩ Finset.range i.val)) q)
    (hLocal : UpLocalTree CR (upShiftDetEnv E detBase) i.val Bc colBase T r seed 0 0)
    (hRoom : UpSaveRoom workStart sav T) :
    let items := hintChildUpdateSchedule CR Bc colBase T seed sav
    UpSavedLayout E detBase items →
    E.det (detBase % 2 ^ E.W) % 2 ^ E.W = items.length →
    Sem P E base (base + hintToggleGateAction.len) state (fun k out =>
      k ≤ 147 * items.length + 24 ∧ out.regs 14 = control ∧
      (∀ q < wordsOf E.W (synLen CR T), out.mem (payBase + q) =
        packMem E.W (y + hintSketchVector CR T r (selected ∩ Finset.range (i.val + 1))) q) ∧
      UpMemFrame (UpTwoRegion payBase (wordsOf E.W (synLen CR T)) workStart (sav + 2)) state out) := by
  dsimp only
  intro hLayout hCount
  have hStep := hintChildUpdateAction_sem P E state CR T r seed base descriptor gate detBase payBase
    control Bc colBase workStart sav _ (y + hintSketchVector CR T r (selected ∩ Finset.range i.val)) i
    rfl tbl hArg hWord hAt hPc hLayout hPayEnd hGap h16 hN hCount hPayload hLocal hRoom
  apply Sem.mono hStep
  rintro k out ⟨hk, hCtrl, hNew, hFrame⟩
  refine ⟨hk, hCtrl, ?_, hFrame⟩
  intro q hq
  rw [hNew q hq, hGate, hintToggleTrace_step]

theorem hintResidualDecode_placed (S : CRSourceBundle) (L : HintDecoderPlacement)
    (node descriptor t base switchBase : ℕ) (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState) (other : List Stmt) (act : Stmt)
    (hW : E.W = L.width) (hWidth : 0 < E.W)
    (hx : x ⊆ Finset.range sch.N) (hZ : sch.Z lr x J ≤ t)
    (hN : 1 ≤ sch.N) (ht : t ≤ sch.N)
    (hWord : 11 < 2 ^ E.W) (hDesc : descriptor + 11 < 2 ^ E.W)
    (hSmall : (S.data sch.N t).W + 1 < E.W)
    (hControl : L.control < 2 ^ E.W)
    (hSpill : (L.arena node).crRegisters + 16 + 2 ^ ((S.data sch.N t).W + 1) + 1 +
      crSourceSteps S sch.N t + 1 < 2 ^ E.W)
    (hTableFit : L.crTable node + 2 ^ (S.data sch.N t).W < 2 ^ E.W)
    (hOut : (L.arena node).residualBitmap + sch.N < (L.arena node).crRegisters)
    (hInput : (L.arena node).residual * E.W + (S.data sch.N t).R < 2 ^ E.W)
    (hInputSep : ((L.arena node).residual * E.W + (S.data sch.N t).R) / E.W <
      (L.arena node).crRegisters + 16)
    (hCRTable : (hintCRTableBlock (S.data sch.N t).W (S.data sch.N t).det).At E (L.crTable node))
    (hRecord : (hintCREventBlock S L node ((L.arena node).residual * L.width)
      (L.arena node).residualBitmap sch.N t).At E descriptor)
    (hFresh : ∀ a ≤ 2 ^ ((S.data sch.N t).W + 1), state.mem ((L.arena node).crRegisters + 16 + a) = 0)
    (hPc : state.pc = base) (hArg : state.regs 6 = descriptor)
    (hSelect : (hintActionsWithCR S switchBase other hintNormalizeStmt)[other.length]? = some act)
    (hEntry : base = hintActionEntry (hintActionsWithCR S switchBase other hintNormalizeStmt) switchBase other.length)
    (hAt : At P base (act.compile base)) :
    let A := L.arena node
    let r : (Node.cr sch.N t).Seed := ()
    let estimate := sch.exactEstimate lr x J
    let residual := symmDiff x estimate
    let layout := hintCRArea (S.data sch.N t).W (A.residual * E.W) A.crRegisters (L.crTable node)
                    descriptor A.residualBitmap L.control
    (∀ q < wordsOf E.W (S.data sch.N t).R, state.mem (A.residual + q) =
      packMem E.W (hintSketchVector (crFamily S) (.cr sch.N t) r x +
                   hintSketchVector (crFamily S) (.cr sch.N t) r estimate) q) →
    Sem P E base (base + act.len) state (fun k out =>
      k ≤ hintCRNodeBudget S sch.N t ∧ out.regs 14 = L.control ∧
      HintBitmap out.mem A.residualBitmap sch.N residual ∧
      HintCRNodeFrame S layout sch.N t state.mem out.mem) := by
  let A := L.arena node
  let r : (Node.cr sch.N t).Seed := ()
  let estimate := sch.exactEstimate lr x J
  let residual := symmDiff x estimate
  let layout := hintCRArea (S.data sch.N t).W (A.residual * E.W) A.crRegisters (L.crTable node)
                    descriptor A.residualBitmap L.control
  dsimp only
  intro hPacked
  have hReq : (hintCRCallBlock layout E.W (S.data sch.N t).W (S.data sch.N t).R
      (crSourceSteps S sch.N t) sch.N).At E descriptor := by
    rw [hintCREventBlock_descriptor S L node _ _ _ _ descriptor] at hRecord
    simpa only [layout, A, hW] using hRecord
  have hPre := hintCRArea_pre S E sch.N t (A.residual * E.W) A.crRegisters (L.crTable node)
    descriptor A.residualBitmap L.control hN ht hSmall hWord hDesc hControl hSpill hTableFit
    hOut hInput hInputSep hCRTable hReq
  obtain ⟨hSupport, hVector⟩ := hintResidual_input S sch lr x J t r hx hZ
  have hBits (i : Fin (S.data sch.N t).R) :
      bitAt state.mem E.W 0 (layout.offset + i.val) =
        if (S.data sch.N t).H (crInput sch.N residual) i = 1 then 1 else 0 := by
    apply hintBitAt_aligned state.mem E.W A.residual _ i hWidth
    intro q hq
    rw [← hVector]
    exact hPacked q hq
  apply Sem.mono (hintCRNode_correct S P E state layout sch.N t base switchBase other act
    (crInput sch.N residual) hPre hSupport hPc hArg hBits hFresh hSelect hEntry hAt)
  rintro k out ⟨hk, hc, hFrame, hb⟩
  refine ⟨hk, hc, ?_, hFrame⟩
  intro a ha
  change out.mem (layout.destination + (⟨a, ha⟩ : Fin sch.N).val) = hintTruth (a ∈ residual)
  rw [hb ⟨a, ha⟩]
  change (if a ∈ residual then (1 : ZMod 2) else 0).val = hintTruth (a ∈ residual)
  by_cases h : a ∈ residual
  · rw [if_pos h, hintTruth, if_pos h]
    decide
  · rw [if_neg h, hintTruth, if_neg h]
    decide

theorem hintCorrectEstimate_placed (S : CRSourceBundle) (H : HintParams) (L : HintDecoderPlacement)
    (node descriptor base : ℕ) (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState)
    (hInfo : (L.info node).universeSize = sch.N)
    (hWord : 1 < 2 ^ E.W) (hDesc : descriptor + 2 < 2 ^ E.W)
    (hResult : (L.arena node).result < 2 ^ E.W)
    (hResid : (L.arena node).residualBitmap < 2 ^ E.W)
    (hSize : sch.N < 2 ^ E.W)
    (hSep : (L.arena node).result + sch.N ≤ (L.arena node).residualBitmap)
    (hEnd : (L.arena node).residualBitmap + sch.N ≤ 2 ^ E.W)
    (hRecord : (hintEventRecord S H L (.correctEstimate node)).At E descriptor)
    (hArg : state.regs 6 = descriptor)
    (hEst : HintBitmap state.mem (L.arena node).result sch.N (sch.exactEstimate lr x J))
    (hError : HintBitmap state.mem (L.arena node).residualBitmap sch.N
      (symmDiff x (sch.exactEstimate lr x J)))
    (hAt : At P base (hintColumnAddAction.compile base)) (hPc : state.pc = base) :
    Sem P E base (base + 20) state (fun k out =>
      k ≤ 11 * sch.N + 11 ∧ out.regs 14 = state.regs 14 ∧
      HintBitmap out.mem (L.arena node).result sch.N x ∧
      CRMemFrame (L.arena node).result ((L.arena node).result + sch.N) state.mem out.mem) := by
  have hBlock : (hintColumnAddBlock (L.arena node).result (L.arena node).residualBitmap sch.N).At E descriptor := by
    simpa only [hintEventRecord, hInfo] using hRecord
  have hTable := HintColumnAddTable.of_block E descriptor (L.arena node).result (L.arena node).residualBitmap
    sch.N hBlock hWord hDesc hResult hResid (by omega) hEnd hSize
  apply Sem.mono (hintAddBitmaps_sem P E state descriptor (L.arena node).result (L.arena node).residualBitmap
    sch.N base _ _ hTable hArg hEst hError (Or.inl hSep) hAt hPc)
  rintro k out ⟨hk, hc, hb, hf⟩
  rw [hintPlusResidual] at hb
  exact ⟨hk, hc, hb, hf⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintUpdate_prefix_step
#print axioms LinearSetReconciliation327.Main.hintResidualDecode_placed
#print axioms LinearSetReconciliation327.Main.hintCorrectEstimate_placed
end -- Def_LinearSetReconciliation327_Main_HintPlacedResidual20261120

section -- Def_LinearSetReconciliation327_Main_HintResidualTailPhase20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

noncomputable def HintDecoderPhase.single {S : CRSourceBundle} {H : HintParams} {D : HintDecoderTables}
    {E : RAMEnv} {header first time : ℕ} {A B : (ℕ → ℕ) → Prop}
    (before : ∀ m v, A m → A (Function.update m (D.control + 2) v))
    (after : ∀ m v, B m → B (Function.update m (D.control + 2) v))
    (step : ∀ j : Fin D.events.length, j.val = first → HintEventStep S H D E header j time A B) :
    HintDecoderPhase S H D E header first 1 A B := by
  let inv := fun i m => if i = 0 then A m else B m
  refine ⟨fun _ => time, inv, ?_, ?_, ?_, ?_⟩
  · intro m
    simp [inv]
  · intro m
    simp [inv]
  · intro i m v h
    by_cases hi : i = 0
    · simpa only [inv, if_pos hi] using before m v (by simpa only [inv, if_pos hi] using h)
    · simpa only [inv, if_neg hi] using after m v (by simpa only [inv, if_neg hi] using h)
  · intro i hi j hj
    have he : i = 0 := by omega
    subst i
    have h := step j (by simpa only [Nat.add_zero] using hj)
    simpa only [inv, if_true, Nat.zero_add, Nat.one_ne_zero, if_false] using h

def HintMemoryWords {M : ℕ} (W base : ℕ) (y : Fin M → ZMod 2) (m : ℕ → ℕ) : Prop :=
  ∀ q < wordsOf W M, m (base + q) = packMem W y q

def HintFreshWords (base count : ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ a < count, m (base + a) = 0

theorem HintBitmap.update_below {m : ℕ → ℕ} {base N : ℕ} {X : Finset ℕ}
    (h : HintBitmap m base N X) (index value : ℕ) (hLow : index < base) :
    HintBitmap (Function.update m index value) base N X := by
  intro a ha
  rw [Function.update_of_ne (by omega : base + a ≠ index)]
  exact h a ha

theorem HintMemoryWords.update_below {M W base : ℕ} {m : ℕ → ℕ} {y : Fin M → ZMod 2}
    (h : HintMemoryWords W base y m) (index value : ℕ) (hLow : index < base) :
    HintMemoryWords W base y (Function.update m index value) := by
  intro a ha
  rw [Function.update_of_ne (by omega : base + a ≠ index)]
  exact h a ha

theorem HintFreshWords.update_below {m : ℕ → ℕ} {base count : ℕ}
    (h : HintFreshWords base count m) (index value : ℕ) (hLow : index < base) :
    HintFreshWords base count (Function.update m index value) := by
  intro a ha
  rw [Function.update_of_ne (by omega : base + a ≠ index)]
  exact h a ha

noncomputable def hintResidualSyndrome (S : CRSourceBundle) (N t : ℕ) (x estimate : Finset ℕ) :
    Fin (synLen (crFamily S) (.cr N t)) → ZMod 2 :=
  hintSketchVector (crFamily S) (.cr N t) () x + hintSketchVector (crFamily S) (.cr N t) () estimate

noncomputable def hintResidualDecode_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first t : ℕ) (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hControl : D.placement.control = D.control)
    (hWidth : E.W = D.placement.width) (hW : 0 < E.W)
    (hx : x ⊆ Finset.range sch.N) (hZ : sch.Z lr x J ≤ t)
    (hN : 1 ≤ sch.N) (ht : t ≤ sch.N) (hWord : 11 < 2 ^ E.W)
    (hEvent : D.events[first]? = some (.decodeResidual node sch.N t)) :
    let L := D.placement
    let A := L.arena node
    let w := (S.data sch.N t).W
    let spill := A.crRegisters + 16
    let spillSize := 2 ^ (w + 1) + 1
    let spillEnd := spill + spillSize + crSourceSteps S sch.N t + 1
    let estimate := sch.exactEstimate lr x J
    let err := symmDiff x estimate
    D.control + 2 < A.result →
    A.result + sch.N ≤ A.residual →
    A.result + sch.N ≤ A.residualBitmap →
    A.residualBitmap + sch.N < A.crRegisters →
    spillEnd < 2 ^ E.W →
    w + 1 < E.W →
    L.crTable node + 2 ^ w < 2 ^ E.W →
    A.residual * E.W + (S.data sch.N t).R < 2 ^ E.W →
    (A.residual * E.W + (S.data sch.N t).R) / E.W < spill →
    (hintCRTableBlock w (S.data sch.N t).det).At E (L.crTable node) →
    (∀ p : Fin D.events.length, p.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H L) p.val + 11 < 2 ^ E.W) →
    (∀ m m', CRMemFrame A.residualBitmap spillEnd m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      (fun m => HintBitmap m A.result sch.N estimate ∧
        HintMemoryWords E.W A.residual (hintResidualSyndrome S sch.N t x estimate) m ∧
        HintFreshWords spill spillSize m ∧ keep m)
      (fun m => HintBitmap m A.result sch.N estimate ∧ HintBitmap m A.residualBitmap sch.N err ∧ keep m) := by
  let L := D.placement
  let A := L.arena node
  let w := (S.data sch.N t).W
  let spill := A.crRegisters + 16
  let spillSize := 2 ^ (w + 1) + 1
  let spillEnd := spill + spillSize + crSourceSteps S sch.N t + 1
  dsimp only
  intro hCtrl hPayload hBefore hOut hEnd hSM hTable hIn hInSep hCRTable hDesc hKeep hCursor
  change D.control + 2 < A.result at hCtrl
  change A.result + sch.N ≤ A.residual at hPayload
  change A.result + sch.N ≤ A.residualBitmap at hBefore
  change A.residualBitmap + sch.N < A.crRegisters at hOut
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
  apply HintDecoderPhase.single (time := hintCRNodeBudget S sch.N t)
  · rintro m v ⟨hb, hp, hf, hk⟩
    exact ⟨hb.update_below _ _ hCtrl, hp.update_below _ _ hCtrlP,
      hf.update_below _ _ hCtrlSpill, hCursor _ _ hk⟩
  · rintro m v ⟨hb, he, hk⟩
    exact ⟨hb.update_below _ _ hCtrl, he.update_below _ _ hCtrlB, hCursor _ _ hk⟩
  · intro pos hPos act base state
    dsimp only
    intro hSelect hEntry hAt hPc hArg hCtx _ hStart hRec
    have hOpt : D.events[pos.val]? = some (.decodeResidual node sch.N t) := by
      rw [hPos]
      exact hEvent
    have hEq := Option.some.inj ((List.getElem?_eq_getElem (l := D.events) pos.isLt).symm.trans hOpt)
    have hTag : D.events[pos.val].tag = 6 := by rw [hEq]; rfl
    rw [hTag] at hSelect hEntry
    rw [hEq] at hRec
    obtain ⟨hEst, hPacked, hFresh, hK⟩ := hStart
    let descriptor := hintEventDescriptor header D.events (hintEventRecord S H L) pos.val
    have hRec' : (hintCREventBlock S L node (A.residual * L.width) A.residualBitmap sch.N t).At E
        descriptor := hRec
    have hRun := hintResidualDecode_placed S L node descriptor t base 75 sch lr x J
      (hintNativeProgram S) E state hintNativeOtherActions act hWidth hW hx hZ hN ht hWord
      (hDesc pos hPos) hSM hControlWord hEnd hTable hOut hIn hInSep hCRTable hRec'
      (fun a ha => hFresh a (Nat.lt_succ_of_le ha)) hPc hArg hSelect hEntry hAt hPacked
    apply Sem.mono hRun
    rintro k out ⟨hk, hc, hb, hf⟩
    have hf' : ∀ a, (a < A.residualBitmap ∨ A.residualBitmap + sch.N < a) →
        (a < A.crRegisters ∨ spillEnd ≤ a) → out.mem a = state.mem a := hf
    have frame : CRMemFrame A.residualBitmap spillEnd state.mem out.mem := by
      intro a ha
      rcases ha with h | h
      · exact hf' a (Or.inl h) (Or.inl (h.trans (by omega)))
      · exact hf' a (Or.inr (by omega)) (Or.inr h)
    refine ⟨hk, ⟨?_, hb, hKeep _ _ frame hK⟩, hc.trans hControl, ?_⟩
    · intro q hq
      have hBeforeBit : A.result + q < A.residualBitmap := by omega
      rw [frame _ (Or.inl hBeforeBit)]
      exact hEst q hq
    · intro a _ ha
      exact frame a (Or.inl (by omega))

noncomputable def hintCorrectEstimate_phase (S : CRSourceBundle) (H : HintParams) (D : HintDecoderTables)
    (header node first : ℕ) (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (E : RAMEnv) (keep : (ℕ → ℕ) → Prop)
    (hInfo : (D.placement.info node).universeSize = sch.N)
    (hEvent : D.events[first]? = some (.correctEstimate node)) :
    let A := D.placement.arena node
    let estimate := sch.exactEstimate lr x J
    1 < 2 ^ E.W →
    D.control + 2 < A.result →
    A.result < 2 ^ E.W →
    A.residualBitmap < 2 ^ E.W →
    sch.N < 2 ^ E.W →
    A.result + sch.N ≤ A.residualBitmap →
    A.residualBitmap + sch.N ≤ 2 ^ E.W →
    (∀ p : Fin D.events.length, p.val = first →
      hintEventDescriptor header D.events (hintEventRecord S H D.placement) p.val + 2 < 2 ^ E.W) →
    (∀ m m', CRMemFrame A.result (A.result + sch.N) m m' → keep m → keep m') →
    (∀ m v, keep m → keep (Function.update m (D.control + 2) v)) →
    HintDecoderPhase S H D E header first 1
      (fun m => HintBitmap m A.result sch.N estimate ∧
        HintBitmap m A.residualBitmap sch.N (symmDiff x estimate) ∧ keep m)
      (fun m => HintBitmap m A.result sch.N x ∧ keep m) := by
  let A := D.placement.arena node
  dsimp only
  intro hWord hCtrl hDest hSource hSize hSep hEnd hDescriptor hKeep hCursor
  have hCtrlSrc : D.control + 2 < A.residualBitmap := by
    change D.control + 2 < A.result at hCtrl
    change A.result + sch.N ≤ A.residualBitmap at hSep
    omega
  apply HintDecoderPhase.single (time := 11 * sch.N + 11)
  · rintro m v ⟨hE, hR, hk⟩
    exact ⟨hE.update_below _ _ hCtrl, hR.update_below _ _ hCtrlSrc, hCursor _ _ hk⟩
  · rintro m v ⟨hX, hk⟩
    exact ⟨hX.update_below _ _ hCtrl, hCursor _ _ hk⟩
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
    have hRun := hintCorrectEstimate_placed S H D.placement node _ base sch lr x J (hintNativeProgram S)
      E state hInfo hWord (hDescriptor pos hPos) hDest hSource hSize hSep hEnd hRec hArg hE hR hAt hPc
    change Sem (hintNativeProgram S) E base (base + 20) state _
    apply Sem.mono hRun
    rintro k out ⟨ht, hc, hX, hf⟩
    exact ⟨ht, ⟨hX, hKeep _ _ hf hk⟩, hc.trans hCtx,
      fun a _ ha => hf a (Or.inl (ha.trans_lt hCtrl))⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintResidualDecode_phase
#print axioms LinearSetReconciliation327.Main.hintCorrectEstimate_phase
end -- Def_LinearSetReconciliation327_Main_HintResidualTailPhase20261120

section -- Def_LinearSetReconciliation327_Main_HintDecoderArenaFit20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintArenaFor_limit (S : CRSourceBundle) (H : HintParams) (W : ℕ)
    (info : HintNodeInfo) (start : ℕ) :
    (hintArenaFor S H W info start).limit = start + (hintArenaFor S H W info 0).limit := by
  unfold hintArenaFor
  cases hr : info.rowParams with
  | none =>
    by_cases hc : (info.isCR || info.rowParams.isSome) = true <;>
      simp only [hr, hc, if_true, if_false, hintNodeArena, Nat.zero_add, Nat.add_assoc]
  | some a =>
    obtain ⟨X, Y⟩ := a
    by_cases hc : (info.isCR || info.rowParams.isSome) = true <;>
      simp only [hr, hc, if_true, if_false, hintNodeArena, Nat.zero_add, Nat.add_assoc]

theorem hintFoldMax_ge (xs : List ℕ) (base value : ℕ) (h : value ∈ xs ∨ value ≤ base) :
    value ≤ xs.foldl max base := by
  induction xs generalizing base with
  | nil =>
      simpa using h
  | cons a rest ih =>
      simp only [List.foldl_cons]
      apply ih
      rcases h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr (le_max_right _ _)
        · exact Or.inl h
      · exact Or.inr (h.trans (le_max_left _ _))

theorem hintRowWorkspace_pivot_bound (start a K BY node row steps h : ℕ) (ha : a ≤ steps) :
    (hintRowWorkspace start a K BY node row steps h).gauss.pivotRow + a ≤
      start + ((hintRowWorkspace 0 steps K BY 0 0 steps K).gauss.pivotRow + steps) := by
  have hSquare : a * a ≤ steps * steps := Nat.mul_le_mul ha ha
  have hRectangle : K * a ≤ K * steps := Nat.mul_le_mul_left K ha
  dsimp only [hintRowWorkspace, hintGaussDenseArea]
  omega

theorem hintDecoderTables_arena_fits (S : CRSourceBundle) (H : HintParams)
    {T : Node} (hT : IsSchemeTree H T) (W Bc header : ℕ) :
    let D := hintDecoderTables S H hT W Bc header
    ∀ node : Fin D.infos.length,
      (D.placement.arena node.val).limit ≤ hintArenaStart D.heap D.stride node.val + D.stride := by
  dsimp only
  let D := hintDecoderTables S H hT W Bc header
  intro node
  have hInfo : D.placement.info node.val = D.infos[node.val] := by
    change D.infos[node.val]?.getD _ = _
    rw [List.getElem?_eq_getElem node.isLt, Option.getD_some]
  change (hintArenaFor S H W (D.placement.info node.val) (hintArenaStart D.heap D.stride node.val)).limit ≤ _
  rw [hintArenaFor_limit, hInfo]
  apply Nat.add_le_add_left
  apply hintFoldMax_ge
  exact Or.inl (List.mem_map.mpr ⟨D.infos[node.val], List.getElem_mem node.isLt, rfl⟩)

theorem hintDecoderTables_arena_separate (S : CRSourceBundle) (H : HintParams)
    {T : Node} (hT : IsSchemeTree H T) (W Bc header : ℕ) :
    let D := hintDecoderTables S H hT W Bc header
    ∀ i j : Fin D.infos.length, i.val < j.val →
      (D.placement.arena i.val).limit ≤ (D.placement.arena j.val).payload := by
  dsimp only
  let D := hintDecoderTables S H hT W Bc header
  intro i j hij
  have hFits := hintDecoderTables_arena_fits S H hT W Bc header i
  have hStart := hintArenaStart_disjoint D.heap D.stride i.val j.val hij
  have hPayload (info : HintNodeInfo) (base : ℕ) :
      (hintArenaFor S H W info base).payload = base := by
    unfold hintArenaFor
    cases info.rowParams <;> cases h : (info.isCR || info.rowParams.isSome) <;> rfl
  change (D.placement.arena i.val).limit ≤
    (hintArenaFor S H W (D.placement.info j.val) (hintArenaStart D.heap D.stride j.val)).payload
  rw [hPayload]
  exact hFits.trans hStart

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_arena_fits
#print axioms LinearSetReconciliation327.Main.hintDecoderTables_arena_separate
end -- Def_LinearSetReconciliation327_Main_HintDecoderArenaFit20261120

section -- Def_LinearSetReconciliation327_Main_HintChildSpan20261120
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
end -- Def_LinearSetReconciliation327_Main_HintChildSpan20261120

section -- Def_LinearSetReconciliation327_Main_HintChildCopyPhase20261120
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
end -- Def_LinearSetReconciliation327_Main_HintChildCopyPhase20261120

section -- Def_LinearSetReconciliation327_Main_HintChildTogglePhase20261120
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
end -- Def_LinearSetReconciliation327_Main_HintChildTogglePhase20261120

section -- Def_LinearSetReconciliation327_Main_HintTranscriptTrace20261120
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
end -- Def_LinearSetReconciliation327_Main_HintTranscriptTrace20261120

section -- Def_LinearSetReconciliation327_Main_HintRecoverColumnPhase20261120
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
end -- Def_LinearSetReconciliation327_Main_HintRecoverColumnPhase20261120

section -- Def_LinearSetReconciliation327_Main_HintResidualPrefixPhase20261120
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
end -- Def_LinearSetReconciliation327_Main_HintResidualPrefixPhase20261120

section -- Def_LinearSetReconciliation327_Main_HintFinishRowExact20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintEstimateRows (sch : RowScheme) (r : sch.LocalSeed) (x J : Finset ℕ)
    (output : ℕ) (done : ℕ → Prop) (mem : ℕ → ℕ) : Prop :=
  ∀ i : Fin sch.N, done ((r.1 i).val % sch.m) →
    mem (output + i.val) = hintTruth (i.val ∈ sch.exactEstimate r x J)

theorem hintEstimateRows_write (sch : RowScheme) (r : sch.LocalSeed) (x J : Finset ℕ)
    (output row scratchEnd : ℕ) (done : ℕ → Prop) (before after : ℕ → ℕ)
    (hSpace : scratchEnd ≤ output)
    (hPrev : HintEstimateRows sch r x J output done before)
    (hNew : ∀ i : Fin sch.N, (r.1 i).val % sch.m = row →
      after (output + i.val) = hintTruth (i.val ∈ sch.exactEstimate r x J))
    (hFrame : ∀ addr ≥ scratchEnd,
      (∀ i : Fin sch.N, (r.1 i).val % sch.m = row → addr ≠ output + i.val) → after addr = before addr) :
    HintEstimateRows sch r x J output (fun n => done n ∨ n = row) after := by
  intro i hi
  by_cases hRow : (r.1 i).val % sch.m = row
  · exact hNew i hRow
  · have hOld := hi.resolve_right hRow
    rw [hFrame _ (by omega)]
    · exact hPrev i hOld
    · intro k hk h
      exact hRow ((show i = k from Fin.ext (by omega)) ▸ hk)

open HintParams in
theorem hintFinishRow_exact (H : HintParams) (N X Y : ℕ)
    (lr : (H.scheme N X Y).LocalSeed) (j : Fin (H.scheme N X Y).m)
    (x J : Finset ℕ) (start node hints hintMap transcript threshold output descriptor control base : ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState)
    (coords : Fin hints → Fin (H.Nmax N X Y))
    (pre : let S := hintRowWorkspace start (H.ell N X Y) (H.Nmax N X Y) (H.BY N X Y)
                  node j.val (H.ell N X Y) hints
           let F := S.fields (rowLen N (H.rows X Y) j.val) (H.rows X Y)
                  hintMap (transcript + j.val) (H.BX N X Y) (H.BY N X Y) threshold output 0
           HintRowCallPre E S.gauss F coords (lr.2 j) (le_refl _) N S.parent lr.1 J)
    (rec : let S := hintRowWorkspace start (H.ell N X Y) (H.Nmax N X Y) (H.BY N X Y)
                  node j.val (H.ell N X Y) hints
           let F := S.fields (rowLen N (H.rows X Y) j.val) (H.rows X Y)
                  hintMap (transcript + j.val) (H.BX N X Y) (H.BY N X Y) threshold output 0
           HintRowRecord E descriptor S.parent (F.value S.gauss))
    (hDesc : state.regs 6 = descriptor) (hCtx : state.regs 14 = control)
    (hControl : control < 2 ^ E.W)
    (hBits : ∀ i : Fin N, state.mem (hintMap + i.val) = hintTruth (i.val ∈ J))
    (hTranscript : HintTranscriptCorrect (H.scheme N X Y) lr x transcript (fun _ _ => True) state.mem)
    (hBY : H.BY N X Y + 1 < 2 ^ E.W)
    (hTableFit : threshold + (H.BY N X Y + 1) * hints < 2 ^ E.W)
    (hOutFit : output < 2 ^ E.W) (hOutSpan : output + N ≤ 2 ^ E.W)
    (hAt : At P base (hintRunFinal.compile base)) (hPc : state.pc = base) :
    let sch := H.scheme N X Y
    let S := hintRowWorkspace start sch.ℓ (H.Nmax N X Y) (H.BY N X Y) node j.val sch.ℓ hints
    let Nj := rowLen N sch.m j.val
    let r := min (H.BY N X Y) (Nj - hints)
    let budget := (hintFinalBudget S.gauss Nj r + 2) * (r + 1) + hintFinalBudget S.gauss Nj r +
      37 * Nj + 9 * sch.ℓ + 18 * hints + 8 * r + 470
    let scratchEnd := S.gauss.pivotRow + sch.ℓ
    scratchEnd ≤ output →
    Sem P E base (base + hintRunFinal.len) state (fun k out =>
      k ≤ budget ∧ out.regs 14 = control ∧
      HintEstimateRows sch lr x J output (· = j.val) out.mem ∧
      (∀ addr, (addr < start ∨ scratchEnd ≤ addr) →
        (∀ i : Fin N, (lr.1 i).val % sch.m = j.val → addr ≠ output + i.val) →
        out.mem addr = state.mem addr)) := by
  let sch := H.scheme N X Y
  let S := hintRowWorkspace start sch.ℓ (H.Nmax N X Y) (H.BY N X Y) node j.val sch.ℓ hints
  let F := S.fields (rowLen N sch.m j.val) sch.m hintMap (transcript + j.val)
    (H.BX N X Y) (H.BY N X Y) threshold output 0
  let v := fun s : Fin sch.ℓ => sch.code j (lr.2 j) (sch.rowOf lr x j) s
  have hObs (s : Fin S.gauss.rows) :
      state.mem (F.transcriptBase + s.val * F.rowCount) = (v s).val := by
    have h := hTranscript j s trivial
    change state.mem (transcript + j.val + s.val * sch.m) = (v s).val
    rw [Nat.add_right_comm]
    exact h
  have hv : List.ofFn v = sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) sch.ℓ :=
    hintTruePrefix_ofFn sch lr x sch.ℓ (le_refl _) j
  dsimp only
  intro hAfter
  have hRun := hintRunFinal_sem S.gauss F coords v (lr.2 j) (le_refl _) N S.parent descriptor control base
    lr.1 J P E state j rfl pre rec hDesc hCtx hControl hBits hObs hBY hTableFit hOutFit hOutSpan
    hAfter hAt hPc
  apply Sem.mono hRun
  rintro k out ⟨hk, hc, hNew, hFrame⟩
  refine ⟨hk, hc, ?_, ?_⟩
  · intro i hi
    have hb := hNew i hi
    have hEst := hintExactEstimate_mem sch lr x J i j hi
    change out.mem (output + i.val) = _
    change out.mem (output + i.val) = hintTruth ((lr.1 i).val / sch.m ∈
      workerFinal N sch.m sch.ℓ (H.Nmax N X Y) (H.BX N X Y) (H.BY N X Y)
        j (lr.2 j) (sch.rowOf lr J j) (List.ofFn v)) at hb
    rw [hb, hv]
    apply congrArg hintTruth
    exact propext hEst.symm
  · intro addr ha hAway
    apply hFrame addr _ hAway
    change addr < start + 1 - 1 ∨ S.gauss.pivotRow + sch.ℓ ≤ addr
    simpa using ha

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintEstimateRows_write
#print axioms LinearSetReconciliation327.Main.hintFinishRow_exact
end -- Def_LinearSetReconciliation327_Main_HintFinishRowExact20261120

section -- Def_LinearSetReconciliation327_Main_HintPredictRowExact20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def HintPredictedRows (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (s : Fin sch.ℓ) (predictions abstentions done : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ j < min done sch.m,
    mem (predictions + j) = hintTruth (j ∈ sch.exactP lr x J s) ∧
    mem (abstentions + j) = hintTruth (j ∈ sch.exactHint lr x J s)

theorem hintPredictedRows_write (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (s : Fin sch.ℓ) (j : Fin sch.m) (predictions abstentions scratchEnd : ℕ)
    (before after : ℕ → ℕ)
    (hAfterP : scratchEnd ≤ predictions) (hAfterA : scratchEnd ≤ abstentions)
    (hSeparate : predictions + sch.m ≤ abstentions ∨ abstentions + sch.m ≤ predictions)
    (hPrev : HintPredictedRows sch lr x J s predictions abstentions j.val before)
    (hNewP : after (predictions + j.val) = hintTruth (j.val ∈ sch.exactP lr x J s))
    (hNewA : after (abstentions + j.val) = hintTruth (j.val ∈ sch.exactHint lr x J s))
    (hFrame : ∀ a ≥ scratchEnd, a ≠ predictions + j.val → a ≠ abstentions + j.val → after a = before a) :
    HintPredictedRows sch lr x J s predictions abstentions (j.val + 1) after := by
  intro q hq
  by_cases hqj : q = j.val
  · simpa [hqj] using And.intro hNewP hNewA
  have hq' : q < min j.val sch.m := by omega
  obtain ⟨hP, hA⟩ := hPrev q hq'
  rw [hFrame (predictions + q) (by omega) (by omega) (by rcases hSeparate with h | h <;> omega),
    hFrame (abstentions + q) (by omega) (by rcases hSeparate with h | h <;> omega) (by omega)]
  exact ⟨hP, hA⟩

open HintParams in
theorem hintPredictRow_exact_word (H : HintParams) (N X Y : ℕ)
    (lr : (H.scheme N X Y).LocalSeed) (x J : Finset ℕ)
    (j : Fin (H.scheme N X Y).m) (s : Fin (H.scheme N X Y).ℓ)
    (P : Program) (E : RAMEnv) (state : RAMState) (base endPc cost control pred abstain : ℕ)
    (F : (ℕ → ℕ) → Prop)
    (exec : Sem P E base endPc state (fun k out =>
      let sch := H.scheme N X Y
      let v := fun t : Fin s.val =>
        sch.code j (lr.2 j) (sch.rowOf lr x j) ⟨t.val, t.isLt.trans s.isLt⟩
      let ans := workerPredict N sch.m sch.ℓ (H.Nmax N X Y) (H.BX N X Y) (H.BY N X Y)
        (H.c N X Y) j (lr.2 j) (sch.rowOf lr J j) (List.ofFn v)
      k ≤ cost ∧ out.regs 14 = control ∧
      out.mem pred = hintTruth (ans = some 1) ∧ out.mem abstain = hintTruth (ans = none) ∧ F out.mem)) :
    Sem P E base endPc state (fun k out =>
      k ≤ cost ∧ out.regs 14 = control ∧
      out.mem pred = hintTruth (j.val ∈ (H.scheme N X Y).exactP lr x J s) ∧
      out.mem abstain = hintTruth (j.val ∈ (H.scheme N X Y).exactHint lr x J s) ∧ F out.mem) := by
  let sch := H.scheme N X Y
  have hPrefix := hintTruePrefix_ofFn sch lr x s.val s.isLt.le j
  have hPred (b : Option (ZMod 2)) : j.val ∈ sch.rowsWhere (fun a => sch.exactPred lr x J s a = b) ↔
      sch.exactPred lr x J s j = b := HintCanonicalDecode.mem_rowsWhere _ j
  apply Sem.mono exec
  rintro k out ⟨hk, hc, hp, ha, hf⟩
  have hP : j.val ∈ sch.exactP lr x J s ↔ sch.exactPred lr x J s j = some 1 := hPred (some 1)
  have hA : j.val ∈ sch.exactHint lr x J s ↔ sch.exactPred lr x J s j = none := hPred none
  rw [hPrefix] at hp ha
  refine ⟨hk, hc, ?_, ?_, hf⟩
  · change out.mem pred = hintTruth (j.val ∈ sch.exactP lr x J s)
    rw [hP]
    exact hp
  · change out.mem abstain = hintTruth (j.val ∈ sch.exactHint lr x J s)
    rw [hA]
    exact ha

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPredictRow_exact_word
#print axioms LinearSetReconciliation327.Main.hintPredictedRows_write
end -- Def_LinearSetReconciliation327_Main_HintPredictRowExact20261120

section -- Def_LinearSetReconciliation327_Main_HintPredictPlaced20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

def hintPredictCallCost (G : HintGaussArea) (Nj maxR : ℕ) : ℕ :=
  (hintRowOuterBudget G Nj maxR + 2) * (maxR + 1) + 12 * Nj + 9 * G.rows + 390

set_option maxHeartbeats 800000 in
theorem hintPredictPlaced_step (H : HintParams) (L : HintDecoderPlacement)
    (N X Y node seed descriptor base output abstention : ℕ) (j : Fin (H.rows X Y))
    (s : Fin (H.ell N X Y))
    (lr : (H.scheme N X Y).LocalSeed) (x J : Finset ℕ)
    (P : Program) (E : RAMEnv) (state : RAMState)
    (hInfoN : (L.info node).universeSize = N) (hInfoXY : (L.info node).rowParams = some (X, Y))
    (hAt : At P base (hintRunPredict.compile base)) (hPc : state.pc = base)
    (hDesc : state.regs 6 = descriptor) (hCtx : state.regs 14 = L.control)
    (hm : H.rows X Y ≤ N) (hSteps : 0 < H.ell N X Y) (hWord : 30 < 2 ^ E.W)
    (hDescFit : descriptor + 31 ≤ 2 ^ E.W)
    (hControlFit : L.control < 2 ^ E.W) (hSeedFit : seed < 2 ^ E.W)
    (hKFit : H.Nmax N X Y < 2 ^ E.W) (hStepsFit : H.ell N X Y < 2 ^ E.W)
    (hBXFit : H.BX N X Y < 2 ^ E.W) (hBYFit : H.BY N X Y + 1 < 2 ^ E.W)
    (hCoeffSpace : (j.val + 1) * H.ell N X Y * H.Nmax N X Y ≤ 2 ^ E.W)
    (hCoeff : ∀ q : Fin (H.Nmax N X Y), ∀ s : Fin (H.ell N X Y),
      E.coeff seed (j.val * H.ell N X Y * H.Nmax N X Y + q.val + s.val * H.Nmax N X Y) =
        (lr.2 j s q).val)
    (hPerm : ∀ i : Fin N, E.permInv seed i.val = (lr.1.symm i).val)
    (hK : rowLen N (H.rows X Y) j.val ≤ H.Nmax N X Y) :
    let sch := H.scheme N X Y
    let A := L.arena node
    let K := H.Nmax N X Y
    let BY := H.BY N X Y
    let threshold := L.threshold node j.val
    let Nj := rowLen N sch.m j.val
    let h := (hintRowMembers N sch.m j.val lr.1 J).length
    let G := hintRowWorkspace L.rowScratch s.val K BY seed j.val sch.ℓ h
    let scratchEnd := G.gauss.pivotRow + s.val
    let maxR := min BY (Nj - h)
    (hintRowEventBlock H L node seed j.val s.val output abstention).At E descriptor →
    (hintWaitDetBlock K Nj BY sch.ℓ (H.c N X Y)).At E threshold →
    (∀ i : Fin N, state.mem (A.hints + i.val) = hintTruth (i.val ∈ J)) →
    HintTranscriptCorrect sch lr x A.transcript (fun _ col => col.val < s.val) state.mem →
    HintPredictedRows sch lr x J s output abstention j.val state.mem →
    scratchEnd < 2 ^ E.W →
    scratchEnd ≤ A.transcript →
    A.transcript + j.val + s.val * sch.m ≤ 2 ^ E.W →
    A.transcript + sch.ℓ * sch.m ≤ A.hints →
    A.hints + N ≤ 2 ^ E.W →
    scratchEnd ≤ output → scratchEnd ≤ abstention →
    output + sch.m ≤ 2 ^ E.W → abstention + sch.m ≤ 2 ^ E.W →
    (output + sch.m ≤ abstention ∨ abstention + sch.m ≤ output) →
    threshold + (K + 1) * (BY + 1) ≤ 2 ^ E.W →
    Sem P E base (base + hintRunPredict.len) state (fun k out =>
      k ≤ hintPredictCallCost G.gauss Nj maxR ∧ out.regs 14 = L.control ∧
      HintPredictedRows sch lr x J s output abstention (j.val + 1) out.mem ∧
      (∀ a, (a < L.rowScratch ∨ scratchEnd ≤ a) →
        a ≠ output + j.val → a ≠ abstention + j.val → out.mem a = state.mem a)) := by
  let sch := H.scheme N X Y
  let A := L.arena node
  let K := H.Nmax N X Y
  let BY := H.BY N X Y
  let threshold := L.threshold node j.val
  let Nj := rowLen N sch.m j.val
  let h := (hintRowMembers N sch.m j.val lr.1 J).length
  let G := hintRowWorkspace L.rowScratch s.val K BY seed j.val sch.ℓ h
  let Gmax := hintRowWorkspace L.rowScratch s.val K BY seed j.val sch.ℓ K
  let F := Gmax.fields Nj sch.m A.hints (A.transcript + j.val) (H.BX N X Y) BY threshold output abstention
  let scratchEnd := G.gauss.pivotRow + s.val
  let maxR := min BY (Nj - h)
  dsimp only
  intro hRecord hWait hJ hTranscript hPrev hSpace hScratch hReadSpan hTran hHint
    hOutputAfter hAbstainAfter hOutput hAbstain hSeparate hTable
  change scratchEnd < 2 ^ E.W at hSpace
  change scratchEnd ≤ A.transcript at hScratch
  change A.transcript + j.val + s.val * sch.m ≤ 2 ^ E.W at hReadSpan
  change A.transcript + sch.ℓ * sch.m ≤ A.hints at hTran
  change A.hints + N ≤ 2 ^ E.W at hHint
  change output + sch.m ≤ 2 ^ E.W at hOutput
  change abstention + sch.m ≤ 2 ^ E.W at hAbstain
  change output + sch.m ≤ abstention ∨ abstention + sch.m ≤ output at hSeparate
  change threshold + (K + 1) * (BY + 1) ≤ 2 ^ E.W at hTable
  change Nj ≤ K at hK
  have hSpaceMax : Gmax.gauss.pivotRow + s.val < 2 ^ E.W := hSpace
  have hPn : Gmax.parent + 30 ≤ scratchEnd :=
    (hintRowWorkspace_addresses L.rowScratch s.val K BY seed j.val sch.ℓ K Nj 0
      s.isLt.le le_rfl hK (Nat.zero_le _)).2.2.2.2.2.2.2
  have hRow : j.val < sch.m := j.isLt
  have hOutputFit : output < 2 ^ E.W := by omega
  have hAbstainFit : abstention < 2 ^ E.W := by omega
  have hNfit : N < 2 ^ E.W := by
    have hp : 0 < A.hints := by omega
    omega
  have hLen : h ≤ Nj := by
    simpa only [h, Nj, hintRowMembers] using
      hintGatherList_length_le (fun q => decide (q ∈ rowImage N sch.m lr.1 j.val J)) Nj
  have hWaitRead := hintWaitDetBlock_read E K Nj BY sch.ℓ (H.c N X Y) threshold
    h maxR hWait hTable (hLen.trans hK) (Nat.min_le_left _ _)
  have hAtBlock : (hintRowDetBlock Gmax.parent (F.value Gmax.gauss)).At E descriptor := by
    unfold hintRowEventBlock at hRecord
    simp only [hInfoN, hInfoXY, Option.getD_some] at hRecord
    exact hRecord
  have hHintAfter : Gmax.parent + 30 ≤ A.hints := by omega
  have hTranscriptAfter : Gmax.parent + 30 ≤ A.transcript + j.val := by omega
  have hParentFit : Gmax.parent + 30 ≤ 2 ^ E.W := by omega
  obtain ⟨coords, hPre⟩ := hintRowWorkspace_callPre E L.rowScratch s.val K BY seed j.val sch.ℓ
    N sch.m A.hints (A.transcript + j.val) (H.BX N X Y) threshold output abstention lr.1 J (lr.2 j)
    s.isLt.le hSteps j.isLt hm hK hKFit hSeedFit hStepsFit hSpaceMax
    hHintAfter (by omega) hTranscriptAfter hReadSpan hCoeffSpace (fun q t => hCoeff q ⟨t.val, t.isLt.trans s.isLt⟩) hPerm
  have hFits : ∀ i < 30, F.value Gmax.gauss i < 2 ^ E.W := by
    intro i hi
    have hHead := hintRowWorkspace_headerFits E L.rowScratch s.val K BY seed j.val sch.ℓ K le_rfl
      s.isLt.le hKFit hSeedFit (j.isLt.trans (hm.trans_lt hNfit)) hStepsFit hSpaceMax
    by_cases hi' : 16 ≤ i
    · by_cases h17 : i = 17
      · simpa only [HintRowFields.value, if_pos hi', if_pos h17] using Nat.two_pow_pos E.W
      · simpa only [HintRowFields.value, if_pos hi', if_neg h17] using hHead.values (i - 16) (by omega)
    have hi16 : i < 16 := by omega
    have hOutside : Gmax.outside < 2 ^ E.W := by
      dsimp only [Gmax, hintRowWorkspace, hintGaussDenseArea] at hSpaceMax ⊢
      omega
    have hBitmap : Gmax.bitmap < 2 ^ E.W := by
      dsimp only [Gmax, hintRowWorkspace, hintGaussDenseArea] at hSpaceMax ⊢
      omega
    have hMfit : sch.m < 2 ^ E.W := by
      change H.rows X Y < 2 ^ E.W
      omega
    have hNjFit : Nj < 2 ^ E.W := hK.trans_lt hKFit
    have hTfit : A.transcript + j.val < 2 ^ E.W := by
      have hSteps' : 0 < sch.ℓ := hSteps
      have hProduct : sch.m ≤ sch.ℓ * sch.m := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right sch.m (Nat.succ_le_of_lt hSteps')
      omega
    have hHintFit : A.hints < 2 ^ E.W := by omega
    have hThreshFit : threshold < 2 ^ E.W := by omega
    have hBYsmall : BY < 2 ^ E.W := by
      dsimp only [BY]
      omega
    have hZero := Nat.two_pow_pos E.W
    simp only [HintRowFields.value, if_neg hi']
    interval_cases i <;>
      first
      | exact hOutside
      | exact hBitmap
      | exact hNjFit
      | exact hTfit
      | exact hMfit
      | exact hHintFit
      | exact hThreshFit
      | exact hOutputFit
      | exact hAbstainFit
      | exact hBYsmall
      | exact hBXFit
      | exact hZero
  have hRec := hintRowWorkspace_record E descriptor L.rowScratch s.val K BY seed j.val sch.ℓ h F
    hAtBlock hWord hDescFit hParentFit hFits
  let v : HintVec s.val := fun a =>
    sch.code j (lr.2 j) (sch.rowOf lr x j) ⟨a.val, a.isLt.trans s.isLt⟩
  have hObs (a : Fin s.val) :
      state.mem (A.transcript + j.val + a.val * sch.m) = (v a).val := by
    rw [Nat.add_right_comm]
    exact hTranscript j ⟨a.val, a.isLt.trans s.isLt⟩ a.isLt
  have hNext (hs : s.val < sch.ℓ) (q : Fin K) :
      E.coeff seed ((j.val * sch.ℓ + s.val) * K + q.val) = (lr.2 j ⟨s.val, hs⟩ q).val := by
    rw [Nat.add_mul, Nat.add_right_comm]
    exact hCoeff q s
  have hDistinct : output + j.val ≠ abstention + j.val := by
    rcases hSeparate with h | h <;> omega
  have hRun := hintRunPredict_sem G.gauss F coords v (lr.2 j) s.isLt.le N G.parent
    descriptor L.control base (H.c N X Y) lr.1 J P E state j rfl hPre hRec hDesc hCtx
    hControlFit hJ hObs hBYFit hWaitRead.1 hWaitRead.2 hNext
    (show output + j.val < 2 ^ E.W by omega) (show abstention + j.val < 2 ^ E.W by omega)
    hOutputAfter hAbstainAfter hDistinct hAt hPc
  let frame : (ℕ → ℕ) → Prop := fun mem =>
    ∀ a, (a < L.rowScratch ∨ scratchEnd ≤ a) →
      a ≠ output + j.val → a ≠ abstention + j.val → mem a = state.mem a
  have hPred := hintPredictRow_exact_word H N X Y lr x J j s P E state base
    (base + hintRunPredict.len) (hintPredictCallCost G.gauss Nj maxR) L.control
    (output + j.val) (abstention + j.val) frame (by
      apply Sem.mono hRun
      rintro k out ⟨hk, hc, hp, hb, hf⟩
      refine ⟨hk, hc, hp, hb, ?_⟩
      intro a ha hp ht
      apply hf a _ hp ht
      change a < L.rowScratch + 1 - 1 ∨ scratchEnd ≤ a
      simpa only [Nat.add_sub_cancel] using ha)
  apply Sem.mono hPred
  rintro k out ⟨hk, hc, hp, ha, hf⟩
  exact ⟨hk, hc, hintPredictedRows_write sch lr x J s j output abstention scratchEnd state.mem out.mem
    hOutputAfter hAbstainAfter hSeparate hPrev hp ha (fun a hs => hf a (Or.inr hs)), hf⟩

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintPredictPlaced_step
end -- Def_LinearSetReconciliation327_Main_HintPredictPlaced20261120


