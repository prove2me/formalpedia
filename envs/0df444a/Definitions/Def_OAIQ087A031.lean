-- Prove2me | Definitions.Def_OAIQ087A031
-- name    : OAIQ087A031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T17:46:50.570202+00:00
-- url     : https://prove2.me/theorems/161635d8-b1d2-4c89-a30b-661e63b1cf4b
-- title:
--   Definitions bundle OAIQ087A031 of the split of OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.OptimalMaxCut.main`, carved from OpenAI's openai/math development (OpenAI, *A Direct Proof of Optimal Max-Cut Hardness (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 206 declarations of OpenAI's Lean: 66 definitions and 140 theorems. The definitions and types are `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody.preSteps`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerBodyBounds.timePolynomial`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Header.computeTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Header.dartTotal`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Header.emitTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Header.headerBits`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Header.paddingTotal`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Header.program`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Header.readTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Header.totalTime`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Header.vertexTotal`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.headerOutput`, `OAI.MaxCutGames.Foundations.Complexity.MachineRegularTable.Top.ownerLoopPolynomial`, `OAI.MaxCutGames.Foundations.Complexity.PoweringInitializeFrame.initialExtra`, `OAI.MaxCutGames.Foundations.Complexity.PoweringInitializeFrame.initializeInTime`, `OAI.MaxCutGames.Foundations.Complexity.PoweringInitializeFrame.preparedCfg`, `OAI.MaxCutGames.Foundations.Complexity.PoweringInitializeFrame.preparedTapes`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineEqualityField.instruction`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineField.instruction`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineFinish.steps`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.machine`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.program`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineOuterLoop.loopInTime`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachinePlan.instruction`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineRelation.instruction`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineRelationField.instruction`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineRotor.instruction`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineRowBody.budget`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineRowBody.instruction`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineRowHeaders.instruction`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineRuntime.beforeFinish`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineVertex.budget`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineVertex.instruction`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineVertex.sequenceInstruction`, `OAI.MaxCutGames.Foundations.Complexity.PoweringMachineWord.instruction`, `OAI.MaxCutGames.Foundations.Complexity.PoweringPlanBudget.rowBudget`, `OAI.MaxCutGames.Foundations.Complexity.PoweringPolynomialBudget.rowTime`, `OAI.MaxCutGames.Foundations.Complexity.PoweringPolynomialBudget.vertexTime`, `OAI.MaxCutGames.Foundations.Hastad.SourceContextPrepare.preparationConfiguration`, `OAI.MaxCutGames.Foundations.Hastad.SourceContextPrepare.program` and 26 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MaxCut_Encoding_InputData`, `MaxCut_Estimates_Basic`, `MaxCut_Games_PoweringInitializeFrame`, `MaxCut_Games_PoweringMasterState`, `MaxCut_Games_PoweringPlanBudget`, `MaxCut_Games_PoweringPolynomialBudget`, `MaxCut_Machines_MachineRegularOwnerProgram`, `MaxCut_Machines_MachineRegularTableTrace`, `MaxCut_Machines_PoweringMachineField`, `MaxCut_Machines_PoweringMachineGlobal`, `MaxCut_Machines_PoweringMachineRelation`, `MaxCut_Machines_PoweringMachineRotor`, `MaxCut_Machines_PoweringMachineRowHeaders`, `MaxCut_Machines_PoweringMachineRuntime`, `MaxCut_Machines_PoweringMachineVertex`, `MaxCut_Machines_RawInitialMachineBudget`, `MaxCut_Machines_RawInitialMachineCleanup`, `MaxCut_Machines_RawInitialMachineModel`, `MaxCut_PCP_ContextPrepare`, `MaxCut_PCP_PoweringRowData`, `MaxCut_PCP_PreprocessingPaddingWords`, `MaxCut_PCP_PreprocessingRegularBounds`, `MaxCut_PCP_PreprocessingStageMaps`, `MaxCut_PCP_RawInitialPredicate`, `MaxCut_PCP_RawInitialTables`, `MaxCut_PCP_TableIteration`.
--
--   **Imports.** It imports the bundles `OAIQ087A021`, `OAIQ087A023`, `OAIQ087A024`, `OAIQ087A025` and `OAIQ087A026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ087A033` and `OAIQ087A034`; the proof of `OAI.OptimalMaxCut.LongCode.InstanceAdapter.exists_encoded_gridComputer`.
-- source:
--   OpenAI, A Direct Proof of Optimal Max-Cut Hardness (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-Direct-Proof-of-Optimal-Max-Cut-Hardness-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ087A021
import Definitions.Def_OAIQ087A023
import Definitions.Def_OAIQ087A024
import Definitions.Def_OAIQ087A025
import Definitions.Def_OAIQ087A026

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_ContextPrepare
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Hastad.SourceContextPrepare

open Turing MaxCutGames.Foundations.Complexity
open Target PCP SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge

variable {u : Nat} {Extra τ : Type}

def program : Label u → TM2.Stmt (fun _ : Arena u Extra => Bool) (Label u) (State u τ)
  | .inl l => MachineStateFrame.statement Sum.inl (some (.inr (prepareEntry u)))
      (SourceContextLoad.program l)
  | .inr l => MachineControl.statement id (stateSwap u τ)
      (MachineStateFrame.statement Sum.inr none (SourceSignaturePrepare.program l))

def preparationConfiguration (loaderState : LoadState)
    (c : TM2.Cfg (fun _ : Arena u Extra => Bool) (SourceSignaturePrepare.Label u) (PrepareState u τ)) :
    TM2.Cfg (fun _ : Arena u Extra => Bool) (Label u) (State u τ) :=
  MachineControl.configuration id (stateSwap u τ)
    (MachineStateFrame.configuration Sum.inr none loaderState c)

end MaxCutGames.Foundations.Hastad.SourceContextPrepare

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingPaddingWords
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exact serialization of whole-vertex padding

The original dart rows remain in their original order, with every old tail,
reverse index, and relation bit unchanged. The suffix is exactly the bit stream
emitted by the checked dummy-vertex machine, starting at vertex `n` and dart
`n*d`. This is an equality for the actual table codec, with no runtime premise.
-/

/-!
# Complete serialization of the actual regularized table

Each global vertex emits its internal ports in increasing order, then its
inherited port. Original darts are the first global vertices. Dummy vertices
follow in increasing owner and local-dummy order. These are identities for the
actual stored rows and existing codec, with arbitrary actual cloud tables.
-/

namespace MaxCutGames.Foundations.PCP.PreprocessingRegularWords

open DegreeReplacement PreprocessingCloudIndex PreprocessingRegularTables Complexity
open scoped BigOperators

variable (t : GraphTables.Table) (padding : Fin t.vertices → Nat) {q : Nat}
variable (tables : ∀ v, ExpanderTables.Table (cloudSize t v + padding v) q)

/-- The inherited dummy row is an always-accepting self-loop. -/
theorem inherited_dummy_words (v : Fin t.vertices) (j : Fin (padding v)) :
    GraphTables.rowWords (actualRow t padding tables (.inr ⟨v, j⟩) (.inr ())) =
      [t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val,
        (q + 1) * (t.darts + PreprocessingPaddingOffsets.offset padding v.val + j.val) + q] ++
        GraphTables.relationWords MachineDummyRows.trueRelation := by
  simp only [GraphTables.rowWords, actualRow_tail,
    PreprocessingPaddingOffsets.vertexOrder_dummy_val,
    inherited_dummy_reverse, inherited_dummy_relation]

/-- The explicit padding list is the inverse enumeration of its numeric order. -/
theorem paddingOrder_ofFn :
    List.ofFn (paddingOrder padding).symm = paddingList padding := by
  calc
    List.ofFn (paddingOrder padding).symm =
        List.ofFn (fun i : Fin (paddingList padding).length =>
          (paddingOrder padding).symm (Fin.cast (paddingList_length padding) i)) :=
      List.ofFn_congr (paddingList_length padding).symm (paddingOrder padding).symm
    _ = paddingList padding := by
      change List.ofFn (fun i => (paddingList padding).get i) = _
      exact List.ofFn_get _

/-- Any global-vertex payload follows old darts, then the explicit dummy list. -/
theorem vertexOrder_ofFn {α : Type*} (f : Vertex t padding → α) :
    List.ofFn (fun i : Fin (vertexCount t padding) => f ((vertexOrder t padding).symm i)) =
      List.ofFn (fun e : Fin t.darts => f (.inl e)) ++
        (paddingList padding).map (fun z => f (.inr z)) := by
  change List.ofFn (fun i : Fin (t.darts + ∑ v, padding v) =>
    f ((vertexOrder t padding).symm i)) = _
  rw [List.ofFn_add]
  have hold (e : Fin t.darts) :
      (vertexOrder t padding).symm (e.castLE (Nat.le_add_right t.darts (∑ v, padding v))) =
        Sum.inl e := (vertexOrder t padding).symm_apply_apply (Sum.inl e)
  have hnew (i : Fin (∑ v, padding v)) :
      (vertexOrder t padding).symm (i.natAdd t.darts) =
        Sum.inr ((paddingOrder padding).symm i) := by
    apply (vertexOrder t padding).injective
    erw [Equiv.apply_symm_apply]
    change i.natAdd t.darts = Fin.natAdd t.darts
      ((paddingOrder padding) ((paddingOrder padding).symm i))
    rw [Equiv.apply_symm_apply]
  have oldPart := congrArg List.ofFn
    (funext (fun e => congrArg f (hold e)))
  have newPart := congrArg List.ofFn
    (funext (fun i => congrArg f (hnew i)))
  erw [oldPart, newPart]
  congr 1
  calc
    List.ofFn (fun i => f (.inr ((paddingOrder padding).symm i))) =
        (List.ofFn (paddingOrder padding).symm).map (fun z => f (.inr z)) :=
      (List.map_ofFn (f := (paddingOrder padding).symm) (g := fun z => f (.inr z))).symm
    _ = _ := by rw [paddingOrder_ofFn]

/-- The stored dummy list uses exactly the nested owner/local-index loop order. -/
theorem paddingList_flatMap {α : Type*} (f : (Σ v : Fin t.vertices, Fin (padding v)) → List α) :
    (paddingList padding).flatMap f =
      (List.ofFn (fun v : Fin t.vertices =>
        (List.ofFn (fun j : Fin (padding v) => f ⟨v, j⟩)).flatten)).flatten := by
  simp only [paddingList, List.sigma, List.finRange, List.flatMap_def,
    List.map_flatten, List.flatten_flatten, List.map_ofFn, Function.comp_def]

end MaxCutGames.Foundations.PCP.PreprocessingRegularWords

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularOwnerProgram
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual dummy-owner body of regularization

The owner is a physically stored unary index. The code computes its cloud
metadata, initializes local index and fuel, skips the family computation when
padding is zero, and otherwise generates one rotor for all dummy vertices of
this owner. Each vertex iteration consumes one fuel bit and increments both
physical vertex indices. The final checked addition and cleanup leave only the
updated global index, prefix, and accumulated output.
-/

/-! Actual execution and exact runtime of the fixed dummy-owner program. -/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody

open Turing MachineComposition PCP
open PreprocessingCloudIndex PreprocessingRegularTables
open MachineRegularTable PreprocessingRegularLoopWords

def preSteps (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  MachineCloudPadding.totalTime t v + (2 * (cloudSize t v + 1) + 1) +
    (2 * (padding t v + 1) + 1)

end MaxCutGames.Foundations.Complexity.MachineRegularOwnerBody

/-! Bounds on actual metadata, stored rotor words, and emitted prefixes. These
are size estimates used inside separately proved machine executions. -/
namespace MaxCutGames.Foundations.PCP.PreprocessingMachineBounds
open PreprocessingRegularTables PreprocessingCloudIndex
open MaxCutGames.Foundations.Complexity
open scoped BigOperators

theorem tableBits_le_of_counts (t : GraphTables.Table) (a b L : Nat)
    (hv : t.vertices ≤ a * L) (he : t.darts ≤ b * L) :
    (GraphTables.tableBits t).length ≤ (tablePolynomial a b).eval L := by
  have hsum := Nat.add_le_add hv he
  have hprod := Nat.mul_le_mul he (Nat.add_le_add_right hsum 8192)
  have h := (GraphTables.tableBits_length_le t).trans
    (Nat.add_le_add (Nat.add_le_add_right hsum 2) hprod)
  simpa only [tablePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] using h

end MaxCutGames.Foundations.PCP.PreprocessingMachineBounds

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Estimates_Basic
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual regular-table construction

The header subroutine reads the two original graph headers, computes the
padding total by the actual prefix machine, performs unary addition and
constant multiplication, and appends both resulting header fields. The
outer vertex routines are assembled from actual metadata and row programs.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularTable

open Turing MachineComposition
open MaxCutGames.Foundations.PCP

namespace Header

variable {σ : Type}

def program (q : Nat) : Label → TM2.Stmt Alphabet Label (State σ)
  | .init => .push indexTape (fun _ => false) (.goto fun _ => .lookup .vertices (.run .copyFirst))
  | .seedM => .push indexTape (fun _ => true) (.goto fun _ => .lookup .darts (.run .copyFirst))
  | .clearIndex => .pop indexTape (fun state _ => (state.1, none))
      (.goto fun _ => .prefix .init)
  | .lookup field l => MachinePreservingLookupClean.statement (lookupSlots field)
      (Label.lookup field) (some (fieldExit field)) l
  | .prefix l => MachineCloudPadding.Placement.statement Sum.inl Label.prefix
      (some (.copyFirst .count)) (MachineCloudPrefix.program l)
  | .copyFirst phase => Reduction.MachineTransfer.loopAt (copySource phase) scratchTape
      id false (.copyFirst phase) (some (.copySecond phase))
  | .copySecond phase => MachineCopy.forkLoop scratchTape (copySource phase) (copyDestination phase)
      false (.copySecond phase) (some (copyExit phase))
  | .add => MachineUnaryAddAt.loop sumTape verticesTape .add (some .scaleSeed)
  | .scaleSeed => MachineUnaryAffineAt.seed dartsTape 0 .scaleScan
  | .scaleScan => MachineUnaryAffineAt.scan verticesTape scratchTape dartsTape (q + 1)
      .scaleScan .scaleRestore
  | .scaleRestore => Reduction.MachineTransfer.loopAt scratchTape verticesTape id false
      .scaleRestore (some (.copyFirst .rEmit))
  | .appendFirst => Reduction.MachineTransfer.loopAt outputTape scratchTape id false
      .appendFirst (some .appendSecond)
  | .appendSecond => Reduction.MachineTransfer.loopAt emitTape scratchTape id false
      .appendSecond (some .appendThird)
  | .appendThird => Reduction.MachineTransfer.loopAt scratchTape outputTape id false
      .appendThird (some .cleanupZeros)
  | .cleanupZeros => .pop sumTape (fun state _ => (state.1, none))
      (.pop fuelTape (fun state _ => (state.1, none)) (.goto fun _ => .clearQuery))
  | .clearQuery => MachineLookup.discard queryTape .clearQuery .done
  | .done => .halt

def paddingTotal (t : GraphTables.Table) : Nat :=
  PreprocessingPaddingOffsets.offset (PreprocessingRegularTables.padding t) t.vertices

def vertexTotal (t : GraphTables.Table) : Nat :=
  PreprocessingRegularTables.vertexCount t (PreprocessingRegularTables.padding t)

def dartTotal (q : Nat) (t : GraphTables.Table) : Nat := vertexTotal t * (q + 1)

theorem vertexTotal_eq (t : GraphTables.Table) :
    vertexTotal t = t.darts + paddingTotal t := by
  unfold vertexTotal PreprocessingRegularTables.vertexCount paddingTotal
  rw [PreprocessingPaddingOffsets.offset_all]

theorem initStep (q : Nat) (table output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .init, ((ambient, false), register),
        frame table [] [] [] [] [] [] [] [] [] [] [] output⟩ =
      some ⟨some (.lookup .vertices (.run .copyFirst)), ((ambient, false), register),
        frame table [] [] [] [] [] (encodeWord 0) [] [] [] [] [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

theorem seedMStep (q : Nat) (table n output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .seedM, ((ambient, false), register),
        frame table n [] [] [] [] (encodeWord 0) [] [] [] [] [] output⟩ =
      some ⟨some (.lookup .darts (.run .copyFirst)), ((ambient, false), register),
        frame table n [] [] [] [] (encodeWord 1) [] [] [] [] [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

theorem clearIndexStep (q : Nat) (table n m output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .clearIndex, ((ambient, false), register),
        frame table n [] [] [] m (encodeWord 0) [] [] [] [] [] output⟩ =
      some ⟨some (.prefix .init), ((ambient, false), none),
        frame table n [] [] [] m [] [] [] [] [] [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

def readTime (t : GraphTables.Table) : Nat :=
  1 + MachinePreservingLookupClean.steps (GraphTables.tableWords t) 0 + 1 +
    MachinePreservingLookupClean.steps (GraphTables.tableWords t) 1 + 1

/-- The original vertex count is the physical bound supplied to the checked
padding-prefix machine. Its complement tapes preserve the original dart count. -/
theorem prefixTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[MachineCloudPrefix.totalTime t t.vertices []]
      (some ⟨some (.prefix .init), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] []
          (encodeWord t.darts) [] [] [] [] [] [] output⟩) =
      some ⟨some (.copyFirst .count), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
          [] [] [] [] [] [] output⟩ := by
  have h := MachineCloudPadding.Placement.trace Sum.inl prefixView prefixView_left prefixView_right
    Label.prefix (some (Label.copyFirst .count))
    (frame [] [] [] [] [] (encodeWord t.darts) [] [] [] [] [] [] output)
    (MachineCloudPrefix.program (σ := σ)) (program q) (fun _ => rfl) _ _ _
    (MachineCloudPrefix.prefixTrace t t.vertices (Nat.le_refl _) [] ambient register)
  simpa only [MachineCloudPadding.Placement.configuration, MachineCloudPadding.Placement.label,
    prefixTapes, frame_m, frame_index, frame_work, frame_scratch, frame_vertices, frame_darts,
    frame_emit, frame_output, List.append_nil, paddingTotal, frame, memory,
    mTape, indexTape, workTape, scratchTape, verticesTape, dartsTape, emitTape, outputTape] using h

def computeTime (t : GraphTables.Table) : Nat :=
  (2 * (t.darts + 2) + (paddingTotal t + 1)) + (2 * (vertexTotal t + 1) + 1)

theorem computeTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[computeTime t]
      (some ⟨some (.copyFirst .count), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
          [] [] [] [] [] [] output⟩) =
      some ⟨some (.copyFirst .rEmit), ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output⟩ := by
  have hc := MachineCopy.copyTrace mTape verticesTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .count) (Label.copySecond .count) (some Label.add)
    (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
      [] [] [] [] [] [] output) rfl (ambient, false) register
  simp only [frame_m, frame_vertices, encodeWord_length, List.append_nil, update_frame_vertices] at hc
  have ha := MachineUnaryAddAt.addFromTapes sumTape verticesTape (by decide)
    Label.add (some Label.scaleSeed) (program q) rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord (paddingTotal t)) (encodeWord t.darts)
      [] [] [] (encodeWord t.darts) [] [] output)
    (paddingTotal t) t.darts [] [] (by simp) (by simp) (ambient, false) none
  simp only [MachineUnaryAddAt.unaryTapes, Reduction.MachineTransfer.tapesAt,
    List.append_nil, update_frame_sum, update_frame_vertices] at ha
  rw [show paddingTotal t + t.darts = vertexTotal t by rw [vertexTotal_eq]; omega] at ha
  have hm := MachineUnaryAffineAt.seededAffineTrace verticesTape scratchTape dartsTape
    (by decide) (by decide) (by decide) (q + 1) 0 Label.scaleSeed Label.scaleScan
    Label.scaleRestore (some (Label.copyFirst .rEmit)) (program q) rfl rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
      [] [] [] (encodeWord (vertexTotal t)) [] [] output)
    (vertexTotal t) [] (by simp) rfl (ambient, false) none
  simp only [frame_darts, List.append_nil, Nat.add_zero, update_frame_darts] at hm
  rw [show (q + 1) * vertexTotal t = dartTotal q t by unfold dartTotal; ac_rfl] at hm
  exact appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ hc ha) hm

def headerBits (q : Nat) (t : GraphTables.Table) : List Bool :=
  encodeWords [vertexTotal t, dartTotal q t]

theorem headerBits_eq (q : Nat) (t : GraphTables.Table) :
    headerBits q t = encodeWord (vertexTotal t) ++ encodeWord (dartTotal q t) := by
  simp only [headerBits, encodeWords, List.append_nil]

theorem headerBits_length (q : Nat) (t : GraphTables.Table) :
    (headerBits q t).length = vertexTotal t + dartTotal q t + 2 := by
  rw [headerBits_eq]
  simp only [List.length_append, encodeWord_length]
  omega

theorem cleanupZerosStep (q : Nat) (table n m N R output : List Bool) (ambient : σ)
    (register : Option Bool) :
    TM2.step (program q)
      ⟨some .cleanupZeros, ((ambient, false), register),
        frame table n n (encodeWord 0) (encodeWord 0) m [] [] [] N R [] output⟩ =
      some ⟨some .clearQuery, ((ambient, false), none),
        frame table n n [] [] m [] [] [] N R [] output⟩ := by
  simp [TM2.step, program, TM2.stepAux, encodeWord]

def emitTime (q : Nat) (t : GraphTables.Table) (output : List Bool) : Nat :=
  (((2 * (dartTotal q t + 2) + 2 * (vertexTotal t + 2)) +
    (2 * ((headerBits q t).length + output.length) + 3)) + 1) + (t.vertices + 1) + 1

theorem emitTrace (q : Nat) (t : GraphTables.Table) (output : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step (program q)))^[emitTime q t output]
      (some ⟨some (.copyFirst .rEmit), ((ambient, false), register),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ := by
  have hr := MachineCopy.copyTrace dartsTape emitTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .rEmit) (Label.copySecond .rEmit)
    (some (Label.copyFirst .nEmit)) (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] output)
    rfl (ambient, false) register
  simp only [frame_darts, frame_emit, encodeWord_length, List.append_nil, update_frame_emit] at hr
  have hn := MachineCopy.copyTrace verticesTape emitTape scratchTape (by decide) (by decide)
    (by decide) false (Label.copyFirst .nEmit) (Label.copySecond .nEmit)
    (some Label.appendFirst) (program q) rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) (encodeWord (dartTotal q t)) output)
    rfl (ambient, false) none
  simp only [frame_vertices, frame_emit, encodeWord_length, update_frame_emit, ← headerBits_eq] at hn
  have ha := MachineAppendAt.appendTrace emitTape outputTape scratchTape
    (by decide) (by decide) (by decide) false Label.appendFirst Label.appendSecond Label.appendThird
    (some Label.cleanupZeros) (program q) rfl rfl rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
      (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) (headerBits q t) output)
    rfl (ambient, false) none
  simp only [frame_emit, frame_output, MachineAppendAt.appendTapes,
    Reduction.MachineTransfer.tapesAt, update_frame_emit, update_frame_output] at ha
  have hz : (advance (TM2.step (program q)))^[1]
      (some ⟨some .cleanupZeros, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          (encodeWord 0) (encodeWord 0) (encodeWord t.darts) [] [] []
          (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) [] (output ++ headerBits q t)⟩) =
      some ⟨some .clearQuery, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
          [] [] (encodeWord t.darts) [] [] [] (encodeWord (vertexTotal t))
          (encodeWord (dartTotal q t)) [] (output ++ headerBits q t)⟩ :=
    cleanupZerosStep q _ _ _ _ _ _ ambient none
  have hc := MachineLookup.discardTrace queryTape Label.clearQuery Label.done (program q) rfl
    (frame (GraphTables.tableBits t) (encodeWord t.vertices) (encodeWord t.vertices)
      [] [] (encodeWord t.darts) [] [] [] (encodeWord (vertexTotal t))
      (encodeWord (dartTotal q t)) [] (output ++ headerBits q t))
    t.vertices [] (by simp) (ambient, false) none
  simp only [update_frame_query] at hc
  have hd : (advance (TM2.step (program q)))^[1]
      (some ⟨some .done, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩) =
      some ⟨none, ((ambient, false), none),
        frame (GraphTables.tableBits t) (encodeWord t.vertices) [] [] [] (encodeWord t.darts)
          [] [] [] (encodeWord (vertexTotal t)) (encodeWord (dartTotal q t)) []
          (output ++ headerBits q t)⟩ := rfl
  exact appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ (appendTrace_inline_MachineRegularTable _ hr hn) ha) hz) hc) hd

def totalTime (q : Nat) (t : GraphTables.Table) (output : List Bool) : Nat :=
  ((readTime t + MachineCloudPrefix.totalTime t t.vertices []) + computeTime t) + emitTime q t output

end Header

end MaxCutGames.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingRegularBounds
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual output prefixes used by the regularization loops.
The bounds include the stored headers and all earlier original/owner blocks.
They concern actual serialized words; machine executions are proved separately. -/
namespace MaxCutGames.Foundations.PCP.PreprocessingRegularBounds

open PreprocessingRegularTables PreprocessingRegularWords PreprocessingRegularLoopWords
open MaxCutGames.Foundations.Complexity
open scoped BigOperators

theorem offset_succ {n : Nat} (p : Fin n → Nat) (k : Nat) (h : k < n) :
    PreprocessingPaddingOffsets.offset p (k + 1) =
      PreprocessingPaddingOffsets.offset p k + p ⟨k, h⟩ := by
  unfold PreprocessingPaddingOffsets.offset
  rw [List.take_succ_eq_append_getElem (show k < (List.finRange n).length by simpa using h)]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero, List.finRange, List.getElem_ofFn]

def header (t : GraphTables.Table) (p : Fin t.vertices → Nat) (q : Nat) : List Bool :=
  encodeWords [vertexCount t p, vertexCount t p * (q + 1)]

end MaxCutGames.Foundations.PCP.PreprocessingRegularBounds

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Encoding_InputData
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.MachineRegularTable
open Turing MachineComposition
open MaxCutGames.Foundations.PCP

namespace Top

def headerOutput (t : GraphTables.Table) : List Bool :=
  Header.headerBits PreprocessingRegularTables.internalDegree t

end Top

end MaxCutGames.Foundations.Complexity.MachineRegularTable

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_PoweringMasterState
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit common-register layout for the powering machine. The header,
word and affine routines use the trailing optional-bit register directly.
Comparison reassociates the finite registers; row evaluation moves the fixed
buffer to the final component. The row adapter below proves an actual step
of the caller's mixed program, rather than requiring that the entire program
be a translated copy of the row routine. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMasterState

open Turing
open MachineFixedBlockMap

section Row

variable {K Λ : Type} [DecidableEq K] {N M : Nat}

/-- Exact caller-program step, with no hypothesis about its other labels. -/
theorem step_encodedBlockAt (src dst : K) (F : Buffer N → Buffer M) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (Master N))
    (label : Λ) (atLabel : program label = encodedBlockAt src dst F exit)
    (hne : src ≠ dst) (bits : Buffer N) (suffix : List Bool)
    (state : Master N) (tapes : K → List Bool)
    (hinput : tapes src = PoweringMachineRow.encodeBits (List.ofFn bits) ++ suffix) :
    TM2.step program ⟨some label, state, tapes⟩ =
      some ⟨exit, clearBuffer state,
        Function.update (Function.update tapes src suffix) dst
          (PoweringMachineRow.encodeBits (List.ofFn (F bits)) ++ tapes dst)⟩ := by
  simp only [TM2.step, atLabel, stepAux_encodedBlockAt src dst F exit hne bits suffix state tapes hinput]

/-- The producer's clean finite controls and any previous buffer contents
become the completely clean master state after one genuine row transition. -/
theorem step_rowAt_clean {t S q : Nat} (src dst : K)
    (labelAt : Fin q → Fin S → PCP.GraphTables.Label) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ
      (Master (PoweringMachineRow.inputSize t S)))
    (label : Λ) (atLabel : program label = rowAt (t := t) src dst labelAt exit)
    (hne : src ≠ dst) (bits register : Buffer (PoweringMachineRow.inputSize t S))
    (suffix : List Bool) (tapes : K → List Bool)
    (hinput : tapes src = PoweringMachineRow.encodeBits (List.ofFn bits) ++ suffix) :
    TM2.step program ⟨some label, withBuffer register, tapes⟩ =
      some ⟨exit, clean (PoweringMachineRow.inputSize t S),
        Function.update (Function.update tapes src suffix) dst
          (PoweringMachineRow.encodeBits (List.ofFn (PoweringMachineRow.rowBlock labelAt bits)) ++
            tapes dst)⟩ := by
  simpa only [rowAt, clearBuffer_withBuffer] using
    step_encodedBlockAt src dst (PoweringMachineRow.rowBlock labelAt) exit
      program label atLabel hne bits suffix (withBuffer register) tapes hinput

end Row

end MaxCutGames.Foundations.Complexity.PoweringMasterState

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineRotor
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A rotor step on the live unary port-table encoding. First read the reverse
dart identifier; then read that dart's tail vertex. This uses no division or
runtime graph data in finite control. Both positional selections are proved
from the actual serialization. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRotor

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

def instruction (tape : Fin 7 → K) (degree port : Nat)
    (labels : Label → Λ) (exit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .reverse l => MachineAffineLookup.instruction (tape 1) (reverseTapes tape)
      (4098 * degree) (4098 * port + 3) (fun q => labels (.reverse q))
      (some (labels (.endpoint .seed))) l
  | .endpoint l => MachineAffineLookup.instruction (tape 4) (endpointTapes tape)
      4098 2 (fun q => labels (.endpoint q)) exit l

theorem rotorTrace (tape : Fin 7 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (port : Fin d)
    (atLabels : ∀ l, program (labels l) = instruction tape d port.val labels exit l)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (tableWord : base (tape 0) = PortTables.tableBits table)
    (scratchEmpty : base (tape 6) = []) (suffix : List Bool)
    (sourceWord : base (tape 1) = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps table vertex port]
      (some ⟨some (labels (.reverse .seed)), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), finalTapes tape table vertex port base⟩ := by
  have hd (i j : Fin 7) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have hrDistinct : Function.Injective (reverseTapes tape) := distinct.comp reverseRole_injective
  have heDistinct : Function.Injective (endpointTapes tape) := distinct.comp endpointRole_injective
  have hrOutside : ∀ i, tape 1 ≠ reverseTapes tape i := fun i =>
    hd 1 (reverseRole i) (source_outside_reverse i)
  have heOutside : ∀ i, tape 4 ≠ endpointTapes tape i := fun i =>
    hd 4 (endpointRole i) (reverse_outside_endpoint i)
  have hreverse := MachineAffineLookup.affineLookupTrace (tape 1) (reverseTapes tape)
    hrDistinct hrOutside (4098 * d) (4098 * port.val + 3)
    (fun q => labels (.reverse q)) (some (labels (.endpoint .seed)))
    program (fun q => atLabels (.reverse q)) base (PortTables.tableWords table)
    tableWord scratchEmpty vertex.val suffix sourceWord (reverseId table vertex port)
    (reverse_selected table vertex port) ambient register
  let mid := afterReverse tape table vertex port base
  have hmidTable : mid (tape 0) = PortTables.tableBits table := by
    calc
      mid (tape 0) = base (tape 0) :=
        MachineAffineLookup.finalTapes_other _ _ _ _ _ _
          (hd 0 2 (by decide)) (hd 0 3 (by decide)) (hd 0 4 (by decide))
      _ = _ := tableWord
  have hmidScratch : mid (tape 6) = [] := by
    calc
      mid (tape 6) = base (tape 6) :=
        MachineAffineLookup.finalTapes_other _ _ _ _ _ _
          (hd 6 2 (by decide)) (hd 6 3 (by decide)) (hd 6 4 (by decide))
      _ = _ := scratchEmpty
  have hmidSource : mid (tape 4) = encodeWord (reverseId table vertex port) ++ base (tape 4) :=
    MachineAffineLookup.finalTapes_output _ _ _ _ _
  have hendpoint := MachineAffineLookup.affineLookupTrace (tape 4) (endpointTapes tape)
    heDistinct heOutside 4098 2 (fun q => labels (.endpoint q)) exit
    program (fun q => atLabels (.endpoint q)) mid (PortTables.tableWords table)
    hmidTable hmidScratch (reverseId table vertex port) (base (tape 4)) hmidSource
    ((PortTables.rotation table (vertex, port)).1.val)
    (endpoint_selected table vertex port) ambient none
  rw [steps, Nat.add_comm, Function.iterate_add_apply, hreverse]
  exact hendpoint

end MaxCutGames.Foundations.Complexity.PoweringMachineRotor

/-! Fixed port words are executed by a finite chain of actual rotor programs.
The six shared tapes hold table, query, scan, reverse identifier, scratch and
output. Each walk position has a separate physical vertex tape. The final
unary copy also handles the empty word and preserves the starting vertex. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineWord

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

def instruction : (t : Nat) → (Tape t → K) → (Fin t → Fin d) →
    (Label t → Λ) → Option Λ → Label t →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | 0, placement, _, labels, exit =>
      copyInstruction (placement (.inr (first 0))) (placement (.inl 4))
        (placement (.inl 5)) labels exit
  | t + 1, placement, ports, labels, exit => fun l =>
      match l with
      | .inl q => PoweringMachineRotor.instruction (placement ∘ rotorRole t) d (ports 0).val
          (fun z => labels (.inl z)) (some (labels (.inr (entry t)))) q
      | .inr q => instruction t (placement ∘ shift t) (fun j => ports j.succ)
          (fun z => labels (.inr z)) exit q

/-- Actual execution together with its endpoint word. No trace or running-time
hypothesis is needed: the recursive proof composes the concrete instructions. -/
theorem wordTrace (table : PortTables.Table n d) (t : Nat)
    (placement : Tape t → K) (distinct : Function.Injective placement)
    (vertex : Fin n) (ports : Fin t → Fin d)
    (labels : Label t → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction t placement ports labels exit l)
    (base : K → List Bool) (tableWord : base (placement (.inl 0)) = PortTables.tableBits table)
    (scratchEmpty : base (placement (.inl 4)) = []) (suffix : List Bool)
    (sourceWord : base (placement (.inr (first t))) = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps table t vertex ports]
      (some ⟨some (labels (entry t)), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), finalTapes table t placement vertex ports base⟩ ∧
    finalTapes table t placement vertex ports base (placement (.inl 5)) =
      encodeWord (PoweringWalks.wordEnd (PortTables.portGraph table) t vertex ports).val ++
        base (placement (.inl 5)) := by
  induction t generalizing vertex base suffix register with
  | zero =>
      have hd (i j : Tape 0) (hne : i ≠ j) : placement i ≠ placement j := fun h => hne (distinct h)
      have hrun := MachineUnaryAffineAt.seededAffineTrace
        (placement (.inr (first 0))) (placement (.inl 4)) (placement (.inl 5))
        (hd _ _ (by simp [first])) (hd _ _ (by simp [first])) (hd _ _ (by simp []))
        1 0 (labels .seed) (labels .scan) (labels .restore) exit program
        (atLabels .seed) (atLabels .scan) (atLabels .restore)
        base vertex.val suffix sourceWord scratchEmpty ambient register
      constructor
      · simpa only [steps, entry, finalTapes, Nat.one_mul, Nat.add_zero] using hrun
      · simp only [finalTapes, Function.update_self, PoweringWalks.wordEnd]
  | succ t ih =>
      have hd (i j : Tape (t + 1)) (hne : i ≠ j) : placement i ≠ placement j :=
        fun h => hne (distinct h)
      have hrotor := PoweringMachineRotor.rotorTrace (placement ∘ rotorRole t)
        (distinct.comp (rotorRole_injective t)) (fun q => labels (.inl q))
        (some (labels (.inr (entry t)))) program (ports 0) (fun q => atLabels (.inl q))
        table vertex base tableWord scratchEmpty suffix sourceWord ambient register
      let mid := PoweringMachineRotor.finalTapes (placement ∘ rotorRole t) table vertex (ports 0) base
      have hmidTable : mid (placement (.inl 0)) = PortTables.tableBits table := by
        calc
          mid (placement (.inl 0)) = base (placement (.inl 0)) :=
            PoweringMachineRotor.finalTapes_other _ _ _ _ _ _
              (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole]))
              (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole, first]))
          _ = _ := tableWord
      have hmidScratch : mid (placement (.inl 4)) = [] := by
        calc
          mid (placement (.inl 4)) = base (placement (.inl 4)) :=
            PoweringMachineRotor.finalTapes_other _ _ _ _ _ _
              (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole]))
              (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole, first]))
          _ = _ := scratchEmpty
      have hmidOutput : mid (placement (.inl 5)) = base (placement (.inl 5)) :=
        PoweringMachineRotor.finalTapes_other _ _ _ _ _ _
          (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole]))
          (hd _ _ (by simp [rotorRole])) (hd _ _ (by simp [rotorRole, first]))
      have hmidSource : mid (placement (.inr (first t).succ)) =
          encodeWord (PortTables.rotation table (vertex, ports 0)).1.val ++
            base (placement (.inr (first t).succ)) :=
        PoweringMachineRotor.finalTapes_endpoint _ (distinct.comp (rotorRole_injective t)) _ _ _ _
      have htail := ih (placement ∘ shift t) (distinct.comp (shift_injective t))
        (PortTables.rotation table (vertex, ports 0)).1 (fun j => ports j.succ)
        (fun q => labels (.inr q)) (fun q => atLabels (.inr q)) mid hmidTable hmidScratch
        (base (placement (.inr (first t).succ))) hmidSource none
      constructor
      · rw [steps, Nat.add_comm, Function.iterate_add_apply]
        simp only [entry]
        rw [hrotor]
        exact htail.1
      · change finalTapes table t (placement ∘ shift t)
          (PortTables.rotation table (vertex, ports 0)).1 (fun j => ports j.succ) mid
          ((placement ∘ shift t) (.inl 5)) = _
        rw [htail.2]
        change _ ++ mid (placement (.inl 5)) = _
        rw [hmidOutput]
        rfl

end MaxCutGames.Foundations.Complexity.PoweringMachineWord

/-! A fixed shared tape layout for the actual powering field subroutines.
The vertex identifiers live on physical tapes. The trajectory capacity is
fixed by `max`; each bounded word uses its first `t` trajectory tapes. -/

/-! Actual powering initialization on the common finite tape set. The first
unary input field is copied by the affine machine and consumed by the checked
header program. The original input and every unrelated tape are preserved.
No runtime graph or vertex count is captured by the finite program. -/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineRelation
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRelation

open Turing
open MachineComposition
open PCP

variable {K Λ σ : Type} [DecidableEq K]
variable {n d : Nat}

def instruction (source : K) (tape : Fin 5 → K) (port : Fin d) (position : Fin 4096)
    (labels : MachineAffineLookup.Label → Λ) (exit : Option Λ) :
    MachineAffineLookup.Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  MachineAffineLookup.instruction source tape (4098 * d)
    (4098 * port.val + 4 + position.val) labels exit

/-- Actual predicate access, with serialization selection discharged. -/
theorem relationTrace (source : K) (tape : Fin 5 → K)
    (distinct : Function.Injective tape) (outside : ∀ i, source ≠ tape i)
    (port : Fin d) (position : Fin 4096)
    (labels : MachineAffineLookup.Label → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction source tape port position labels exit l)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (tableWord : base (tape 0) = PortTables.tableBits table) (scratchEmpty : base (tape 4) = [])
    (suffix : List Bool) (sourceWord : base source = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[MachineAffineLookup.steps (PortTables.tableWords table)
      vertex.val (4098 * d) (4098 * port.val + 4 + position.val)]
      (some ⟨some (labels .seed), (ambient,register), base⟩) =
      some ⟨exit, (ambient,none), MachineAffineLookup.finalTapes tape base
        (PortTables.tableWords table) (address vertex port position) (value table vertex port position)⟩ :=
  MachineAffineLookup.affineLookupTrace source tape distinct outside
    (4098 * d) (4098 * port.val + 4 + position.val) labels exit program atLabels
    base (PortTables.tableWords table) tableWord scratchEmpty vertex.val suffix sourceWord
    (value table vertex port position) (selected table vertex port position) ambient register

end MaxCutGames.Foundations.Complexity.PoweringMachineRelation

/-! A concrete relation-field producer: execute a fixed word from the live
start vertex, then read the predicate at the reached vertex and fixed port.
All instructions use the shared tape layout and preserve the finite row
buffer. No execution premise is supplied by the caller. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRelationField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {n d max : Nat}

def instruction (placement : PoweringMachineTapes.Tape max → K) (path : List (Fin d))
    (lengthBound : path.length ≤ max) (port : Fin d) (left right : PortTables.Label)
    (labels : Label path → Λ) (exit : Option Λ) :
    Label path → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .inl q => PoweringMachineWord.instruction path.length (placement ∘ PoweringMachineTapes.wordPlacement lengthBound false)
      path.get (fun z => labels (.inl z)) (some (labels (.inr .seed))) q
  | .inr q => PoweringMachineRelation.instruction (placement (.inl 6)) (lookupTapes placement)
      port (GraphTables.relationIndex (left, right)) (fun z => labels (.inr z)) exit q

theorem fieldTrace (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (path : List (Fin d)) (lengthBound : path.length ≤ max)
    (port : Fin d) (left right : PortTables.Label)
    (labels : Label path → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction placement path lengthBound port left right labels exit l)
    (table : PortTables.Table n d) (vertex : Fin n) (base : K → List Bool)
    (tableWord : base (placement (.inl 0)) = PortTables.tableBits table)
    (scratchEmpty : base (placement (.inl 5)) = []) (suffix : List Bool)
    (sourceWord : base (placement (.inl 1)) = encodeWord vertex.val ++ suffix) (ambient : A) :
    (advance (TM2.step program))^[steps path port left right table vertex]
      (some ⟨some (labels (.inl (PoweringMachineWord.entry path.length))), MachineUnaryEqualityBit.clean ambient, base⟩) =
      some ⟨exit, MachineUnaryEqualityBit.clean ambient,
        finalTapes placement path lengthBound port left right table vertex base⟩ ∧
    finalTapes placement path lengthBound port left right table vertex base (placement (.inl 10)) =
      encodeWord (bit table vertex path port left right) ++ base (placement (.inl 10)) := by
  have hword := PoweringMachineWord.wordTrace table path.length (placement ∘ PoweringMachineTapes.wordPlacement lengthBound false)
    (distinct.comp (PoweringMachineTapes.wordPlacement_injective lengthBound false)) vertex path.get
    (fun q => labels (.inl q)) (some (labels (.inr .seed))) program
    (fun q => atLabels (.inl q)) base (by simpa [PoweringMachineTapes.table] using tableWord)
    (by simpa [PoweringMachineTapes.scratch] using scratchEmpty) suffix
    (by simpa [PoweringMachineTapes.start] using sourceWord) (ambient, false, none) none
  let mid := afterWord placement path lengthBound table vertex base
  have hmidTable : mid (placement (.inl 0)) = PortTables.tableBits table := by
    dsimp only [mid]
    rw [afterWord_frame placement distinct path lengthBound table vertex base 0
      (by decide) (by decide) (by decide) (by decide)]
    exact tableWord
  have hmidScratch : mid (placement (.inl 5)) = [] := by
    dsimp only [mid]
    rw [afterWord_frame placement distinct path lengthBound table vertex base 5
      (by decide) (by decide) (by decide) (by decide)]
    exact scratchEmpty
  have hmidOutput : mid (placement (.inl 10)) = base (placement (.inl 10)) :=
    afterWord_frame placement distinct path lengthBound table vertex base 10
      (by decide) (by decide) (by decide) (by decide)
  have hmidEndpoint : mid (placement (.inl 6)) = encodeWord (endpoint table vertex path).val ++
      base (placement (.inl 6)) := by
    dsimp only [mid, afterWord]
    simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_five, PoweringMachineTapes.endpoint_false,
      PoweringMachineTapes.leftEndpoint, ← endpoint_eq_wordEnd] using hword.2
  have hrelation := PoweringMachineRelation.relationTrace (placement (.inl 6)) (lookupTapes placement)
    (lookupTapes_injective placement distinct) (source_outside_lookup placement distinct)
    port (GraphTables.relationIndex (left, right)) (fun q => labels (.inr q)) exit program
    (fun q => atLabels (.inr q)) table (endpoint table vertex path) mid
    (by simpa [lookupTapes, PoweringMachineTapes.table] using hmidTable)
    (by simpa [lookupTapes, PoweringMachineTapes.scratch] using hmidScratch)
    (base (placement (.inl 6))) hmidEndpoint (ambient, false, none) none
  constructor
  · simp only [MachineUnaryEqualityBit.clean]
    rw [steps, Nat.add_comm, Function.iterate_add_apply, hword.1]
    exact hrelation
  · change MachineAffineLookup.finalTapes (lookupTapes placement) _ _ _ _ (lookupTapes placement 3) = _
    rw [MachineAffineLookup.finalTapes_output]
    change encodeWord (bit table vertex path port left right) ++ mid (placement (.inl 10)) = _
    rw [hmidOutput]

theorem steps_le (path : List (Fin d)) (port : Fin d) (left right : PortTables.Label)
    (table : PortTables.Table n d) (vertex : Fin n) :
    steps path port left right table vertex ≤
      (14 * path.length + 9) * (PortTables.tableBits table).length + 12 * path.length + 9 := by
  have hw := PoweringMachineWord.steps_le table path.length vertex path.get
  have hr := PoweringMachineRelation.steps_le table (endpoint table vertex path) port
    (GraphTables.relationIndex (left, right))
  simp only [steps, Nat.add_mul, Nat.mul_assoc] at hw ⊢
  omega

end MaxCutGames.Foundations.Complexity.PoweringMachineRelationField

/-!
# Actual producer for equality of two bounded walk endpoints

The two port words are fixed finite control. Each executes against the live
rotor table from the same preserved starting vertex. Their endpoint fields
are compared by the physical unary equality primitive. The emitted field is
the Boolean equality of the two actual walk endpoints.

Work tapes may retain arbitrary histories. The table, start, scratch and two
comparison copies satisfy exact frame theorems. There is no execution or
running-time premise in the composite trace theorem.
-/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineEqualityField

open Turing
open MachineComposition
open PCP

variable {K Λ A : Type} [DecidableEq K]
variable {max l r n d : Nat}

def instruction (hl : l ≤ max) (hr : r ≤ max) (placement : Tape max → K)
    (left : Fin l → Fin d) (right : Fin r → Fin d)
    (labels : Label l r → Λ) (exit : Option Λ) :
    Label l r → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .inl q => PoweringMachineWord.instruction l
      (placement ∘ PoweringMachineTapes.wordPlacement hl false) left
      (fun z => labels (.inl z))
      (some (labels (.inr (.inl (PoweringMachineWord.entry r))))) q
  | .inr (.inl q) => PoweringMachineWord.instruction r
      (placement ∘ PoweringMachineTapes.wordPlacement hr true) right
      (fun z => labels (.inr (.inl z)))
      (some (labels (.inr (.inr .seedLeft)))) q
  | .inr (.inr q) => MachineUnaryEqualityBit.instruction
      (placement ∘ PoweringMachineTapes.equalityPlacement max)
      (fun z => labels (.inr (.inr z))) exit q

theorem fieldTrace (graph : PortTables.Table n d) (hl : l ≤ max) (hr : r ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin n) (left : Fin l → Fin d) (right : Fin r → Fin d)
    (labels : Label l r → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ q, program (labels q) = instruction hl hr placement left right labels exit q)
    (base : K → List Bool)
    (tableWord : base (placement (.inl 0)) = PortTables.tableBits graph)
    (scratchEmpty : base (placement (.inl 5)) = [])
    (leftCopyEmpty : base (placement (.inl 8)) = [])
    (rightCopyEmpty : base (placement (.inl 9)) = [])
    (suffix : List Bool) (sourceWord : base (placement (.inl 1)) = encodeWord vertex.val ++ suffix)
    (ambient : A) :
    (advance (TM2.step program))^[steps graph vertex left right]
      (some ⟨some (labels (entry l r)), MachineUnaryEqualityBit.clean ambient, base⟩) =
      some ⟨exit, MachineUnaryEqualityBit.clean ambient,
        finalTapes graph hl hr placement vertex left right base⟩ := by
  let afterLeft := wordTapes graph hl placement false vertex left base
  let afterBoth := wordTapes graph hr placement true vertex right afterLeft
  have leftFrame (j : Fin 11) (h2 : j ≠ 2) (h3 : j ≠ 3) (h4 : j ≠ 4) (h6 : j ≠ 6) :
      afterLeft (placement (.inl j)) = base (placement (.inl j)) :=
    wordTapes_role graph hl placement distinct false vertex left base j h2 h3 h4 h6
  have rightFrame (j : Fin 11) (h2 : j ≠ 2) (h3 : j ≠ 3) (h4 : j ≠ 4) (h7 : j ≠ 7) :
      afterBoth (placement (.inl j)) = afterLeft (placement (.inl j)) :=
    wordTapes_role graph hr placement distinct true vertex right afterLeft j h2 h3 h4 h7
  have bothFrame (j : Fin 11) (h2 : j ≠ 2) (h3 : j ≠ 3) (h4 : j ≠ 4)
      (h6 : j ≠ 6) (h7 : j ≠ 7) :
      afterBoth (placement (.inl j)) = base (placement (.inl j)) :=
    (rightFrame j h2 h3 h4 h7).trans (leftFrame j h2 h3 h4 h6)
  have leftRun := PoweringMachineWord.wordTrace graph l
    (placement ∘ PoweringMachineTapes.wordPlacement hl false)
    (distinct.comp (PoweringMachineTapes.wordPlacement_injective hl false)) vertex left
    (fun q => labels (.inl q))
    (some (labels (.inr (.inl (PoweringMachineWord.entry r))))) program
    (fun q => atLabels (.inl q)) base
    (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_zero,
      PoweringMachineTapes.table] using tableWord)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_four,
      PoweringMachineTapes.scratch] using scratchEmpty)
    suffix (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_first,
      PoweringMachineTapes.start] using sourceWord)
    (ambient, false, none) none
  have rightTable : afterLeft (placement (.inl 0)) = PortTables.tableBits graph :=
    (leftFrame 0 (by decide) (by decide) (by decide) (by decide)).trans tableWord
  have rightScratch : afterLeft (placement (.inl 5)) = [] :=
    (leftFrame 5 (by decide) (by decide) (by decide) (by decide)).trans scratchEmpty
  have rightSource : afterLeft (placement (.inl 1)) = encodeWord vertex.val ++ suffix :=
    (leftFrame 1 (by decide) (by decide) (by decide) (by decide)).trans sourceWord
  have rightRun := PoweringMachineWord.wordTrace graph r
    (placement ∘ PoweringMachineTapes.wordPlacement hr true)
    (distinct.comp (PoweringMachineTapes.wordPlacement_injective hr true)) vertex right
    (fun q => labels (.inr (.inl q))) (some (labels (.inr (.inr .seedLeft)))) program
    (fun q => atLabels (.inr (.inl q))) afterLeft
    (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_zero,
      PoweringMachineTapes.table] using rightTable)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_four,
      PoweringMachineTapes.scratch] using rightScratch)
    suffix (by simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_first,
      PoweringMachineTapes.start] using rightSource)
    (ambient, false, none) none
  have leftEndpoint : afterBoth (placement (.inl 6)) =
      encodeWord (endpoint graph vertex left).val ++ base (placement (.inl 6)) := by
    rw [rightFrame 6 (by decide) (by decide) (by decide) (by decide)]
    dsimp only [afterLeft, wordTapes]
    simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_five,
      PoweringMachineTapes.endpoint_false, PoweringMachineTapes.leftEndpoint,
      wordTapes, endpoint] using leftRun.2
  have rightEndpoint : afterBoth (placement (.inl 7)) =
      encodeWord (endpoint graph vertex right).val ++ afterLeft (placement (.inl 7)) := by
    dsimp only [afterBoth, wordTapes]
    simpa only [Function.comp_apply, PoweringMachineTapes.wordPlacement_inl_five,
      PoweringMachineTapes.endpoint_true, PoweringMachineTapes.rightEndpoint,
      wordTapes, endpoint] using rightRun.2
  have copiesLeft : afterBoth (placement (.inl 8)) = [] :=
    (bothFrame 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans leftCopyEmpty
  have copiesRight : afterBoth (placement (.inl 9)) = [] :=
    (bothFrame 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans rightCopyEmpty
  have scratchBoth : afterBoth (placement (.inl 5)) = [] :=
    (bothFrame 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans scratchEmpty
  have equalityRun := MachineUnaryEqualityBit.equalityTrace
    (placement ∘ PoweringMachineTapes.equalityPlacement max)
    (distinct.comp (PoweringMachineTapes.equalityPlacement_injective max))
    (fun q => labels (.inr (.inr q))) exit program (fun q => atLabels (.inr (.inr q)))
    afterBoth (endpoint graph vertex left).val (endpoint graph vertex right).val
    (base (placement (.inl 6))) (afterLeft (placement (.inl 7)))
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_zero,
      PoweringMachineTapes.leftEndpoint] using leftEndpoint)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_one,
      PoweringMachineTapes.rightEndpoint] using rightEndpoint)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_two,
      PoweringMachineTapes.leftCopy] using copiesLeft)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_three,
      PoweringMachineTapes.rightCopy] using copiesRight)
    (by simpa only [Function.comp_apply, PoweringMachineTapes.equalityPlacement_four,
      PoweringMachineTapes.scratch] using scratchBoth)
    ambient
  have joined := joinTrace_inline_PoweringMachineEqualityField (joinTrace_inline_PoweringMachineEqualityField leftRun.1 rightRun.1) equalityRun
  simpa only [steps, entry, MachineUnaryEqualityBit.clean, Function.comp_apply,
    PoweringMachineTapes.equalityPlacement_five, PoweringMachineTapes.rowOutput,
    finalTapes, resultBit, Fin.ext_iff,
    afterLeft, afterBoth, wordTapes] using joined

end MaxCutGames.Foundations.Complexity.PoweringMachineEqualityField

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PoweringRowData
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineField.labelDecidableEq _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineField.labelFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Actual graph data consumed by the powered-row machine

The data fields are computed from the stored rotor and base relations. The
endpoint masks compare actual bounded word endpoints, in `allAddresses` order.
Their first true positions equal the already checked canonical address indices.

Reversing a row swaps the two masks and transposes each base predicate. Thus
one fixed row machine handles both directions. Its label lookup depends only
on the fixed degree and radius. The final identities describe the exact unary
input fields and the exact serialized relation emitted for a stored output row.

These are semantic producer-to-emitter identities. A machine implementation
that computes the input data from the serialized rotor is a separate frontend.
-/

namespace MaxCutGames.Foundations.PCP.PoweringRowData

open MaxCutGames.Foundations.Complexity
open Turing
open PoweringMachineRow MachineFixedBlockMap
open PoweringWalks PoweringLabels PoweringAddresses PoweringReach
open PoweringOpinionTables PoweringEnumeration

variable {vertices d : Nat}

/-! ## Exact field and emitted-relation serialization -/

theorem dataTape_eq (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    dataTape input n e = encodeBits (List.ofFn (rowBits input n e)) :=
  (encodeBits_graphWords _).symm

theorem rowBlock_unary (input : PortTables.Table vertices d) (n : Nat)
    (e : PoweringTest.Dart (Fin vertices) (Fin d) n) :
    encodeBits (List.ofFn (rowBlock (fixedLabelAt d n) (rowBits input n e))) =
      encodeWords (GenericGraphTables.relationWords (emittedRelation input n e)) := by
  have hbit : GraphTables.bitWord = GenericGraphTables.bitWord := by
    funext b
    cases b <;> rfl
  have h := encodeBits_graphWords
    (List.ofFn (rowBlock (fixedLabelAt d n) (rowBits input n e)))
  rw [hbit] at h
  simpa only [emittedRelation, GenericGraphTables.relationWords, Vector.toList_ofFn] using h

end MaxCutGames.Foundations.PCP.PoweringRowData

/-! A fixed powered-row data block is reduced to two concrete instruction
forms: follow a fixed port word and read one stored predicate entry, or follow
two fixed words and compare their endpoint identifiers. The plan depends only
on the fixed degree, radius, word and orientation. Its interpretation is exactly
the data block consumed by the checked row transducer. -/

namespace MaxCutGames.Foundations.PCP.PoweringFieldPlan

open PoweringWalks PoweringLabels PoweringAddresses PoweringReach PoweringRowData
open MaxCutGames.Foundations.Complexity PoweringMachineRow

variable {V D : Type*}

theorem dataTape_eq_plan {vertices d : Nat} (input : PortTables.Table vertices d)
    (n : Nat) (start : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    dataTape input n (direction, start, ports) =
      encodeBits ((rowPlan n ports direction).map (evaluate input start)) := by
  rw [evaluate_rowPlan, dataTape_eq]

end MaxCutGames.Foundations.PCP.PoweringFieldPlan

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineField
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.PoweringMachineField

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {n d max : Nat}

def instruction (placement : Tape max → K) : (op : Instruction d) → op.radius ≤ max →
    (Label op → Λ) → Option Λ → Label op → TM2.Stmt (fun _ : K => Bool) Λ (State A)
  | .relation path port a b, bounded, labels, exit =>
      PoweringMachineRelationField.instruction placement path bounded port a b labels exit
  | .equal left right, bounded, labels, exit =>
      PoweringMachineEqualityField.instruction
        ((le_max_left _ _).trans bounded) ((le_max_right _ _).trans bounded)
        placement left.get right.get labels exit

theorem fieldTrace (graph : PortTables.Table n d) (placement : Tape max → K)
    (distinct : Function.Injective placement) (vertex : Fin n)
    (op : Instruction d) (bounded : op.radius ≤ max)
    (labels : Label op → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction placement op bounded labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : Ready graph placement vertex suffix base) (ambient : A) :
    (advance (TM2.step program))^[steps graph vertex op]
      (some ⟨some (labels (entry op)), MachineUnaryEqualityBit.clean ambient, base⟩) =
      some ⟨exit, MachineUnaryEqualityBit.clean ambient,
        finalTapes graph placement vertex op bounded base⟩ := by
  cases op with
  | relation path port a b =>
      exact (PoweringMachineRelationField.fieldTrace placement distinct path bounded port a b
        labels exit program atLabels graph vertex base ready.table ready.scratch suffix
        ready.source ambient).1
  | equal left right =>
      exact PoweringMachineEqualityField.fieldTrace graph _ _ placement distinct
        vertex left.get right.get labels exit program atLabels base ready.table ready.scratch
        ready.leftCopy ready.rightCopy suffix ready.source ambient

theorem finalTapes_output (graph : PortTables.Table n d) (placement : Tape max → K)
    (distinct : Function.Injective placement) (vertex : Fin n)
    (op : Instruction d) (bounded : op.radius ≤ max) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph placement vertex suffix base) :
    finalTapes graph placement vertex op bounded base (placement (.inl 10)) =
      PoweringMachineRow.encodeBit (evaluate graph vertex op) ++ base (placement (.inl 10)) := by
  cases op with
  | relation path port a b =>
      have h := (PoweringMachineRelationField.fieldTrace placement distinct path bounded port a b
        id none (PoweringMachineRelationField.instruction placement path bounded port a b id none)
        (fun _ => rfl) graph vertex base ready.table ready.scratch suffix ready.source ()).2
      have he : ∀ bit : Bool, encodeWord (GraphTables.bitWord bit) =
          PoweringMachineRow.encodeBit bit := by intro bit; cases bit <;> rfl
      simpa only [finalTapes, PoweringMachineRelationField.bit, PoweringMachineRelationField.endpoint,
        evaluate, he] using h
  | equal left right =>
      have h := PoweringMachineEqualityField.finalTapes_output graph
        ((le_max_left _ _).trans bounded) ((le_max_right _ _).trans bounded) placement distinct
        vertex left.get right.get base
      have he : ∀ bit : Bool, MachineUnaryEqualityBit.bitEncoding bit =
          PoweringMachineRow.encodeBit bit := by intro bit; cases bit <;> rfl
      simpa only [finalTapes, PoweringMachineEqualityField.resultBit, PoweringMachineEqualityField.endpoint,
        PoweringReach.wordEnd_eq_walkEnd_ofFn, List.ofFn_get, evaluate, he] using h

end MaxCutGames.Foundations.Complexity.PoweringMachineField

/-! The concrete finite program that produces an entire powered-row input
block. Its static control executes the field plan backwards, so prepending each
computed unary Boolean field leaves the canonical serialized block in order. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachinePlan

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

def instruction (placement : PoweringMachineTapes.Tape max → K)
    (commands : List (Command d max)) (labels : Label commands → Λ) (exit : Option Λ) :
    Label commands → TM2.Stmt (fun _ : K => Bool) Λ (MachineUnaryEqualityBit.State A) :=
  MachineFiniteSequence.instruction LocalLabel (fun op => PoweringMachineField.entry op.val)
    (fun op => PoweringMachineField.instruction placement op.val op.property)
    commands labels exit

theorem planTrace (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (commands : List (Command d max))
    (labels : Label commands → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (MachineUnaryEqualityBit.State A))
    (atLabels : ∀ l, program (labels l) = instruction placement commands labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineField.Ready graph placement vertex suffix base) (ambient : A) :
    (advance (TM2.step program))^[steps graph placement vertex commands base]
      (some ⟨entry commands labels exit, MachineUnaryEqualityBit.clean ambient, base⟩) =
    some ⟨exit, MachineUnaryEqualityBit.clean ambient,
      finalTapes graph placement vertex commands base⟩ := by
  apply MachineFiniteSequence.trace LocalLabel (fun op => PoweringMachineField.entry op.val)
    (fun op => PoweringMachineField.instruction placement op.val op.property)
    (result graph placement vertex) (fun op _ => PoweringMachineField.steps graph vertex op.val)
    program (PoweringMachineField.Ready graph placement vertex suffix)
    (fun _ => MachineUnaryEqualityBit.clean ambient) id commands
  · intro op _ tapes good
    exact PoweringMachineField.ready_finalTapes graph placement distinct vertex op.val
      op.property tapes suffix good
  · intro op _ localLabels localExit atLocal tapes good
    exact PoweringMachineField.fieldTrace graph placement distinct vertex op.val op.property
      localLabels localExit program atLocal tapes suffix good ambient
  · exact atLabels
  · exact ready

theorem finalTapes_output (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (commands : List (Command d max)) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineField.Ready graph placement vertex suffix base) :
    finalTapes graph placement vertex commands base (placement (.inl 10)) =
      PoweringMachineRow.encodeBits ((commands.map (fun op => evaluate graph vertex op.val)).reverse) ++
        base (placement (.inl 10)) := by
  induction commands generalizing base with
  | nil => rfl
  | cons op commands ih =>
      have nextReady := PoweringMachineField.ready_finalTapes graph placement distinct vertex
        op.val op.property base suffix ready
      change finalTapes graph placement vertex commands
        (result graph placement vertex op base) (placement (.inl 10)) = _
      dsimp only [result]
      rw [ih _ nextReady, PoweringMachineField.finalTapes_output graph placement distinct vertex
        op.val op.property base suffix ready]
      simp only [List.map_cons, List.reverse_cons, PoweringMachineRow.encodeBits_append,
        PoweringMachineRow.encodeBits, List.append_nil,
        List.append_assoc]

theorem rowPlan_output (graph : PortTables.Table vertices d)
    (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (placement : PoweringMachineTapes.Tape (2 * (n + 1)) → K)
    (distinct : Function.Injective placement) (vertex : Fin vertices) (base : K → List Bool)
    (suffix : List Bool) (ready : PoweringMachineField.Ready graph placement vertex suffix base) :
    finalTapes graph placement vertex (boundedRowPlan n ports direction).reverse base
      (placement (.inl 10)) =
      PoweringRowData.dataTape graph n (direction, vertex, ports) ++ base (placement (.inl 10)) := by
  rw [finalTapes_output graph placement distinct vertex _ base suffix ready]
  rw [List.map_reverse, List.reverse_reverse, PoweringFieldPlan.dataTape_eq_plan]
  have h := congrArg (List.map (evaluate graph vertex)) (boundedRowPlan_values n ports direction)
  simpa only [List.map_map, Function.comp_def] using
    congrArg (fun bits => PoweringMachineRow.encodeBits bits ++ base (placement (.inl 10))) h

end MaxCutGames.Foundations.Complexity.PoweringMachinePlan

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_PoweringPlanBudget
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Execution budget of the concrete powered-row field plan

The cost is the sum of the actual relation and endpoint-comparison transition
counts. Each fixed command scans only the serialized input graph. The execution
certificates below instantiate the concrete plan trace; no execution witness or
running-time bound is assumed.
-/

namespace MaxCutGames.Foundations.Complexity.PoweringPlanBudget

open Turing MachineComposition PCP PoweringFieldPlan

variable {K Λ A : Type} [DecidableEq K] {vertices d max : Nat}

theorem field_steps_le (graph : PortTables.Table vertices d) (vertex : Fin vertices)
    (op : Instruction d) (bounded : op.radius ≤ max) :
    PoweringMachineField.steps graph vertex op ≤
      fieldBudget max (PortTables.tableBits graph).length := by
  cases op with
  | relation path port left right =>
      change path.length ≤ max at bounded
      have h := PoweringMachineRelationField.steps_le path port left right graph vertex
      have coefficient : 14 * path.length + 9 ≤ 28 * max + 10 := by omega
      have product := Nat.mul_le_mul_right (PortTables.tableBits graph).length coefficient
      change PoweringMachineRelationField.steps path port left right graph vertex ≤ _
      unfold fieldBudget
      omega
  | equal left right =>
      change Nat.max left.length right.length ≤ max at bounded
      have hl : left.length ≤ max := (le_max_left _ _).trans bounded
      have hr : right.length ≤ max := (le_max_right _ _).trans bounded
      have h := PoweringMachineEqualityField.steps_le graph vertex left.get right.get
      have coefficient : 14 * (left.length + right.length) + 10 ≤ 28 * max + 10 := by
        omega
      have product := Nat.mul_le_mul_right (PortTables.tableBits graph).length coefficient
      change PoweringMachineEqualityField.steps graph vertex left.get right.get ≤ _
      unfold fieldBudget
      omega

/-- Sum the actual recursive cost, including its changing intermediate tapes. -/
theorem plan_steps_le (graph : PortTables.Table vertices d)
    (placement : PoweringMachineTapes.Tape max → K) (vertex : Fin vertices)
    (commands : List (PoweringMachinePlan.Command d max)) (base : K → List Bool) :
    PoweringMachinePlan.steps graph placement vertex commands base ≤
      commands.length * fieldBudget max (PortTables.tableBits graph).length := by
  induction commands generalizing base with
  | nil => simp only [PoweringMachinePlan.steps, MachineFiniteSequence.steps,
      List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons op commands ih =>
      have first := field_steps_le graph vertex op.val op.property
      have rest := ih (PoweringMachinePlan.result graph placement vertex op base)
      change PoweringMachineField.steps graph vertex op.val +
        PoweringMachinePlan.steps graph placement vertex commands
          (PoweringMachinePlan.result graph placement vertex op base) ≤ _
      simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        Nat.add_le_add first rest

/-- For fixed degree and radius this is affine in the serialized graph length. -/
def rowBudget (d n inputLength : Nat) : Nat :=
  PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n) *
    fieldBudget (2 * (n + 1)) inputLength

/-- The backwards plan that produces the actual row-data tape obeys this bound. -/
theorem rowPlan_steps_le (graph : PortTables.Table vertices d) (n : Nat)
    (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (placement : PoweringMachineTapes.Tape (2 * (n + 1)) → K)
    (vertex : Fin vertices) (base : K → List Bool) :
    PoweringMachinePlan.steps graph placement vertex
        (PoweringMachinePlan.boundedRowPlan n ports direction).reverse base ≤
      PoweringMachineRow.inputSize (n + 1) (PoweringRowData.slotCount d n) *
        ((28 * (2 * (n + 1)) + 10) * (PortTables.tableBits graph).length +
          24 * (2 * (n + 1)) + 15) := by
  have h := plan_steps_le graph placement vertex
    (PoweringMachinePlan.boundedRowPlan n ports direction).reverse base
  simpa only [List.length_reverse, boundedRowPlan_length, fieldBudget] using h

end MaxCutGames.Foundations.Complexity.PoweringPlanBudget

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineRowHeaders
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRowHeaders

open Turing MachineComposition
open PCP PoweringRowHeaderSemantics
open PoweringMachineTapes

variable {K Λ σ : Type} [DecidableEq K]
variable {vertices d max : Nat}

/-- Only the coefficient, word, and direction are built into finite control. -/
def instruction (n : Nat) (h : n + 1 ≤ max) (placement : Tape max → K)
    (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n → Λ) (exit : Option Λ) :
    Label n → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .inl q => affineInstruction (placement (start max)) (placement (scratch max))
      (placement (rowOutput max)) (blockSize d n) (reverseOffset d n ports direction)
      (fun z => labels (.inl z)) (some (labels (tailEntry n direction))) q
  | .inr (.inl q) => PoweringMachineWord.copyInstruction
      (placement (start max)) (placement (scratch max)) (placement (rowOutput max))
      (fun z => labels (.inr (.inl z))) exit q
  | .inr (.inr q) => PoweringMachineWord.instruction (n + 1)
      (placement ∘ headerPlacement h) ports (fun z => labels (.inr (.inr z))) exit q

/-- Compose the actual affine and word/copy instructions. The trace and both
header values are derived; the only data premises describe the physical input. -/
theorem headerTrace (input : PortTables.Table vertices d) (n : Nat) (h : n + 1 ≤ max)
    (placement : Tape max → K) (distinct : Function.Injective placement)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool))
    (atLabels : ∀ l, program (labels l) = instruction n h placement ports direction labels exit l)
    (base : K → List Bool) (tableWord : base (placement (table max)) = PortTables.tableBits input)
    (scratchEmpty : base (placement (scratch max)) = []) (suffix : List Bool)
    (sourceWord : base (placement (start max)) = encodeWord vertex.val ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step program))^[steps input n vertex ports direction]
      (some ⟨some (labels (entry n)), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), finalTapes input n h placement vertex ports direction base⟩ ∧
    finalTapes input n h placement vertex ports direction base (placement (rowOutput max)) =
      encodeWords (headerWords input n vertex ports direction) ++ base (placement (rowOutput max)) := by
  have hd (i j : Tape max) (hne : i ≠ j) : placement i ≠ placement j :=
    fun eq => hne (distinct eq)
  have hsourceOut : placement (start max) ≠ placement (rowOutput max) :=
    hd _ _ (by simp [start, rowOutput])
  have hscratchOut : placement (scratch max) ≠ placement (rowOutput max) :=
    hd _ _ (by simp [scratch, rowOutput])
  have htableOut : placement (table max) ≠ placement (rowOutput max) :=
    hd _ _ (by simp [table, rowOutput])
  let mid := afterReverse n placement vertex ports direction base
  have hrev := MachineUnaryAffineAt.seededAffineTrace
    (placement (start max)) (placement (scratch max)) (placement (rowOutput max))
    (hd _ _ (by simp [start, scratch])) hsourceOut hscratchOut
    (blockSize d n) (reverseOffset d n ports direction)
    (labels (.inl .seed)) (labels (.inl .scan)) (labels (.inl .restore))
    (some (labels (tailEntry n direction))) program
    (atLabels (.inl .seed)) (atLabels (.inl .scan)) (atLabels (.inl .restore))
    base vertex.val suffix sourceWord scratchEmpty ambient register
  have hreverseTrace : (advance (TM2.step program))^[2 * (vertex.val + 1) + 1]
      (some ⟨some (labels (entry n)), (ambient, register), base⟩) =
      some ⟨some (labels (tailEntry n direction)), (ambient, none), mid⟩ := by
    simpa only [entry, mid, afterReverse, reverseValue] using hrev
  have hmidSource : mid (placement (start max)) = encodeWord vertex.val ++ suffix := by
    simpa only [mid, afterReverse, Function.update_of_ne hsourceOut] using sourceWord
  have hmidScratch : mid (placement (scratch max)) = [] := by
    simpa only [mid, afterReverse, Function.update_of_ne hscratchOut] using scratchEmpty
  have hmidTable : mid (placement (table max)) = PortTables.tableBits input := by
    simpa only [mid, afterReverse, Function.update_of_ne htableOut] using tableWord
  cases direction with
  | false =>
    have hcopy := MachineUnaryAffineAt.seededAffineTrace
      (placement (start max)) (placement (scratch max)) (placement (rowOutput max))
      (hd _ _ (by simp [start, scratch])) hsourceOut hscratchOut 1 0
      (labels (.inr (.inl .seed))) (labels (.inr (.inl .scan)))
      (labels (.inr (.inl .restore))) exit program
      (atLabels (.inr (.inl .seed))) (atLabels (.inr (.inl .scan)))
      (atLabels (.inr (.inl .restore))) mid vertex.val suffix hmidSource hmidScratch ambient none
    constructor
    · rw [steps, ite_eq_right Bool.false_ne_true, Function.iterate_add_apply, hreverseTrace]
      simpa only [tailEntry, Bool.false_eq_true, ite_false, finalTapes, Nat.one_mul,
        Nat.add_zero] using hcopy
    · simp only [finalTapes, Bool.false_eq_true, ite_false, Function.update_self,
        afterReverse, headerWords, tailVertex, encodeWords, List.append_nil, List.append_assoc]
  | true =>
    have hword := PoweringMachineWord.wordTrace input (n + 1)
      (placement ∘ headerPlacement h) (distinct.comp (headerPlacement_injective h)) vertex ports
      (fun z => labels (.inr (.inr z))) exit program (fun z => atLabels (.inr (.inr z))) mid
      (by simpa only [Function.comp_apply, headerPlacement_table] using hmidTable)
      (by simpa only [Function.comp_apply, headerPlacement_scratch] using hmidScratch)
      suffix (by simpa only [Function.comp_apply, headerPlacement_start] using hmidSource) ambient none
    constructor
    · rw [steps, ite_eq_left rfl, Nat.add_comm, Function.iterate_add_apply, hreverseTrace]
      simpa only [tailEntry, ite_true, if_true, finalTapes] using hword.1
    · have hout := hword.2
      simp only [Function.comp_apply, headerPlacement_output] at hout
      simpa only [finalTapes, ite_true, if_true, mid, afterReverse, Function.update_self,
        headerWords, tailVertex, encodeWords, List.append_nil, List.append_assoc] using hout

/-- Linear in the serialized input length for the fixed word length. -/
theorem steps_le (input : PortTables.Table vertices d) (n : Nat) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    steps input n vertex ports direction ≤
      (14 * (n + 1) + 4) * (PortTables.tableBits input).length + 12 * (n + 1) + 6 := by
  have hv : vertex.val ≤ (PortTables.tableBits input).length :=
    Nat.le_trans (Nat.le_of_lt vertex.isLt) (PortTables.vertices_le_tableBits_length input)
  have hw := PoweringMachineWord.steps_le input (n + 1) vertex ports
  cases direction <;> simp only [steps, Bool.false_eq_true, ite_false, ite_true, if_true]
  · simp only [Nat.add_mul]
    omega
  · calc
      _ ≤ (2 * (PortTables.tableBits input).length + 3) +
          ((14 * (n + 1) + 2) * (PortTables.tableBits input).length + 12 * (n + 1) + 3) :=
        Nat.add_le_add (by omega) hw
      _ = _ := by simp only [Nat.add_mul]; omega

end MaxCutGames.Foundations.Complexity.PoweringMachineRowHeaders

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRowBody

open Turing MachineComposition PCP
open MachineFixedBlockMap

variable {K Λ : Type} [DecidableEq K] {vertices d : Nat}

def instruction (n : Nat) (placement : PoweringMachineTapes.Tape (capacity n) → K)
    (output : K) (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n ports direction → Λ) (exit : Option Λ) :
    Label n ports direction → TM2.Stmt (fun _ : K => Bool) Λ (State d n)
  | .inl q => PoweringMachinePlan.instruction placement (commands n ports direction)
      (fun z => labels (.inl z)) (some (labels (.inr (.inl ())))) q
  | .inr (.inl _) => PoweringMasterState.rowAt (t := n + 1) (placement (.inl 10)) output
      (PoweringRowData.fixedLabelAt d n) (some (labels (.inr (.inr (PoweringMachineRowHeaders.entry n)))))
  | .inr (.inr q) => PoweringMachineRowHeaders.instruction n (by unfold capacity; omega)
      (headerPlacement placement output) ports direction (fun z => labels (.inr (.inr z))) exit q

theorem rowBlock_eq_rowRelation (graph : PortTables.Table vertices d) (n : Nat)
    (vertex : Fin vertices) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    PoweringMachineRow.encodeBits (List.ofFn (PoweringMachineRow.rowBlock
      (PoweringRowData.fixedLabelAt d n) (PoweringRowData.rowBits graph n (direction, vertex, ports)))) =
      rowRelation graph n vertex ports direction := by
  calc
    _ = encodeWords (GenericGraphTables.relationWords
        (PoweringRowData.emittedRelation graph n (direction, vertex, ports))) :=
      PoweringRowData.rowBlock_unary graph n (direction, vertex, ports)
    _ = _ := by
      have h := PoweringRowData.emittedRelation_table graph n
        (PoweringEnumeration.encodeDart vertices d n (direction, vertex, ports))
      rw [PoweringEnumeration.decodeDart_encodeDart] at h
      exact congrArg (fun relation : GenericGraphTables.RelationTable (PoweringTables.labelCount d n) =>
        encodeWords (GenericGraphTables.relationWords relation)) h

/-- The full serialized row is prepended to the caller's existing output. -/
theorem finalTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool) (base : K → List Bool)
    (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    finalTapes graph n placement output vertex ports direction base output =
      encodeWords (rowWords graph n vertex ports direction) ++ base output := by
  have hm := afterEmit_ready graph n placement distinct output outside vertex ports direction base suffix ready
  have hh := (PoweringMachineRowHeaders.headerTrace graph n (by unfold capacity; omega)
    (headerPlacement placement output) (headerPlacement_injective placement distinct output outside)
    vertex ports direction id none
    (PoweringMachineRowHeaders.instruction n (by unfold capacity; omega)
      (headerPlacement placement output) ports direction id none) (fun _ => rfl)
    (afterEmit graph n placement output vertex ports direction base)
    (by simpa [headerPlacement, PoweringMachineTapes.table] using hm.1.table)
    (by simpa [headerPlacement, PoweringMachineTapes.scratch] using hm.1.scratch) suffix
    (by simpa [headerPlacement, PoweringMachineTapes.start] using hm.1.source) () none).2
  simp only [PoweringMachineTapes.rowOutput, headerPlacement_output] at hh
  calc
    finalTapes graph n placement output vertex ports direction base output =
        encodeWords (PoweringRowHeaderSemantics.headerWords graph n vertex ports direction) ++
          afterEmit graph n placement output vertex ports direction base output := hh
    _ = encodeWords (PoweringRowHeaderSemantics.headerWords graph n vertex ports direction) ++
        (rowRelation graph n vertex ports direction ++ base output) := by
      simp only [afterEmit, Function.update_self]
      rw [show afterPlan graph n placement vertex ports direction base output = base output from
        plan_other_inline_PoweringMachineRowBody graph placement vertex _ base output outside]
    _ = _ := PoweringRowHeaderSemantics.header_relation_bits graph n vertex ports direction (base output)

/-- The complete row producer executes its concrete plan, one row transition,
and the concrete two-header writer. No local execution hypothesis is assumed. -/
theorem rowTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (capacity n) → K) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i) (vertex : Fin vertices)
    (ports : Fin (n + 1) → Fin d) (direction : Bool)
    (labels : Label n ports direction → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = instruction n placement output ports direction labels exit l)
    (base : K → List Bool) (suffix : List Bool) (ready : Ready graph n placement vertex suffix base) :
    (advance (TM2.step program))^[steps graph vertex n ports direction]
      (some ⟨some (labels (entry n ports direction)), PoweringMasterState.clean (bufferSize d n), base⟩) =
      some ⟨exit, PoweringMasterState.clean (bufferSize d n),
        finalTapes graph n placement output vertex ports direction base⟩ := by
  have hp := PoweringMachinePlan.planTrace graph placement distinct vertex (commands n ports direction)
    (fun q => labels (.inl q)) (some (labels (.inr (.inl ())))) program
    (fun q => atLabels (.inl q)) base suffix ready.1 (emptyBuffer (bufferSize d n))
  rw [planSteps_eq, plan_entry_eq] at hp
  let mid := afterPlan graph n placement vertex ports direction base
  have hinput : mid (placement (.inl 10)) = PoweringMachineRow.encodeBits
      (List.ofFn (PoweringRowData.rowBits graph n (direction, vertex, ports))) ++ [] := by
    dsimp only [mid, afterPlan, commands]
    have h := PoweringMachinePlan.rowPlan_output graph n ports direction placement distinct vertex base suffix ready.1
    simpa only [ready.2, List.append_nil, PoweringRowData.dataTape_eq] using h
  have hr := PoweringMasterState.step_rowAt_clean (t := n + 1) (placement (.inl 10)) output
    (PoweringRowData.fixedLabelAt d n)
    (some (labels (.inr (.inr (PoweringMachineRowHeaders.entry n))))) program (labels (.inr (.inl ())))
    (atLabels (.inr (.inl ()))) (Ne.symm (outside _))
    (PoweringRowData.rowBits graph n (direction, vertex, ports))
    (emptyBuffer (bufferSize d n)) [] mid hinput
  rw [rowBlock_eq_rowRelation] at hr
  have hm := afterEmit_ready graph n placement distinct output outside vertex ports direction base suffix ready
  have hh := (PoweringMachineRowHeaders.headerTrace graph n (by unfold capacity; omega)
    (headerPlacement placement output) (headerPlacement_injective placement distinct output outside)
    vertex ports direction (fun q => labels (.inr (.inr q))) exit program
    (fun q => atLabels (.inr (.inr q)))
    (afterEmit graph n placement output vertex ports direction base)
    (by simpa [headerPlacement, PoweringMachineTapes.table] using hm.1.table)
    (by simpa [headerPlacement, PoweringMachineTapes.scratch] using hm.1.scratch) suffix
    (by simpa [headerPlacement, PoweringMachineTapes.start] using hm.1.source)
    (emptyBuffer (bufferSize d n), false, none) none).1
  rw [steps, Nat.add_comm, Function.iterate_add_apply, Function.iterate_succ_apply']
  change (advance (TM2.step program))^[PoweringMachineRowHeaders.steps graph n vertex ports direction]
    (advance (TM2.step program) ((advance (TM2.step program))^[planSteps graph vertex (commands n ports direction)]
      (some ⟨some (labels (planMain (commands n ports direction) (.inl ()))),
        MachineUnaryEqualityBit.clean (emptyBuffer (bufferSize d n)), base⟩))) = _
  rw [hp]
  simp only [advance_some]
  change (advance (TM2.step program))^[PoweringMachineRowHeaders.steps graph n vertex ports direction]
    (TM2.step program ⟨some (labels (.inr (.inl ()))),
      PoweringMasterState.withBuffer (emptyBuffer (bufferSize d n)), mid⟩) = _
  rw [hr]
  exact hh

def budget (d n inputLength : Nat) : Nat :=
  PoweringPlanBudget.rowBudget d n inputLength + 1 +
    ((14 * (n + 1) + 4) * inputLength + 12 * (n + 1) + 6)

theorem steps_le (graph : PortTables.Table vertices d) (vertex : Fin vertices)
    (n : Nat) (ports : Fin (n + 1) → Fin d) (direction : Bool) :
    steps graph vertex n ports direction ≤ budget d n (PortTables.tableBits graph).length := by
  have hp := PoweringPlanBudget.rowPlan_steps_le graph n ports direction id vertex (fun _ => [])
  rw [planSteps_eq] at hp
  have hh := PoweringMachineRowHeaders.steps_le graph n vertex ports direction
  change planSteps graph vertex (commands n ports direction) ≤
    PoweringPlanBudget.rowBudget d n (PortTables.tableBits graph).length at hp
  unfold steps budget
  omega

end MaxCutGames.Foundations.Complexity.PoweringMachineRowBody

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineVertex
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.PoweringMachineVertex

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

def sequenceInstruction (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (ops : List (Command d n)) (labels : SequenceLabel ops → Λ)
    (exit : Option Λ) : SequenceLabel ops → TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  MachineFiniteSequence.instruction LocalLabel
    (fun j => PoweringMachineRowBody.entry n (ports j) (direction j))
    (fun j => PoweringMachineRowBody.instruction n placement output (ports j) (direction j))
    ops labels exit

def instruction (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (output : K) (labels : Label d n → Λ) (exit : Option Λ) :
    Label d n → TM2.Stmt (fun _ : K => Bool) Λ (State d n) :=
  sequenceInstruction n placement output (commands d n) labels exit

def budget (d n inputLength : Nat) : Nat :=
  PoweringTableLayout.blockSize d n * PoweringMachineRowBody.budget d n inputLength

theorem costSum_le (graph : PortTables.Table vertices d) (vertex : Fin vertices)
    (n : Nat) (ops : List (Command d n)) :
    costSum graph vertex n ops ≤
      ops.length * PoweringMachineRowBody.budget d n (PortTables.tableBits graph).length := by
  induction ops with
  | nil => simp only [costSum, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons j ops ih =>
      have hfirst := PoweringMachineRowBody.steps_le graph vertex n (ports j) (direction j)
      change PoweringMachineRowBody.steps graph vertex n (ports j) (direction j) +
        costSum graph vertex n ops ≤ _
      simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        Nat.add_le_add hfirst ih

theorem steps_le (graph : PortTables.Table vertices d) (vertex : Fin vertices) (n : Nat) :
    steps graph vertex n ≤ budget d n (PortTables.tableBits graph).length := by
  simpa only [steps, budget, commands_length] using costSum_le graph vertex n (commands d n)

theorem sequenceTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (ops : List (Command d n))
    (labels : SequenceLabel ops → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = sequenceInstruction n placement output ops labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    (advance (TM2.step program))^[sequenceSteps graph n placement output vertex ops base]
      (some ⟨sequenceEntry ops labels exit,
        PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), base⟩) =
      some ⟨exit, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        sequenceTapes graph n placement output vertex ops base⟩ := by
  apply MachineFiniteSequence.trace LocalLabel
    (fun j => PoweringMachineRowBody.entry n (ports j) (direction j))
    (fun j => PoweringMachineRowBody.instruction n placement output (ports j) (direction j))
    (result graph n placement output vertex)
    (fun j _ => PoweringMachineRowBody.steps graph vertex n (ports j) (direction j))
    program (PoweringMachineRowBody.Ready graph n placement vertex suffix)
    (fun _ => PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)) id ops
  · intro j _ tapes good
    exact PoweringMachineRowBody.finalTapes_ready graph n placement distinct output outside
      vertex (ports j) (direction j) tapes suffix good
  · intro j _ localLabels localExit atLocal tapes good
    exact PoweringMachineRowBody.rowTrace graph n placement distinct output outside vertex
      (ports j) (direction j) localLabels localExit program atLocal tapes suffix good
  · exact atLabels
  · exact ready

theorem vertexTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (labels : Label d n → Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atLabels : ∀ l, program (labels l) = instruction n placement output labels exit l)
    (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    (advance (TM2.step program))^[steps graph vertex n]
      (some ⟨entry d n labels exit,
        PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), base⟩) =
      some ⟨exit, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output vertex base⟩ := by
  have h := sequenceTrace graph n placement distinct output outside vertex (commands d n)
    labels exit program atLabels base suffix ready
  rw [sequenceSteps_eq] at h
  exact h

theorem sequenceTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (ops : List (Command d n)) (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    sequenceTapes graph n placement output vertex ops base output =
      ops.reverse.flatMap (rowBits graph n vertex) ++ base output := by
  induction ops generalizing base with
  | nil => rfl
  | cons j ops ih =>
      have nextReady := PoweringMachineRowBody.finalTapes_ready graph n placement distinct
        output outside vertex (ports j) (direction j) base suffix ready
      change sequenceTapes graph n placement output vertex ops
        (result graph n placement output vertex j base) output = _
      dsimp only [result]
      rw [ih _ nextReady, PoweringMachineRowBody.finalTapes_output graph n placement distinct
        output outside vertex (ports j) (direction j) base suffix ready]
      simp only [List.reverse_cons, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.append_assoc, rowBits]

theorem finalTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n) → K)
    (distinct : Function.Injective placement) (output : K) (outside : ∀ i, output ≠ placement i)
    (vertex : Fin vertices) (base : K → List Bool) (suffix : List Bool)
    (ready : PoweringMachineRowBody.Ready graph n placement vertex suffix base) :
    finalTapes graph n placement output vertex base output =
      PoweringTableLayout.vertexRowBits graph n vertex ++ base output := by
  rw [finalTapes, sequenceTapes_output graph n placement distinct output outside vertex
    (commands d n) base suffix ready]
  simp only [commands, List.reverse_reverse, rows_eq_vertexRowBits]

end MaxCutGames.Foundations.Complexity.PoweringMachineVertex

/-! Actual variable-size vertex enumeration. The finite guard decrements the
live unary counter, a one-step bridge enters the fixed vertex producer, and the
producer returns to the guard. Work tapes may change after every vertex. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineOuterLoop

open Turing MachineComposition PCP

variable {K Λ : Type} [DecidableEq K] {vertices d n : Nat}

theorem steps_le (graph : PortTables.Table vertices d) (n remaining : Nat)
    (bounded : remaining ≤ vertices) :
    steps graph n remaining bounded ≤
      remaining * (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1 := by
  induction remaining with
  | zero => simp [steps]
  | succ r ih =>
      have hv := PoweringMachineVertex.steps_le graph (⟨r, by omega⟩ : Fin vertices) n
      have hi := ih (by omega)
      simp only [steps, Nat.add_mul, Nat.one_mul]
      omega

theorem prefixRows_ofFn (graph : PortTables.Table vertices d) (n remaining : Nat)
    (bounded : remaining ≤ vertices) :
    prefixRows graph n remaining =
      (List.ofFn (fun i : Fin remaining =>
        PoweringTableLayout.vertexRowBits graph n (Fin.castLE bounded i))).flatten := by
  induction remaining with
  | zero => rfl
  | succ r ih =>
      have hr : r < vertices := by omega
      rw [prefixRows, dite_eq_left hr, List.ofFn_succ_last, List.flatten_append]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      change prefixRows graph n r ++ PoweringTableLayout.vertexRowBits graph n ⟨r, hr⟩ =
        (List.ofFn (fun i : Fin r => PoweringTableLayout.vertexRowBits graph n
          (Fin.castLE (show r ≤ vertices by omega) i))).flatten ++
          PoweringTableLayout.vertexRowBits graph n ⟨r, hr⟩
      rw [ih]

theorem prefixRows_all (graph : PortTables.Table vertices d) (n : Nat) :
    prefixRows graph n vertices =
      (List.finRange vertices).flatMap (PoweringTableLayout.vertexRowBits graph n) := by
  rw [prefixRows_ofFn graph n vertices (Nat.le_refl _)]
  simp only [List.finRange, List.flatMap_def, List.map_ofFn]
  rfl

theorem finalTapes_output (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    finalTapes graph n placement output remaining bounded base output =
      prefixRows graph n remaining ++ base output := by
  induction remaining generalizing base with
  | zero =>
      exact MachineUnaryCounter.counterTapes_other (placement (.inl 1)) output (outside _)
        base 0 []
  | succ r ih =>
      let vertex : Fin vertices := ⟨r, by omega⟩
      let current := counter placement base r
      have vertexReady := ready_vertex graph n placement distinct base ready vertex
      have nextReady := PoweringMachineVertex.finalTapes_ready graph n placement distinct
        output outside vertex current [] vertexReady
      change finalTapes graph n placement output r (by omega)
        (PoweringMachineVertex.finalTapes graph n placement output vertex current) output = _
      rw [ih (by omega) _ (ready_of_vertex graph n placement _ vertex nextReady),
        PoweringMachineVertex.finalTapes_output graph n placement distinct output outside
          vertex current [] vertexReady]
      have hc : current output = base output :=
        MachineUnaryCounter.counterTapes_other (placement (.inl 1)) output (outside _) base r []
      rw [hc, prefixRows, dite_eq_left vertex.isLt, List.append_assoc]

theorem loopTrace (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (guardLabel bridgeLabel exitLabel : Λ) (labels : PoweringMachineVertex.Label d n → Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atGuard : program guardLabel =
      MachineUnaryCounter.guard (placement (.inl 1)) bridgeLabel exitLabel)
    (atBridge : program bridgeLabel = bridge d n labels guardLabel)
    (atVertex : ∀ l, program (labels l) =
      PoweringMachineVertex.instruction n placement output labels (some guardLabel) l)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    (advance (TM2.step program))^[steps graph n remaining bounded]
      (some ⟨some guardLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        counter placement base remaining⟩) =
      some ⟨some exitLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output remaining bounded base⟩ := by
  let initial := PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)
  induction remaining generalizing base with
  | zero =>
      simpa only [steps, finalTapes, counter, initial, PoweringMasterState.clean,
        PoweringMasterState.withBuffer] using
        MachineUnaryCounter.guardTrace_zero (placement (.inl 1)) guardLabel bridgeLabel exitLabel
          program atGuard base [] initial.1 none
  | succ r ih =>
      let vertex : Fin vertices := ⟨r, by omega⟩
      let current := counter placement base r
      let next := PoweringMachineVertex.finalTapes graph n placement output vertex current
      have vertexReady : PoweringMachineRowBody.Ready graph n placement vertex [] current :=
        ready_vertex graph n placement distinct base ready vertex
      have nextVertexReady := PoweringMachineVertex.finalTapes_ready graph n placement distinct
        output outside vertex current [] vertexReady
      have nextReady : Ready graph n placement next :=
        ready_of_vertex graph n placement next vertex nextVertexReady
      have sameCounter : counter placement next r = next := by
        have hs := nextVertexReady.1.source
        change next (placement (.inl 1)) = encodeWord r ++ [] at hs
        unfold counter MachineUnaryCounter.counterTapes
        rw [← hs]
        exact Function.update_eq_self _ _
      have tailRun := ih (by omega) next nextReady
      rw [sameCounter] at tailRun
      have guardRun : advance (TM2.step program)
          (some ⟨some guardLabel, initial, counter placement base (r + 1)⟩) =
          some ⟨some bridgeLabel, initial, current⟩ := by
        simpa only [advance_some, current, counter, initial, PoweringMasterState.clean,
          PoweringMasterState.withBuffer] using
          MachineUnaryCounter.guardStep_succ (placement (.inl 1)) guardLabel bridgeLabel exitLabel
            program atGuard base r [] initial.1 none
      have bridgeRun : advance (TM2.step program)
          (some ⟨some bridgeLabel, initial, current⟩) =
          some ⟨PoweringMachineVertex.entry d n labels (some guardLabel), initial, current⟩ := by
        change some (TM2.stepAux (program bridgeLabel) initial current) = _
        rw [atBridge, vertexEntry]
        rfl
      have vertexRun := PoweringMachineVertex.vertexTrace graph n placement distinct output outside
        vertex labels (some guardLabel) program atVertex current [] vertexReady
      change (advance (TM2.step program))^[2 + PoweringMachineVertex.steps graph vertex n +
          steps graph n r (by omega)]
        (some ⟨some guardLabel, initial, counter placement base (r + 1)⟩) = _
      rw [show 2 + PoweringMachineVertex.steps graph vertex n + steps graph n r (by omega) =
          (steps graph n r (by omega) + PoweringMachineVertex.steps graph vertex n) + 1 + 1 by omega,
        Function.iterate_succ_apply, guardRun, Function.iterate_succ_apply, bridgeRun,
        Function.iterate_add_apply, vertexRun]
      exact tailRun

def loopInTime (graph : PortTables.Table vertices d) (n : Nat)
    (placement : Placement K n) (distinct : Function.Injective placement)
    (output : K) (outside : ∀ i, output ≠ placement i)
    (guardLabel bridgeLabel exitLabel : Λ) (labels : PoweringMachineVertex.Label d n → Λ)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (State d n))
    (atGuard : program guardLabel =
      MachineUnaryCounter.guard (placement (.inl 1)) bridgeLabel exitLabel)
    (atBridge : program bridgeLabel = bridge d n labels guardLabel)
    (atVertex : ∀ l, program (labels l) =
      PoweringMachineVertex.instruction n placement output labels (some guardLabel) l)
    (remaining : Nat) (bounded : remaining ≤ vertices) (base : K → List Bool)
    (ready : Ready graph n placement base) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some guardLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        counter placement base remaining⟩
      (some ⟨some exitLabel, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        finalTapes graph n placement output remaining bounded base⟩)
      (remaining * (PoweringMachineVertex.budget d n (PortTables.tableBits graph).length + 2) + 1) where
  steps := steps graph n remaining bounded
  evals_in_steps := loopTrace graph n placement distinct output outside guardLabel bridgeLabel
    exitLabel labels program atGuard atBridge atVertex remaining bounded base ready
  steps_le_m := steps_le graph n remaining bounded

end MaxCutGames.Foundations.Complexity.PoweringMachineOuterLoop

/-!
# Physical output headers followed by complete work-tape cleanup

The finite program first copies the dart-count word onto the existing row
output, then copies the vertex-count word, and finally drains every tape except
the output. Both unary header values are read from physical tapes; they do not
parameterize the program. Header sources and their unread suffixes are restored
by the two copies before cleanup. The final configuration contains the full
encoded header and rows on the output tape and empty words on every other tape.
-/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineFinish

open Turing MachineComposition

variable {K Λ σ : Type} [DecidableEq K] {N : Nat}

theorem afterHeaders_other (output : K) (base : K → List Bool) (n m : Nat)
    (k : K) (hk : k ≠ output) : afterHeaders output base n m k = base k :=
  Function.update_of_ne hk _ _

/-- Exact cleanup cost is computed on the actual post-copy tape contents. -/
def steps (enumeration : Fin N ≃ K) (output : K) (base : K → List Bool) (n m : Nat) : Nat :=
  copySteps n m + MachineDrainMany.steps (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m)

theorem afterHeaders_length_le (output : K) (base : K → List Bool) (n m bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) (k : K) :
    (afterHeaders output base n m k).length ≤ bound + n + m + 2 := by
  by_cases hk : k = output
  · subst k
    rw [afterHeaders_output]
    have hb := bounded output
    simp only [List.length_append, encodeWords, encodeWord_length, List.length_nil]
    omega
  · rw [afterHeaders_other output base n m k hk]
    have hb := bounded k
    omega

/-- A uniform pre-cleanup stack bound gives a linear finishing budget. -/
theorem steps_le_uniform (enumeration : Fin N ≃ K) (output : K)
    (base : K → List Bool) (n m bound : Nat)
    (bounded : ∀ k, (base k).length ≤ bound) :
    steps enumeration output base n m ≤ 2 * (n + m) + 6 + N * (bound + n + m + 3) := by
  have hc := MachineDrainMany.steps_le_uniform (MachineDrainMany.workTapes enumeration output)
    (afterHeaders output base n m) (bound + n + m + 2)
    (afterHeaders_length_le output base n m bound bounded)
  have hl := MachineDrainMany.workTapes_length_le enumeration output
  have hm := Nat.mul_le_mul_right (bound + n + m + 3) hl
  rw [show bound + n + m + 2 + 1 = bound + n + m + 3 by omega] at hc
  unfold steps
  rw [copySteps_eq]
  exact Nat.add_le_add_left (hc.trans hm) _

end MaxCutGames.Foundations.Complexity.PoweringMachineFinish

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineGlobal
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The fixed global powering machine

For fixed degree `d` and radius parameter `n`, this is one concrete finite
machine: initialization, unary vertex guard, the fixed vertex-row producer,
and output-header/cleanup instructions are connected by explicit labels.
Its definition takes no input graph, vertex count, or program callback.

The code equations below expose each actual branch for the separate runtime
proof. The variable-size input graph and counters reside on physical tapes.
-/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineGlobal

open Turing

/-- The complete program, fixed solely by the reduction parameters. -/
def program (d n : Nat) :
    Label d n → TM2.Stmt (fun _ : Tape n => Bool) (Label d n) (State d n)
  | .inl label => PoweringMachineInitialize.instruction
      (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
      (PCP.PoweringTableLayout.blockSize d n) (initLabels d n) (some (guardLabel d n)) label
  | .inr (.inl false) => MachineUnaryCounter.guard
      (placement n (PoweringMachineTapes.start (PoweringMachineRowBody.capacity n)))
      (bridgeLabel d n) (finishEntry d n)
  | .inr (.inl true) => PoweringMachineOuterLoop.bridge d n (vertexLabels d n) (guardLabel d n)
  | .inr (.inr (.inl label)) => PoweringMachineVertex.instruction n (placement n) (outputTape n)
      (vertexLabels d n) (some (guardLabel d n)) label
  | .inr (.inr (.inr label)) => PoweringMachineFinish.instruction (enumeration n)
      (headerVertices n) (headerDarts n) (outputTape n)
      (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
      (finishLabels d n) label

@[simp] theorem atInit (d n : Nat) (label : PoweringMachineInitialize.Label) :
    program d n (initLabels d n label) = PoweringMachineInitialize.instruction
      (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
      (PCP.PoweringTableLayout.blockSize d n) (initLabels d n) (some (guardLabel d n)) label := rfl

@[simp] theorem atGuard (d n : Nat) :
    program d n (guardLabel d n) = MachineUnaryCounter.guard
      (placement n (PoweringMachineTapes.start (PoweringMachineRowBody.capacity n)))
      (bridgeLabel d n) (finishEntry d n) := rfl

@[simp] theorem atBridge (d n : Nat) :
    program d n (bridgeLabel d n) =
      PoweringMachineOuterLoop.bridge d n (vertexLabels d n) (guardLabel d n) := rfl

@[simp] theorem atVertex (d n : Nat) (label : PoweringMachineVertex.Label d n) :
    program d n (vertexLabels d n label) = PoweringMachineVertex.instruction n
      (placement n) (outputTape n) (vertexLabels d n) (some (guardLabel d n)) label := rfl

@[simp] theorem atFinish (d n : Nat) (label : FinishLabel n) :
    program d n (finishLabels d n label) = PoweringMachineFinish.instruction (enumeration n)
      (headerVertices n) (headerDarts n) (outputTape n)
      (placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)))
      (finishLabels d n) label := rfl

/-- All state and control spaces are explicit finite types; only the tapes
hold variable-size data. -/
def machine (d n : Nat) : FinTM2 where
  K := Tape n
  k₀ := inputTape n
  k₁ := outputTape n
  Γ _ := Bool
  Λ := Label d n
  main := main d n
  σ := State d n
  initialState := PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n)
  m := program d n

@[simp] theorem machine_code (d n : Nat) (label : Label d n) :
    (machine d n).m label = program d n label := rfl

@[simp] theorem machine_main (d n : Nat) : (machine d n).main = main d n := rfl

@[simp] theorem machine_initialState (d n : Nat) :
    (machine d n).initialState = PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n) := rfl

end MaxCutGames.Foundations.Complexity.PoweringMachineGlobal

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_PoweringInitializeFrame
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.PoweringInitializeFrame

open Turing PCP

variable {vertices d : Nat}

/-- The extra tapes initially contain only the live serialized table. -/
def initialExtra (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineInitialize.ExtraTape (PoweringMachineRowBody.capacity n) → List Bool :=
  fun tape => if tape = .inl (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))
    then PortTables.tableBits graph else []

@[simp] theorem initialExtra_table (graph : PortTables.Table vertices d) (n : Nat) :
    initialExtra graph n (.inl (PoweringMachineTapes.table (PoweringMachineRowBody.capacity n))) =
      PortTables.tableBits graph := by simp [initialExtra]

@[simp] theorem initialExtra_scratch (graph : PortTables.Table vertices d) (n : Nat) :
    initialExtra graph n
      (.inl (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n))) = [] := by
  simp [initialExtra, PoweringMachineTapes.table, PoweringMachineTapes.scratch]

/-- Exact frame left by initialization, including the preserved input table. -/
def preparedTapes (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineGlobal.Tape n → List Bool :=
  PoweringMachineInitialize.mergeTapes
    (PoweringMachineLoop.finalTapes (PoweringTableLayout.blockSize d n) vertices [])
    (initialExtra graph n)

theorem prepared_commonRole (graph : PortTables.Table vertices d) (n : Nat)
    (j : Fin 11) (hne : j ≠ 1) :
    preparedTapes graph n (PoweringMachineGlobal.placement n (.inl j)) =
      if j = 0 then PortTables.tableBits graph else [] := by
  simp [preparedTapes, PoweringMachineGlobal.placement,
    PoweringMachineInitialize.commonPlacement, PoweringMachineTapes.start,
    PoweringMachineInitialize.mergeTapes, initialExtra, PoweringMachineTapes.table, hne]

theorem prepared_ready (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineOuterLoop.Ready graph n (PoweringMachineGlobal.placement n)
      (preparedTapes graph n) := by
  constructor
  · simpa using prepared_commonRole graph n 0 (by decide)
  · simpa using prepared_commonRole graph n 5 (by decide)
  · simpa using prepared_commonRole graph n 8 (by decide)
  · simpa using prepared_commonRole graph n 9 (by decide)
  · simpa using prepared_commonRole graph n 10 (by decide)

@[simp] theorem prepared_start (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.placement n (.inl 1)) =
      encodeWord vertices := by
  simpa only [preparedTapes, PoweringMachineGlobal.placement, PoweringMachineTapes.start] using
    PoweringMachineInitialize.final_counter (PoweringMachineRowBody.capacity n)
      (PoweringTableLayout.blockSize d n) vertices (initialExtra graph n)

/-- Installing the outer-loop counter changes nothing: it is already present. -/
theorem prepared_counter (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineOuterLoop.counter (PoweringMachineGlobal.placement n)
      (preparedTapes graph n) vertices = preparedTapes graph n := by
  unfold PoweringMachineOuterLoop.counter MachineUnaryCounter.counterTapes
  rw [List.append_nil, ← prepared_start graph n]
  simp only [Function.update_eq_self]

@[simp] theorem prepared_output (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.outputTape n) = [] := by
  simp [preparedTapes, PoweringMachineGlobal.outputTape, PoweringMachineInitialize.finalOutput,
    PoweringMachineInitialize.mergeTapes, initialExtra]

@[simp] theorem prepared_vertices (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.headerVertices n) = encodeWord vertices := rfl

@[simp] theorem prepared_darts (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (PoweringMachineGlobal.headerDarts n) =
      encodeWord (PoweringTableLayout.blockSize d n * vertices) := rfl

@[simp] theorem prepared_source (graph : PortTables.Table vertices d) (n : Nat) :
    preparedTapes graph n (.inl PoweringMachineLoop.HeaderTape.source) = [] := rfl

def preparedCfg (graph : PortTables.Table vertices d) (n : Nat) :
    (PoweringMachineGlobal.machine d n).Cfg :=
  ⟨some (PoweringMachineGlobal.guardLabel d n),
    PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n), preparedTapes graph n⟩

/-- A homogeneous Boolean description of the machine's literal initial stacks. -/
theorem initialGlobalTapes_eq (graph : PortTables.Table vertices d) (n : Nat) :
    PoweringMachineInitialize.initialGlobalTapes (initialExtra graph n) =
      fun tape => if tape = PoweringMachineGlobal.inputTape n
        then PortTables.tableBits graph else [] := by
  funext tape
  cases tape with
  | inl field =>
    simp [PoweringMachineInitialize.initialGlobalTapes, PoweringMachineInitialize.mergeTapes,
      PoweringMachineGlobal.inputTape, PoweringMachineGlobal.placement,
      PoweringMachineInitialize.commonPlacement_table]
  | inr field =>
    simp [PoweringMachineInitialize.initialGlobalTapes, PoweringMachineInitialize.mergeTapes,
      PoweringMachineGlobal.inputTape, PoweringMachineGlobal.placement,
      PoweringMachineInitialize.commonPlacement_table, initialExtra]

theorem machine_initialStacks_inline_PoweringInitializeFrame (d n : Nat) (input : List Bool) :
    (initList (PoweringMachineGlobal.machine d n) input).stk =
      fun tape => if tape = PoweringMachineGlobal.inputTape n then input else [] := by
  funext tape
  by_cases h : tape = PoweringMachineGlobal.inputTape n
  · subst tape
    simp [initList, PoweringMachineGlobal.machine]
    rfl
  · simp only [initList, PoweringMachineGlobal.machine]
    erw [dite_eq_right h, ite_eq_right h]

/-- The trace starts at `Turing.initList`, with no assumed prepared work tapes. -/
theorem initList_eq (graph : PortTables.Table vertices d) (n : Nat) :
    initList (PoweringMachineGlobal.machine d n) (PortTables.tableBits graph) =
      ⟨some (PoweringMachineGlobal.main d n),
        PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        PoweringMachineInitialize.initialGlobalTapes (initialExtra graph n)⟩ := by
  have ht := (machine_initialStacks_inline_PoweringInitializeFrame d n (PortTables.tableBits graph)).trans
    (initialGlobalTapes_eq graph n).symm
  exact congrArg (TM2.Cfg.mk _ _) ht

/-- The first serialized input field is the actual number of vertices. -/
theorem tableBits_head (graph : PortTables.Table vertices d) :
    PortTables.tableBits graph = encodeWord vertices ++
      encodeWords (PortTables.tableWords graph).tail := rfl

/-- Initialization of the actual global program from its literal input list.
Every work-tape readiness property follows from the explicit final frame. -/
def initializeInTime (graph : PortTables.Table vertices d) (n : Nat) :
    StateTransition.EvalsToInTime (PoweringMachineGlobal.machine d n).step
      (initList (PoweringMachineGlobal.machine d n) (PortTables.tableBits graph))
      (some (preparedCfg graph n)) (3 * vertices + 5) := by
  rw [initList_eq]
  exact PoweringMachineInitialize.initializeAtInTime
    (PoweringMachineRowBody.capacity n) (PoweringMachineRowBody.bufferSize d n)
    (PoweringTableLayout.blockSize d n) vertices
    (PoweringMachineGlobal.initLabels d n) (some (PoweringMachineGlobal.guardLabel d n))
    (PoweringMachineGlobal.program d n) (PoweringMachineGlobal.atInit d n)
    (initialExtra graph n) (encodeWords (PortTables.tableWords graph).tail)
    (by rw [initialExtra_table, tableBits_head]) (initialExtra_scratch graph n)
    (PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n))

end MaxCutGames.Foundations.Complexity.PoweringInitializeFrame

/-!
# Concrete global configurations and tape separation

These lemmas specialize the checked initializer placement to the fixed global
machine. The final configuration is the actual `Turing.haltList`, with the
machine's clean initial register and only the output tape populated.
-/

namespace MaxCutGames.Foundations.Complexity.PoweringGlobalConfiguration

open Turing PoweringMachineGlobal

theorem headerVertices_ne_placement (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    headerVertices n ≠ placement n tape :=
  Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header
    (PoweringMachineRowBody.capacity n) tape .vertices (by decide))

theorem headerDarts_ne_placement (n : Nat)
    (tape : PoweringMachineTapes.Tape (PoweringMachineRowBody.capacity n)) :
    headerDarts n ≠ placement n tape :=
  Ne.symm (PoweringMachineInitialize.commonPlacement_ne_header
    (PoweringMachineRowBody.capacity n) tape .darts (by decide))

theorem headerVertices_ne_output (n : Nat) : headerVertices n ≠ outputTape n := by
  simp [headerVertices, outputTape, PoweringMachineInitialize.finalOutput]

theorem headerDarts_ne_output (n : Nat) : headerDarts n ≠ outputTape n := by
  simp [headerDarts, outputTape, PoweringMachineInitialize.finalOutput]

theorem headerVertices_ne_scratch (n : Nat) :
    headerVertices n ≠
      placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)) :=
  headerVertices_ne_placement n _

theorem headerDarts_ne_scratch (n : Nat) :
    headerDarts n ≠
      placement n (PoweringMachineTapes.scratch (PoweringMachineRowBody.capacity n)) :=
  headerDarts_ne_placement n _

/-- A Boolean tape alphabet is constant, so the type-equality transport in
the bundled machine's dependent stack specification leaves its word intact. -/
@[simp] theorem boolList_mpr_eq (h : List Bool = List Bool) (bits : List Bool) :
    h.mpr bits = bits := rfl

/-- The dependent stack definition in `haltList` is exactly the Boolean output
tape shape produced by the checked finite cleanup program. -/
theorem haltList_tapes (d n : Nat) (output : List Bool) :
    (Turing.haltList (machine d n) output).stk =
      MachineDrainMany.haltTapes (outputTape n) output := by
  funext tape
  simp only [Turing.haltList, machine, MachineDrainMany.haltTapes]
  by_cases h : tape = outputTape n
  · erw [dite_eq_left h, ite_eq_left h]
    rfl
  · erw [dite_eq_right h, ite_eq_right h]

/-- Exact identity with the global machine's actual output specification. -/
theorem haltList_eq (d n : Nat) (output : List Bool) :
    Turing.haltList (machine d n) output =
      (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
        MachineDrainMany.haltTapes (outputTape n) output⟩ : (machine d n).Cfg) := by
  change (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
      (Turing.haltList (machine d n) output).stk⟩ : (machine d n).Cfg) = _
  exact congrArg
    (fun tapes => (⟨none, PoweringMasterState.clean (PoweringMachineRowBody.bufferSize d n),
      tapes⟩ : (machine d n).Cfg)) (haltList_tapes d n output)

end MaxCutGames.Foundations.Complexity.PoweringGlobalConfiguration

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Games_PoweringPolynomialBudget
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.Complexity.PoweringPolynomialBudget

open PCP

/-- The exact affine polynomial of one concrete row body. -/
noncomputable def rowTime (d n : Nat) : Polynomial Nat :=
  Polynomial.C (PoweringMachineRowBody.bufferSize d n) *
      (Polynomial.C (28 * (2 * (n + 1)) + 10) * Polynomial.X +
        Polynomial.C (24 * (2 * (n + 1)) + 15)) + Polynomial.C 1 +
    (Polynomial.C (14 * (n + 1) + 4) * Polynomial.X +
      Polynomial.C (12 * (n + 1)) + Polynomial.C 6)

@[simp] theorem rowTime_eval (d n inputLength : Nat) :
    (rowTime d n).eval inputLength = PoweringMachineRowBody.budget d n inputLength := by
  simp only [rowTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, PoweringMachineRowBody.budget, PoweringPlanBudget.rowBudget,
    PoweringPlanBudget.fieldBudget, PoweringMachineRowBody.bufferSize, Nat.add_assoc]

/-- The actual fixed number of row commands multiplies the row polynomial. -/
noncomputable def vertexTime (d n : Nat) : Polynomial Nat :=
  Polynomial.C (PoweringTableLayout.blockSize d n) * rowTime d n

end MaxCutGames.Foundations.Complexity.PoweringPolynomialBudget

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_MachineRegularTableTrace
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial bounds for the actual regularization subcalls. These lemmas
bound the established step counts; they do not assume any machine execution. -/

/-! Polynomial runtime for the actual original-vertex body. The size parameter
includes the already accumulated output, so no output-prefix premise is used. -/

/-!
# Bounds for actual dummy-owner execution

The size parameter includes the old output length. During the owner loop,
newly emitted dummy blocks are bounded by the actual complete regularized
table codec. No hypothesis about a machine body's execution supplies a bound.
-/

namespace MaxCutGames.Foundations.Complexity.MachineRegularOwnerBodyBounds

open Turing MachineComposition PCP PreprocessingCloudIndex PreprocessingRegularTables
open PreprocessingMachineBounds PreprocessingRegularLoopWords

noncomputable def timePolynomial : Polynomial Nat :=
  prePolynomial + MachineRegularExecutionBounds.familyPolynomial + loopPolynomial +
    cleanupPolynomial + 2

end MaxCutGames.Foundations.Complexity.MachineRegularOwnerBodyBounds

/-! A polynomial cap for the actual two regularization loops, their header,
and all seven final drain loops. Per-call sizes include the complete stored
output prefix. -/
namespace MaxCutGames.Foundations.Complexity.MachineRegularTable.Top

open Turing MachineComposition PCP PreprocessingRegularTables
open PreprocessingRegularBounds PreprocessingMachineBounds

noncomputable def ownerLoopPolynomial : Polynomial Nat :=
  Polynomial.X *
    (MachineRegularOwnerBodyBounds.timePolynomial.comp
      (Polynomial.X + regularPolynomial) + 2)

end MaxCutGames.Foundations.Complexity.MachineRegularTable.Top

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_PoweringMachineRuntime
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete execution of the one fixed powering machine on the actual
port-table input and generic graph-table output encodings. The varying vertex
count remains on unary tapes throughout. -/

namespace MaxCutGames.Foundations.Complexity.PoweringMachineRuntime

open Turing MachineComposition PCP PoweringMachineGlobal

variable {vertices d : Nat}

/-- The actual work tapes after all vertex blocks, before final headers. -/
def beforeFinish (graph : PortTables.Table vertices d) (n : Nat) : Tape n → List Bool :=
  PoweringMachineOuterLoop.finalTapes graph n (placement n) (outputTape n)
    vertices (Nat.le_refl _) (PoweringInitializeFrame.preparedTapes graph n)

end MaxCutGames.Foundations.Complexity.PoweringMachineRuntime

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RawInitialTables
attribute [-instance] _root_.OAI.MaxCutGames.Appendix.A5Passage.pairFintype _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.sourceAnswerNonempty _root_.OAI.MaxCutGames.Clean.ActualAdviceStochasticBridge.targetAnswerNonempty _root_.OAI.MaxCutGames.Decoder.AdviceLaw.observedRowsFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.MaxCutGames.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.MaxCutGames.Fourier.MatrixRestrictions.parameterFintype _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Integration.AddressTupleBody.labelFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.basisMapFintype _root_.OAI.MaxCutGames.Inverse.KMSBasisComparison.functionalFintype _root_.OAI.MaxCutGames.Inverse.Shortcode.Slice.directionsFintype _root_.OAI.MaxCutGames.Outer.Clone100Triples.instNonemptyGoodTriple _root_.OAI.MaxCutGames.Quadratic.binaryFieldFintype _root_.OAI.MaxCutGames.Quadratic.blockOrientationFintype _root_.OAI.MaxCutGames.Quadratic.fieldLineFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.dualFintype _root_.OAI.MaxCutGames.Reduction.ActualGame.mapFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelFintype _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit structural numberings of the raw 3SAT incidence graph. Unused
declared variable names are retained; their unary input header pays for them.
The graph has one dummy vertex and one tautological loop, even for an empty
formula. No input-dependent choice of a finite enumeration is made. -/

/-!
A stable type of finite graphs over one fixed alphabet. Vertex and dart types,
their finite enumeration and equality data, and the actual constraint graph
are stored together. The gap is computed from that graph's actual finite
labeling minimum. This mathematical bundle is not a serialized machine input;
no finite numbering is chosen here.
-/

/-! The concrete numbered amplification round, with one fixed base expander.
Every intermediate is an actual stored table, with explicit finite coordinates.
The running-time certificate is a separate theorem about these same functions. -/

namespace MaxCutGames.Foundations.PCP.RoundTables

def initial (F : Target.Formula) : Input :=
  ⟨RawInitialTables.table F, RawInitialTables.table_darts_positive F⟩

noncomputable def gap (input : Input) : ℝ := (GraphTables.semantics input.val).gap

end MaxCutGames.Foundations.PCP.RoundTables

/-!
The finite iteration and size arithmetic for an amplification transformation.
The transformation itself must be supplied by the actual graph construction;
these theorems do not assert that such a transformation exists.  In particular,
the polynomial size estimate below is not a machine runtime certificate.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RawInitialMachineBudget
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial arithmetic for the actual initial-machine phase counts. The
separate execution theorem must connect these counts to the concrete program. -/

namespace MaxCutGames.Foundations.PCP.RawInitialMachineBudget

open Target Complexity

theorem fullBudget_le (F : Formula) :
    fullBudget F ≤ timePolynomial.eval (formulaBits F).length := by
  have hinput := input_header_bound F
  have hloop := loopTime_le 0 F.clauses
  have hout := GraphTableComplexity.bits_le_of_size_le (RawInitialTables.table F)
    (graph_size_bound F)
  rw [GraphTableComplexity.encodingPolynomial_eval] at hout
  simp only [Nat.zero_add] at hloop
  have hm : F.clauses.length ≤ (formulaBits F).length := by omega
  have hcoefficient : 18 * F.«variables» + 18 * F.clauses.length + 81 ≤
      18 * (formulaBits F).length + 81 := by omega
  have hproduct := Nat.mul_le_mul hm hcoefficient
  rw [timePolynomial_eval]
  unfold fullBudget
  nlinarith

end MaxCutGames.Foundations.PCP.RawInitialMachineBudget

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_RawInitialPredicate
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit finite predicates and numeric row words of the initial incidence table.
Every relation retains all 4096 entries, including repetitions. -/

/-! Exact ordered rows of the initial incidence table. Every relation retains
all 4096 entries, including repetitions; this is a list identity, not a runtime bound. -/

namespace MaxCutGames.Foundations.PCP.RawInitialRows

open Target GraphTables RawInitialTables

def clauseDarts (F : Formula) (i : Fin F.clauses.length) : List (InitialGraph.Dart F) :=
  [.inl ((i, .first), false), .inl ((i, .first), true),
   .inl ((i, .second), false), .inl ((i, .second), true),
   .inl ((i, .third), false), .inl ((i, .third), true)]

theorem orderedList_dartOrder (F : Formula) :
    orderedList (dartOrder F) =
      (List.finRange F.clauses.length).flatMap (clauseDarts F) ++ [.inr ()] := by
  rw [dartOrder, orderedList_cast, orderedList_sum, orderedList_prod]
  rw [eventOrder, orderedList_prod]
  have hs : orderedList slotOrder = [.first, .second, .third] := rfl
  have hb : orderedList finTwoEquiv.symm = [false, true] := rfl
  have hu : orderedList unitOrder = [()] := rfl
  rw [hs, hb, hu]
  simp [orderedList, List.finRange, List.flatMap_assoc, List.map_flatMap,
    ]
  rfl

def rowFor (F : Formula) (d : InitialGraph.Dart F) :
    DartRow (F.«variables» + F.clauses.length + 1) (6 * F.clauses.length + 1) where
  tail := vertexOrder F (InitialGraph.tail F d)
  reverseIndex := dartOrder F (InitialGraph.reverse F d)
  relation := relationOf (fun a b => InitialGraph.predicate F d (decodedLabel a) (decodedLabel b))

theorem rowList_table (F : Formula) :
    rowList (table F) = (orderedList (dartOrder F)).map (rowFor F) := by
  simp only [rowList, table, ofEnumeratedGraph, ofGraph, graphRows, Vector.toList_ofFn,
    orderedList, List.map_ofFn]
  rfl

theorem rowWords_incidence (F : Formula) (i : Fin F.clauses.length)
    (slot : Slot) (orientation : Bool) :
    rowWords (rowFor F (.inl ((i, slot), orientation))) =
      incidenceWords F.«variables» i.val (clauseNames (clauseAt F i))
        (clauseSigns (clauseAt F i)) slot orientation := by
  have ht : (rowFor F (.inl ((i, slot), orientation))).tail.val =
      if orientation then nameWord (clauseNames (clauseAt F i)) slot else F.«variables» + i.val := by
    cases orientation <;> cases slot <;> rfl
  have hr : (rowFor F (.inl ((i, slot), orientation))).reverseIndex.val =
      6 * i.val + 2 * (slotOrder slot).val + (if orientation then 0 else 1) := by
    cases orientation <;> cases slot <;>
      simp [rowFor, InitialGraph.reverse, dartOrder, eventOrder, slotOrder, unitOrder,
        finProdFinEquiv, finSumFinEquiv, finTwoEquiv, Nat.mul_add,
        Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm]
  have hp : (rowFor F (.inl ((i, slot), orientation))).relation =
      relationOf (relationPredicate (clauseSigns (clauseAt F i)) slot orientation) := by
    cases orientation <;> rfl
  unfold rowWords incidenceWords relationWordsFor
  rw [ht, hr, hp]

theorem rowWords_dummy (F : Formula) :
    rowWords (rowFor F (.inr ())) = dummyWords F.«variables» F.clauses.length := by
  have ht : (rowFor F (.inr ())).tail.val = F.«variables» + F.clauses.length := rfl
  have hr : (rowFor F (.inr ())).reverseIndex.val = 6 * F.clauses.length := by
    simp [rowFor, InitialGraph.reverse, dartOrder, unitOrder, finSumFinEquiv]
  have hp : (rowFor F (.inr ())).relation = relationOf (fun _ _ => true) := rfl
  have hw : relationWords (relationOf (fun _ _ => true)) = List.replicate 4096 1 := by
    unfold relationWords
    rw [relationOf, Vector.toList_ofFn, List.map_ofFn]
    exact List.ofFn_const 4096 1
  unfold rowWords dummyWords
  rw [ht, hr, hp, hw]

theorem clauseDarts_rowWords (F : Formula) (i : Fin F.clauses.length) :
    (clauseDarts F i).flatMap (fun d => rowWords (rowFor F d)) =
      clauseWords F.«variables» i.val (clauseNames (clauseAt F i))
        (clauseSigns (clauseAt F i)) := by
  simp [clauseDarts, rowWords_incidence, clauseWords, List.append_assoc]

/-- Exact headers and exact clause/slot/orientation order of every emitted word. -/
theorem tableWords_eq (F : Formula) :
    tableWords (table F) =
      [F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
      (List.finRange F.clauses.length).flatMap (fun i =>
        clauseWords F.«variables» i.val (clauseNames (clauseAt F i))
          (clauseSigns (clauseAt F i))) ++ dummyWords F.«variables» F.clauses.length := by
  rw [tableWords, rowList_table, orderedList_dartOrder]
  simp [List.flatMap_map, List.flatMap_append, List.flatMap_assoc, clauseDarts_rowWords,
    rowWords_dummy]

end MaxCutGames.Foundations.PCP.RawInitialRows

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RawInitialMachineModel
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MaxCutGames.Foundations.PCP.RawInitialMachineModel

open Turing Complexity Hastad

def relationOutput (slot : Fin 3) (orientation : Bool) (state : State) : List Bool :=
  (encodeWords (RawInitialRows.relationWordsFor state.1
    (RawInitialTables.slotOrder.symm slot) orientation)).reverse

def program : Label → TM2.Stmt Alphabet Label State
  | .headerStart slot => SourceMachine.fieldStart (headerTape slot) (.headerLoop slot)
  | .headerLoop slot => SourceMachine.fieldLoop .input (headerTape slot) (.headerLoop slot)
      (if slot.val = 0 then some (.headerStart 1) else some .scanN)
  | .scanN => MachineInitialHeaders.prefixScan .«variables» .scratch .reversed 1 .scanN .restoreN
  | .restoreN => Reduction.MachineTransfer.loopAt .scratch .«variables» id false .restoreN (some .scanM1)
  | .scanM1 => MachineInitialHeaders.prefixScan .counter .scratch .reversed 1 .scanM1 .restoreM1
  | .restoreM1 => Reduction.MachineTransfer.loopAt .scratch .counter id false .restoreM1 (some .closeFirst)
  | .closeFirst => Reduction.MachineSubstitution.pushWord .reversed [true, false]
      (.goto fun _ => .scanM6)
  | .scanM6 => MachineInitialHeaders.prefixScan .counter .scratch .reversed 6 .scanM6 .restoreM6
  | .restoreM6 => Reduction.MachineTransfer.loopAt .scratch .counter id false .restoreM6 (some .closeSecond)
  | .closeSecond => Reduction.MachineSubstitution.pushWord .reversed [true, false]
      (.goto fun _ => .initializeIndex)
  | .initializeIndex => .push .index (fun _ => false) (.goto fun _ => .guard)
  | .guard => MachineUnaryCounter.guard .counter (.fieldStart 0) (.scan .dummyVariables)
  | .fieldStart slot => SourceMachine.fieldStart (.field slot) (.fieldLoop slot)
  | .fieldLoop slot => SourceMachine.fieldLoop .input (.field slot) (.fieldLoop slot)
      (if h : slot.val + 1 < 6 then some (.fieldStart ⟨slot.val + 1, h⟩)
        else some .loadSigns)
  | .loadSigns =>
      .peek (.field 1) (fun state head => ((head.getD false, state.1.2), state.2))
        (.peek (.field 3) (fun state head => ((state.1.1, head.getD false, state.1.2.2), state.2))
          (.peek (.field 5) (fun state head => ((state.1.1, state.1.2.1, head.getD false), state.2))
            (.load (fun state => (state.1, none)) (.goto fun _ => .scan (.tailVariables 0)))))
  | .scan phase => MachineInitialHeaders.prefixScan (copySource phase) .scratch .reversed
      (copyScale phase) (.scan phase) (.restore phase)
  | .restore phase => Reduction.MachineTransfer.loopAt .scratch (copySource phase) id false
      (.restore phase) (some (copyNext phase))
  | .closeTail slot orientation => .push .reversed (fun _ => false)
      (.goto fun _ => .scan (.reverseIndex slot orientation))
  | .closeReverse slot orientation => Reduction.MachineSubstitution.pushWord .reversed
      (encodeWord (2 * slot.val + if orientation then 0 else 1))
        (.goto fun _ => .relation slot orientation)
  | .relation slot orientation => MachineFiniteTable.emit .reversed
      (relationOutput slot orientation)
      stateKeys (.goto fun _ => relationNext slot orientation)
  | .cleanupField slot => drain (.field slot) (.cleanupField slot)
      (if h : slot.val + 1 < 6 then .cleanupField ⟨slot.val + 1, h⟩ else .incrementIndex)
  | .incrementIndex => .push .index (fun _ => true) (.goto fun _ => .guard)
  | .closeDummyTail => .push .reversed (fun _ => false) (.goto fun _ => .scan .dummyReverse)
  | .closeDummyReverse => .push .reversed (fun _ => false) (.goto fun _ => .dummyRelation)
  | .dummyRelation => Reduction.MachineSubstitution.pushWord .reversed
      (encodeWords (GraphTables.relationWords (GraphTables.relationOf (fun _ _ => true))))
        (.goto fun _ => .cleanupFinal 0)
  | .cleanupFinal slot => drain (finalTape slot) (.cleanupFinal slot)
      (if h : slot.val + 1 < 3 then .cleanupFinal ⟨slot.val + 1, h⟩ else .reset)
  | .reset => .load (fun _ => initialState) (.goto fun _ => .finalReverse)
  | .finalReverse => Reduction.MachineTransfer.loopAt .reversed .output id false .finalReverse none

def machine : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .headerStart 0
  σ := State
  initialState := initialState
  m := program

end MaxCutGames.Foundations.PCP.RawInitialMachineModel

/-!
Actual execution of the raw initial graph machine from its standard input
configuration to the first clause-loop guard. The unread clause bits are
preserved verbatim, and all tape contents at the boundary are explicit.
-/

namespace MaxCutGames.Foundations.PCP.RawInitialMachineStart

open Turing Complexity Hastad RawInitialMachineModel

theorem initList_eq (bits : List Bool) :
    initList machine bits =
      ⟨some (.headerStart 0), initialState, inputTapes bits⟩ := by
  unfold initList
  congr 1
  funext k
  change Tape at k
  cases k <;> rfl

/-- The two actual header-field readers reach the prepared counter boundary. -/
theorem readCountersTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[n + m + 4]
      (some (initList machine (encodeWords [n, m] ++ clauseBits))) =
      some ⟨some .scanN, initialState, counterTapes n m clauseBits⟩ := by
  let t0 := inputTapes (encodeWords [n, m] ++ clauseBits)
  have first := (SourceMachine.fieldInTime .input .«variables» (by decide)
    (.headerStart 0) (.headerLoop 0) (some (.headerStart 1)) program rfl rfl
    t0 n (encodeWord m ++ clauseBits)
    (by simp [t0, inputTapes, encodeWords, List.append_assoc])
    (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[n + 2]
    (some ⟨some (.headerStart 0), initialState, t0⟩) = _ at first
  have firstFrame : SourceMachine.fieldTapes .input .«variables» t0
      (encodeWord m ++ clauseBits) (encodeWord n ++ t0 .«variables») =
      firstTapes_inline_RawInitialMachineStart n m clauseBits := by
    funext k
    cases k <;> simp [SourceMachine.fieldTapes, t0, inputTapes, firstTapes_inline_RawInitialMachineStart]
  rw [firstFrame] at first
  have second := (SourceMachine.fieldInTime .input .counter (by decide)
    (.headerStart 1) (.headerLoop 1) (some .scanN) program rfl rfl
    (firstTapes_inline_RawInitialMachineStart n m clauseBits) m clauseBits rfl (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[m + 2]
    (some ⟨some (.headerStart 1), initialState, firstTapes_inline_RawInitialMachineStart n m clauseBits⟩) = _ at second
  have secondFrame : SourceMachine.fieldTapes .input .counter (firstTapes_inline_RawInitialMachineStart n m clauseBits)
      clauseBits (encodeWord m ++ firstTapes_inline_RawInitialMachineStart n m clauseBits .counter) =
      counterTapes n m clauseBits := by
    funext k
    cases k <;> simp [SourceMachine.fieldTapes, firstTapes_inline_RawInitialMachineStart, counterTapes]
  rw [secondFrame] at second
  have total := trace_trans_inline_RawInitialMachineStart _ first second
  rw [show (n + 2) + (m + 2) = n + m + 4 by omega] at total
  simpa only [initList_eq, t0, initialState] using! total

/-- Instantiation of the checked arithmetic phase in the actual global program. -/
theorem headersTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 4 * m + 8]
      (some ⟨some .scanN, initialState, counterTapes n m clauseBits⟩) =
      some ⟨some .initializeIndex, initialState, headerTapes_inline_RawInitialMachineStart n m clauseBits⟩ := by
  have h := MachineInitialHeaders.headerTrace .«variables» .counter .scratch .reversed
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    .scanN .restoreN .scanM1 .restoreM1 .closeFirst .scanM6 .restoreM6 .closeSecond
    (some .initializeIndex) program rfl rfl rfl rfl rfl rfl rfl rfl
    (counterTapes n m clauseBits) n m [] []
    (by simp [counterTapes]) (by simp [counterTapes]) rfl
    (false, false, false) none
  have frame : Function.update (counterTapes n m clauseBits) .reversed
      ((encodeWords [n + m + 1, 6 * m + 1]).reverse ++
        counterTapes n m clauseBits .reversed) = headerTapes_inline_RawInitialMachineStart n m clauseBits := by
    funext k
    cases k <;> simp [counterTapes, headerTapes_inline_RawInitialMachineStart]
  rw [frame] at h
  exact h

theorem initializeIndexTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .initializeIndex, initialState, headerTapes_inline_RawInitialMachineStart n m clauseBits⟩) =
      some ⟨some .guard, initialState, startTapes n m clauseBits⟩ := by
  simp only [Function.iterate_one, MachineComposition.advance_some]
  change some (TM2.stepAux (program .initializeIndex) initialState
    (headerTapes_inline_RawInitialMachineStart n m clauseBits)) = _
  simp only [program, TM2.stepAux]
  congr 2
  funext k
  cases k <;> simp [headerTapes_inline_RawInitialMachineStart, startTapes]

/-- Exact startup trace for arbitrary encoded clause-tail data. -/
theorem startTrace (n m : ℕ) (clauseBits : List Bool) :
    (MachineComposition.advance (TM2.step program))^[3 * n + 5 * m + 13]
      (some (initList machine (encodeWords [n, m] ++ clauseBits))) =
      some ⟨some .guard, initialState, startTapes n m clauseBits⟩ := by
  have total := trace_trans_inline_RawInitialMachineStart _
    (trace_trans_inline_RawInitialMachineStart _ (readCountersTrace n m clauseBits) (headersTrace n m clauseBits))
    (initializeIndexTrace n m clauseBits)
  simpa only [show (n + m + 4) + (2 * n + 4 * m + 8) + 1 =
    3 * n + 5 * m + 13 by omega] using total

/-- Startup from the actual serialized CNF, with its untouched clause tail. -/
theorem formulaStartTrace (F : Target.Formula) :
    (MachineComposition.advance (TM2.step program))^[
        3 * F.«variables» + 5 * F.clauses.length + 13]
      (some (initList machine (formulaBits F))) =
      some ⟨some .guard, initialState,
        startTapes F.«variables» F.clauses.length
          (encodeWords (F.clauses.flatMap clauseWords))⟩ := by
  simpa only [formulaBits, formulaWords, encodeWords_append] using
    startTrace F.«variables» F.clauses.length (encodeWords (F.clauses.flatMap clauseWords))

end MaxCutGames.Foundations.PCP.RawInitialMachineStart

/-! The exact input and output streams at successive clause-loop iterations.
These tape invariants use the actual word codecs and clause occurrence order. -/

namespace MaxCutGames.Foundations.PCP.RawInitialMachineLoopData

open Target Complexity RawInitialMachineModel

theorem mapIdx_ofFn_inline_RawInitialMachineLoopData {α β : Type} (xs : List α) (f : Nat → α → β) :
    xs.mapIdx f = List.ofFn (fun i : Fin xs.length => f i.val (xs.get i)) := by
  induction xs generalizing f with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem clauseOutput_numbered (F : Formula) :
    clauseOutput F.«variables» 0 F.clauses =
      (List.finRange F.clauses.length).flatMap (fun i =>
        RawInitialRows.clauseWords F.«variables» i.val
          (RawInitialRows.clauseNames (clauseAt F i))
          (RawInitialRows.clauseSigns (clauseAt F i))) := by
  simp only [clauseOutput, mapIdx_ofFn_inline_RawInitialMachineLoopData, List.ofFn_eq_map,
    Nat.zero_add, clauseAt]
  rfl

theorem tableWords_decomposition (F : Formula) :
    GraphTables.tableWords (RawInitialTables.table F) =
      [F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
        clauseOutput F.«variables» 0 F.clauses ++
          RawInitialRows.dummyWords F.«variables» F.clauses.length := by
  rw [RawInitialRows.tableWords_eq, clauseOutput_numbered]

theorem startTapes_eq (n m : Nat) (input : List Bool) :
    RawInitialMachineStart.startTapes n m input =
      loopTapes n 0 m input (encodeWords [n + m + 1, 6 * m + 1]).reverse := by
  funext tape
  cases tape <;> rfl

end MaxCutGames.Foundations.PCP.RawInitialMachineLoopData

/-! Actual execution of the raw initial graph program's reusable phases. -/

namespace MaxCutGames.Foundations.PCP.RawInitialMachinePhases

open Turing Complexity RawInitialMachineModel

theorem copySource_ne_scratch (phase : CopyPhase) : copySource phase ≠ Tape.scratch := by
  cases phase <;> simp [copySource]

theorem copySource_ne_reversed (phase : CopyPhase) : copySource phase ≠ Tape.reversed := by
  cases phase <;> simp [copySource]

def copyInTime (phase : CopyPhase) (base : Tape → List Bool)
    (n : Nat) (suffix : List Bool)
    (hsource : base (copySource phase) = encodeWord n ++ suffix)
    (hscratch : base .scratch = []) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.scan phase), state, base⟩
      (some ⟨some (copyNext phase), (state.1, none),
        Function.update base .reversed
          (List.replicate (copyScale phase * n) true ++ base .reversed)⟩)
      (2 * n + 2) :=
  MachineInitialHeaders.prefixInTime (copySource phase) Tape.scratch Tape.reversed
    (copySource_ne_scratch phase) (copySource_ne_reversed phase) (by decide)
    (copyScale phase) (.scan phase) (.restore phase) (some (copyNext phase))
    program rfl rfl base n suffix hsource hscratch state.1 state.2

def relationInTime (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.relation slot orientation), state, base⟩
      (some ⟨some (relationNext slot orientation), state,
        Function.update base .reversed
          (relationOutput slot orientation state ++ base .reversed)⟩) 1 :=
  MachineFiniteTable.emitInTime (K := Tape) (Λ := Label) (σ := State) (Γ := Alphabet)
    Tape.reversed
    (relationOutput slot orientation)
    stateKeys stateKeys_complete program (.relation slot orientation)
    (relationNext slot orientation) rfl state base

theorem loadSigns_step (base : Tape → List Bool) (a b c : Bool)
    (ha : base (.field 1) = encodeWord (if a then 1 else 0))
    (hb : base (.field 3) = encodeWord (if b then 1 else 0))
    (hc : base (.field 5) = encodeWord (if c then 1 else 0)) (state : State) :
    (TM2.step program) ⟨some .loadSigns, state, base⟩ =
      some ⟨some (.scan (.tailVariables 0)), ((a, b, c), none), base⟩ := by
  change some (TM2.stepAux (program .loadSigns) state base) = _
  simp only [program, TM2.stepAux, ha, hb, hc, bitWord_head_inline_RawInitialMachinePhases, Option.getD_some]

def cleanupFieldInTime (slot : Fin 6) (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.cleanupField slot), state, base⟩
      (some ⟨some (if h : slot.val + 1 < 6 then .cleanupField ⟨slot.val + 1, h⟩
        else .incrementIndex), (state.1, none), Function.update base (.field slot) []⟩)
      ((base (.field slot)).length + 1) :=
  MachineDrain.drainInTime (.field slot) (.cleanupField slot) _ program rfl base state.1 state.2

def cleanupFinalInTime (slot : Fin 3) (base : Tape → List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.cleanupFinal slot), state, base⟩
      (some ⟨some (if h : slot.val + 1 < 3 then .cleanupFinal ⟨slot.val + 1, h⟩
        else .reset), (state.1, none), Function.update base (finalTape slot) []⟩)
      ((base (finalTape slot)).length + 1) :=
  MachineDrain.drainInTime (finalTape slot) (.cleanupFinal slot) _ program rfl base state.1 state.2

end MaxCutGames.Foundations.PCP.RawInitialMachinePhases

/-!
Read exactly one concrete six-field CNF clause in the actual global machine,
then execute its real sign-loading instruction. No extra finish transition
is inserted. Every unrelated tape and the unread input suffix are preserved.
-/

namespace MaxCutGames.Foundations.PCP.RawInitialMachineReadClause

open Turing Complexity Hastad RawInitialMachineModel

/-- Six actual field routines, stopping directly at the global sign loader. -/
theorem fieldsTrace {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool)
    (hinput : base .input = encodeWords (Complexity.clauseWords c) ++ suffix)
    (hempty : ∀ j, base (.field j) = []) (state : State) :
    (MachineComposition.advance (TM2.step program))^[
        (encodeWords (Complexity.clauseWords c)).length + 6]
      (some ⟨some (.fieldStart 0), state, base⟩) =
      some ⟨some .loadSigns, (state.1, none), recordTapes base c suffix⟩ := by
  let a := fieldValue c 0
  let b := fieldValue c 1
  let d := fieldValue c 2
  let e := fieldValue c 3
  let f := fieldValue c 4
  let g := fieldValue c 5
  have hwords : Complexity.clauseWords c = [a, b, d, e, f, g] := rfl
  have hin : base .input = encodeWord a ++ (encodeWords [b, d, e, f, g] ++ suffix) := by
    rw [hinput, hwords]
    simp only [encodeWords, List.append_assoc]
  let t1 := SourceMachine.afterField .input (.field 0) base a
    (encodeWords [b, d, e, f, g] ++ suffix)
  let t2 := SourceMachine.afterField .input (.field 1) t1 b
    (encodeWords [d, e, f, g] ++ suffix)
  let t3 := SourceMachine.afterField .input (.field 2) t2 d
    (encodeWords [e, f, g] ++ suffix)
  let t4 := SourceMachine.afterField .input (.field 3) t3 e
    (encodeWords [f, g] ++ suffix)
  let t5 := SourceMachine.afterField .input (.field 4) t4 f
    (encodeWords [g] ++ suffix)
  let t6 := SourceMachine.afterField .input (.field 5) t5 g suffix
  have h1 := (SourceMachine.fieldInTime .input (.field 0) (by decide)
    (.fieldStart 0) (.fieldLoop 0) (some (.fieldStart 1)) program rfl rfl
    base a (encodeWords [b, d, e, f, g] ++ suffix) hin state.1 state.2).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[a + 2]
    (some ⟨some (.fieldStart 0), state, base⟩) =
    some ⟨some (.fieldStart 1), (state.1, none), t1⟩ at h1
  have h2 := (SourceMachine.fieldInTime .input (.field 1) (by decide)
    (.fieldStart 1) (.fieldLoop 1) (some (.fieldStart 2)) program rfl rfl
    t1 b (encodeWords [d, e, f, g] ++ suffix)
    (by simp [t1, SourceMachine.afterField, encodeWords, List.append_assoc])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[b + 2]
    (some ⟨some (.fieldStart 1), (state.1, none), t1⟩) =
    some ⟨some (.fieldStart 2), (state.1, none), t2⟩ at h2
  have h3 := (SourceMachine.fieldInTime .input (.field 2) (by decide)
    (.fieldStart 2) (.fieldLoop 2) (some (.fieldStart 3)) program rfl rfl
    t2 d (encodeWords [e, f, g] ++ suffix)
    (by simp [t2, SourceMachine.afterField, encodeWords, List.append_assoc])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[d + 2]
    (some ⟨some (.fieldStart 2), (state.1, none), t2⟩) =
    some ⟨some (.fieldStart 3), (state.1, none), t3⟩ at h3
  have h4 := (SourceMachine.fieldInTime .input (.field 3) (by decide)
    (.fieldStart 3) (.fieldLoop 3) (some (.fieldStart 4)) program rfl rfl
    t3 e (encodeWords [f, g] ++ suffix)
    (by simp [t3, SourceMachine.afterField, encodeWords, List.append_assoc])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[e + 2]
    (some ⟨some (.fieldStart 3), (state.1, none), t3⟩) =
    some ⟨some (.fieldStart 4), (state.1, none), t4⟩ at h4
  have h5 := (SourceMachine.fieldInTime .input (.field 4) (by decide)
    (.fieldStart 4) (.fieldLoop 4) (some (.fieldStart 5)) program rfl rfl
    t4 f (encodeWords [g] ++ suffix)
    (by simp [t4, SourceMachine.afterField, encodeWords, List.append_assoc])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[f + 2]
    (some ⟨some (.fieldStart 4), (state.1, none), t4⟩) =
    some ⟨some (.fieldStart 5), (state.1, none), t5⟩ at h5
  have h6 := (SourceMachine.fieldInTime .input (.field 5) (by decide)
    (.fieldStart 5) (.fieldLoop 5) (some .loadSigns) program rfl rfl
    t5 g suffix
    (by simp [t5, SourceMachine.afterField, encodeWords])
    state.1 none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[g + 2]
    (some ⟨some (.fieldStart 5), (state.1, none), t5⟩) =
    some ⟨some .loadSigns, (state.1, none), t6⟩ at h6
  have total := trace_trans_inline_RawInitialMachineReadClause _ (trace_trans_inline_RawInitialMachineReadClause _ (trace_trans_inline_RawInitialMachineReadClause _
    (trace_trans_inline_RawInitialMachineReadClause _ (trace_trans_inline_RawInitialMachineReadClause _ h1 h2) h3) h4) h5) h6
  have htime : (((((a + 2) + (b + 2)) + (d + 2)) + (e + 2)) + (f + 2)) + (g + 2) =
      (encodeWords (Complexity.clauseWords c)).length + 6 := by
    rw [hwords, encodeWords_length]
    simp
    omega
  rw [htime] at total
  have frame : t6 = recordTapes base c suffix := by
    funext k
    cases k with
    | field j =>
      fin_cases j <;>
        simp [t6, t5, t4, t3, t2, t1, SourceMachine.afterField, SourceMachine.fieldTapes,
          recordTapes, hempty, a, b, d, e, f, g]
    | _ =>
      simp [t6, t5, t4, t3, t2, t1, SourceMachine.afterField, SourceMachine.fieldTapes,
        recordTapes]
  rw [frame] at total
  exact total

theorem readClauseTrace {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool)
    (hinput : base .input = encodeWords (Complexity.clauseWords c) ++ suffix)
    (hempty : ∀ j, base (.field j) = []) (state : State) :
    (MachineComposition.advance (TM2.step program))^[
        (encodeWords (Complexity.clauseWords c)).length + 7]
      (some ⟨some (.fieldStart 0), state, base⟩) =
      some ⟨some (.scan (.tailVariables 0)), (RawInitialRows.clauseSigns c, none),
        recordTapes base c suffix⟩ := by
  have first := fieldsTrace base c suffix hinput hempty state
  have last := RawInitialMachinePhases.loadSigns_step (recordTapes base c suffix)
    (c)[0].positive (c)[1].positive (c)[2].positive rfl rfl rfl (state.1, none)
  have lastTrace : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .loadSigns, (state.1, none), recordTapes base c suffix⟩) =
      some ⟨some (.scan (.tailVariables 0)), (RawInitialRows.clauseSigns c, none),
        recordTapes base c suffix⟩ := last
  have total := trace_trans_inline_RawInitialMachineReadClause _ first lastTrace
  simpa only [show (encodeWords (Complexity.clauseWords c)).length + 6 + 1 =
    (encodeWords (Complexity.clauseWords c)).length + 7 by omega] using total

end MaxCutGames.Foundations.PCP.RawInitialMachineReadClause

/-! The six incidence rows are emitted by the actual finite program, with
their exact order, full relation lists, transition count, and tape frame. -/

namespace MaxCutGames.Foundations.PCP.RawInitialMachineRows

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases

attribute [local irreducible] relationOutput RawInitialRows.relationWordsFor

abbrev advance_inline_RawInitialMachineRows := MachineComposition.advance (TM2.step program)

def outputTapes (base : Tape → List Bool) (bits : List Bool) : Tape → List Bool :=
  Function.update base .reversed (bits ++ base .reversed)

@[simp] theorem outputTapes_reversed (base : Tape → List Bool) (bits : List Bool) :
    outputTapes base bits .reversed = bits ++ base .reversed := by simp [outputTapes]

@[simp] theorem outputTapes_twice (base : Tape → List Bool) (first second : List Bool) :
    outputTapes (outputTapes base first) second = outputTapes base (second ++ first) := by
  funext tape
  by_cases h : tape = .reversed
  · subst tape; simp [List.append_assoc]
  · simp [outputTapes, h]

theorem copyTrace_inline_RawInitialMachineRows (phase : CopyPhase) (base : Tape → List Bool)
    (n : ℕ) (hsource : base (copySource phase) = encodeWord n)
    (hscratch : base .scratch = []) (signs : Signs) :
    advance_inline_RawInitialMachineRows^[2 * n + 2] (some ⟨some (.scan phase), (signs, none), base⟩) =
      some ⟨some (copyNext phase), (signs, none),
        outputTapes base (List.replicate (copyScale phase * n) true)⟩ :=
  (copyInTime phase base n [] (by simpa using hsource) hscratch (signs, none)).evals_in_steps

theorem closeTailTrace_inline_RawInitialMachineRows (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (signs : Signs) :
    advance_inline_RawInitialMachineRows^[1] (some ⟨some (.closeTail slot orientation), (signs, none), base⟩) =
      some ⟨some (.scan (.reverseIndex slot orientation)), (signs, none),
        outputTapes base [false]⟩ := by
  change some (TM2.stepAux (program (.closeTail slot orientation)) (signs, none) base) = _
  rfl

theorem closeReverseTrace_inline_RawInitialMachineRows (slot : Fin 3) (orientation : Bool)
    (base : Tape → List Bool) (signs : Signs) :
    advance_inline_RawInitialMachineRows^[1] (some ⟨some (.closeReverse slot orientation), (signs, none), base⟩) =
      some ⟨some (.relation slot orientation), (signs, none),
        outputTapes base (encodeWord (2 * slot.val + if orientation then 0 else 1)).reverse⟩ :=
  MachineInitialHeaders.literalTrace .reversed
    (encodeWord (2 * slot.val + if orientation then 0 else 1))
    (.closeReverse slot orientation) (some (.relation slot orientation))
    program rfl base signs none

theorem reverse_encodeWord_add_inline_RawInitialMachineRows (a b : ℕ) :
    (encodeWord b).reverse ++ List.replicate a true = (encodeWord (a + b)).reverse := by
  simp only [encodeWord, List.reverse_append, List.reverse_replicate, List.reverse_singleton]
  rw [Nat.add_comm a b, List.replicate_add]
  simp only [List.append_assoc]

def rowEndBits (slot : Fin 3) (orientation : Bool) (i : ℕ) (signs : Signs) : List Bool :=
  relationOutput slot orientation (signs, none) ++
    (encodeWord (6 * i + 2 * slot.val + if orientation then 0 else 1)).reverse ++ [false]

theorem rowEndTrace_inline_RawInitialMachineRows (slot : Fin 3) (orientation : Bool) (base : Tape → List Bool)
    (i : ℕ) (hindex : base .index = encodeWord i) (hscratch : base .scratch = [])
    (signs : Signs) :
    advance_inline_RawInitialMachineRows^[2 * i + 5] (some ⟨some (.closeTail slot orientation), (signs, none), base⟩) =
      some ⟨some (relationNext slot orientation), (signs, none),
        outputTapes base (rowEndBits slot orientation i signs)⟩ := by
  let first := outputTapes base [false]
  let second := outputTapes first (List.replicate (6 * i) true)
  let third := outputTapes second
    (encodeWord (2 * slot.val + if orientation then 0 else 1)).reverse
  have h1 := closeTailTrace_inline_RawInitialMachineRows slot orientation base signs
  have h2 := copyTrace_inline_RawInitialMachineRows (.reverseIndex slot orientation) first i
    (by simpa [first, outputTapes, copySource] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  change advance_inline_RawInitialMachineRows^[2 * i + 2]
    (some ⟨some (.scan (.reverseIndex slot orientation)), (signs, none), first⟩) =
    some ⟨some (.closeReverse slot orientation), (signs, none), second⟩ at h2
  have h3 := closeReverseTrace_inline_RawInitialMachineRows slot orientation second signs
  have h4 := (relationInTime slot orientation third (signs, none)).evals_in_steps
  change advance_inline_RawInitialMachineRows^[1] (some ⟨some (.relation slot orientation), (signs, none), third⟩) =
    some ⟨some (relationNext slot orientation), (signs, none),
      outputTapes third (relationOutput slot orientation (signs, none))⟩ at h4
  have total := trace_trans_inline_RawInitialMachineRows _ (trace_trans_inline_RawInitialMachineRows _ (trace_trans_inline_RawInitialMachineRows _ h1 h2) h3) h4
  have hout : outputTapes third (relationOutput slot orientation (signs, none)) =
      outputTapes base (rowEndBits slot orientation i signs) := by
    simp only [third, second, first, outputTapes_twice]
    apply congrArg (outputTapes base)
    rw [reverse_encodeWord_add_inline_RawInitialMachineRows]
    simp only [rowEndBits, Nat.add_assoc, List.append_assoc]
  rw [hout] at total
  simpa only [show 1 + (2 * i + 2) + 1 + 1 = 2 * i + 5 by omega] using total

theorem rowEndBits_append_inline_RawInitialMachineRows (slot : Fin 3) (orientation : Bool)
    (tail i : ℕ) (signs : Signs) :
    rowEndBits slot orientation i signs ++ List.replicate tail true =
      (encodeWords ([tail, 6 * i + 2 * slot.val + if orientation then 0 else 1] ++
        RawInitialRows.relationWordsFor signs (RawInitialTables.slotOrder.symm slot) orientation)).reverse := by
  simp only [rowEndBits, relationOutput, encodeWords_append, encodeWords,
    List.append_nil, List.reverse_append, encodeWord,
    List.reverse_replicate, List.reverse_singleton, List.append_assoc]

theorem falseRowTrace (slot : Fin 3) (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .«variables» = encodeWord n) (hindex : base .index = encodeWord i)
    (hscratch : base .scratch = []) :
    advance_inline_RawInitialMachineRows^[2 * n + 4 * i + 9]
      (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
      some ⟨some (.scan (.variableName slot)), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
          (RawInitialTables.slotOrder.symm slot) false)).reverse⟩ := by
  let first := outputTapes base (List.replicate n true)
  let second := outputTapes first (List.replicate i true)
  have h1 := copyTrace_inline_RawInitialMachineRows (.tailVariables slot) base n hvariables hscratch signs
  have h2 := copyTrace_inline_RawInitialMachineRows (.tailIndex slot) first i
    (by simpa [first, outputTapes, copySource] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  simp only [copyScale, Nat.one_mul, copyNext] at h1 h2
  change advance_inline_RawInitialMachineRows^[2 * n + 2]
    (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
    some ⟨some (.scan (.tailIndex slot)), (signs, none), first⟩ at h1
  change advance_inline_RawInitialMachineRows^[2 * i + 2]
    (some ⟨some (.scan (.tailIndex slot)), (signs, none), first⟩) =
    some ⟨some (.closeTail slot false), (signs, none), second⟩ at h2
  have h3 := rowEndTrace_inline_RawInitialMachineRows slot false second i
    (by simpa [second, first, outputTapes] using hindex)
    (by simpa [second, first, outputTapes] using hscratch) signs
  have total := trace_trans_inline_RawInitialMachineRows _ (trace_trans_inline_RawInitialMachineRows _ h1 h2) h3
  have hout : outputTapes second (rowEndBits slot false i signs) =
      outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
        (RawInitialTables.slotOrder.symm slot) false)).reverse := by
    simp only [second, first, outputTapes_twice]
    apply congrArg (outputTapes base)
    rw [← List.replicate_add, Nat.add_comm i n, rowEndBits_append_inline_RawInitialMachineRows]
    simp only [RawInitialRows.incidenceWords, Bool.false_eq_true, ↓reduceIte,
      Equiv.apply_symm_apply]
  rw [hout] at total
  simpa only [relationNext, Bool.false_eq_true, ↓reduceIte,
    show (2 * n + 2) + (2 * i + 2) + (2 * i + 5) = 2 * n + 4 * i + 9 by omega] using total

theorem trueRowTrace (slot : Fin 3) (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hname : base (.field (nameField slot)) =
      encodeWord (RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot)))
    (hindex : base .index = encodeWord i) (hscratch : base .scratch = []) :
    advance_inline_RawInitialMachineRows^[2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 2 * i + 7]
      (some ⟨some (.scan (.variableName slot)), (signs, none), base⟩) =
      some ⟨some (relationNext slot true), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
          (RawInitialTables.slotOrder.symm slot) true)).reverse⟩ := by
  let value := RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot)
  let first := outputTapes base (List.replicate value true)
  have h1 := copyTrace_inline_RawInitialMachineRows (.variableName slot) base value hname hscratch signs
  simp only [copyScale, Nat.one_mul, copyNext] at h1
  change advance_inline_RawInitialMachineRows^[2 * value + 2]
    (some ⟨some (.scan (.variableName slot)), (signs, none), base⟩) =
    some ⟨some (.closeTail slot true), (signs, none), first⟩ at h1
  have h2 := rowEndTrace_inline_RawInitialMachineRows slot true first i
    (by simpa [first, outputTapes] using hindex)
    (by simpa [first, outputTapes] using hscratch) signs
  have total := trace_trans_inline_RawInitialMachineRows _ h1 h2
  have hout : outputTapes first (rowEndBits slot true i signs) =
      outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
        (RawInitialTables.slotOrder.symm slot) true)).reverse := by
    simp only [first, outputTapes_twice, rowEndBits_append_inline_RawInitialMachineRows, value,
      RawInitialRows.incidenceWords, ↓reduceIte, Equiv.apply_symm_apply]
  rw [hout] at total
  simpa only [value, show (2 * value + 2) + (2 * i + 5) = 2 * value + 2 * i + 7 by omega] using total

def pairWords (slot : Fin 3) (n i : ℕ) (names : RawInitialRows.Names)
    (signs : Signs) : List ℕ :=
  RawInitialRows.incidenceWords n i names signs (RawInitialTables.slotOrder.symm slot) false ++
    RawInitialRows.incidenceWords n i names signs (RawInitialTables.slotOrder.symm slot) true

theorem pairTrace (slot : Fin 3) (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .«variables» = encodeWord n) (hindex : base .index = encodeWord i)
    (hname : base (.field (nameField slot)) =
      encodeWord (RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot)))
    (hscratch : base .scratch = []) :
    advance_inline_RawInitialMachineRows^[2 * n + 6 * i +
      2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 16]
      (some ⟨some (.scan (.tailVariables slot)), (signs, none), base⟩) =
      some ⟨some (relationNext slot true), (signs, none),
        outputTapes base (encodeWords (pairWords slot n i names signs)).reverse⟩ := by
  let first := outputTapes base (encodeWords (RawInitialRows.incidenceWords n i names signs
    (RawInitialTables.slotOrder.symm slot) false)).reverse
  have h1 := falseRowTrace slot base n i names signs hvariables hindex hscratch
  have h2 := trueRowTrace slot first n i names signs
    (by simpa [first, outputTapes] using hname)
    (by simpa [first, outputTapes] using hindex)
    (by simpa [first, outputTapes] using hscratch)
  have total := trace_trans_inline_RawInitialMachineRows _ h1 h2
  simpa only [first, outputTapes_twice, pairWords, encodeWords_append, List.reverse_append,
    show (2 * n + 4 * i + 9) +
      (2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 2 * i + 7) =
      2 * n + 6 * i +
        2 * RawInitialRows.nameWord names (RawInitialTables.slotOrder.symm slot) + 16 by omega]
    using total

/-- Exact execution of all six incidence rows. Relation tables stay symbolic;
no entry is discarded and every non-output tape is preserved. -/
theorem rowsTrace (base : Tape → List Bool) (n i : ℕ)
    (names : RawInitialRows.Names) (signs : Signs)
    (hvariables : base .«variables» = encodeWord n) (hindex : base .index = encodeWord i)
    (hname0 : base (.field 0) = encodeWord names.1)
    (hname2 : base (.field 2) = encodeWord names.2.1)
    (hname4 : base (.field 4) = encodeWord names.2.2)
    (hscratch : base .scratch = []) :
    advance_inline_RawInitialMachineRows^[6 * n + 18 * i + 2 * (names.1 + names.2.1 + names.2.2) + 48]
      (some ⟨some (.scan (.tailVariables 0)), (signs, none), base⟩) =
      some ⟨some (.cleanupField 0), (signs, none),
        outputTapes base (encodeWords (RawInitialRows.clauseWords n i names signs)).reverse⟩ := by
  let first := outputTapes base (encodeWords (pairWords 0 n i names signs)).reverse
  let second := outputTapes first (encodeWords (pairWords 1 n i names signs)).reverse
  have h0 := pairTrace 0 base n i names signs hvariables hindex hname0 hscratch
  have h1 := pairTrace 1 first n i names signs
    (by simpa [first, outputTapes] using hvariables)
    (by simpa [first, outputTapes] using hindex)
    (by simpa [first, outputTapes, nameField, RawInitialRows.nameWord,
      RawInitialTables.slotOrder] using hname2)
    (by simpa [first, outputTapes] using hscratch)
  have h2 := pairTrace 2 second n i names signs
    (by simpa [second, first, outputTapes] using hvariables)
    (by simpa [second, first, outputTapes] using hindex)
    (by simpa [second, first, outputTapes, nameField, RawInitialRows.nameWord,
      RawInitialTables.slotOrder] using hname4)
    (by simpa [second, first, outputTapes] using hscratch)
  change advance_inline_RawInitialMachineRows^[2 * n + 6 * i + 2 * names.1 + 16]
    (some ⟨some (.scan (.tailVariables 0)), (signs, none), base⟩) =
    some ⟨some (.scan (.tailVariables 1)), (signs, none), first⟩ at h0
  change advance_inline_RawInitialMachineRows^[2 * n + 6 * i + 2 * names.2.1 + 16]
    (some ⟨some (.scan (.tailVariables 1)), (signs, none), first⟩) =
    some ⟨some (.scan (.tailVariables 2)), (signs, none), second⟩ at h1
  change advance_inline_RawInitialMachineRows^[2 * n + 6 * i + 2 * names.2.2 + 16]
    (some ⟨some (.scan (.tailVariables 2)), (signs, none), second⟩) =
    some ⟨some (.cleanupField 0), (signs, none),
      outputTapes second (encodeWords (pairWords 2 n i names signs)).reverse⟩ at h2
  have total := trace_trans_inline_RawInitialMachineRows _ (trace_trans_inline_RawInitialMachineRows _ h0 h1) h2
  have hout : outputTapes second (encodeWords (pairWords 2 n i names signs)).reverse =
      outputTapes base (encodeWords (RawInitialRows.clauseWords n i names signs)).reverse := by
    simp only [second, first, outputTapes_twice, RawInitialRows.clauseWords,
      encodeWords_append, List.reverse_append, pairWords, List.append_assoc]
    rfl
  rw [hout] at total
  simpa only [show (2 * n + 6 * i + 2 * names.1 + 16) +
    (2 * n + 6 * i + 2 * names.2.1 + 16) + (2 * n + 6 * i + 2 * names.2.2 + 16) =
      6 * n + 18 * i + 2 * (names.1 + names.2.1 + names.2.2) + 48 by omega] using total

end MaxCutGames.Foundations.PCP.RawInitialMachineRows

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_Machines_RawInitialMachineCleanup
attribute [-instance] _root_.OAI.MaxCutGames.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.labelDecidableEq _root_.OAI.MaxCutGames.Reduction.MachineOutcomeRows.localLabelDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual cleanup of all six clause-field tapes followed by the global unary
index increment. The output accumulator, unread input, and other caller tapes
are preserved, and no additional finish instruction is assumed.
-/

namespace MaxCutGames.Foundations.PCP.RawInitialMachineCleanup

open Turing Complexity RawInitialMachineModel RawInitialMachineReadClause

/-- The index increment is exactly the one push in the actual global program. -/
theorem incrementIndexTrace (base : Tape → List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .incrementIndex, state, base⟩) =
      some ⟨some .guard, state, Function.update base .index (true :: base .index)⟩ := by
  rfl

/-- Clear six actual field tapes, increment the index, and return to the guard. -/
theorem cleanupTrace {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool) (i : ℕ)
    (hempty : ∀ j, base (.field j) = []) (hindex : base .index = encodeWord i)
    (incoming : State) :
    (MachineComposition.advance (TM2.step program))^[
        (encodeWords (Complexity.clauseWords c)).length + 7]
      (some ⟨some (.cleanupField 0), incoming, recordTapes base c suffix⟩) =
      some ⟨some .guard, (incoming.1, none),
        Function.update (Function.update base .input suffix) .index (encodeWord (i + 1))⟩ := by
  let r := recordTapes base c suffix
  let t1 := Function.update r (.field 0) []
  let t2 := Function.update t1 (.field 1) []
  let t3 := Function.update t2 (.field 2) []
  let t4 := Function.update t3 (.field 3) []
  let t5 := Function.update t4 (.field 4) []
  let t6 := Function.update t5 (.field 5) []
  have h1 := (RawInitialMachinePhases.cleanupFieldInTime 0 r incoming).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[
      (encodeWord (fieldValue c 0)).length + 1]
    (some ⟨some (.cleanupField 0), incoming, r⟩) =
    some ⟨some (.cleanupField 1), (incoming.1, none), t1⟩ at h1
  have h2 := (RawInitialMachinePhases.cleanupFieldInTime 1 t1 (incoming.1, none)).evals_in_steps
  have hf2 : t1 (.field 1) = encodeWord (fieldValue c 1) := by
    simp [t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t1 (.field 1)).length + 1]
    (some ⟨some (.cleanupField 1), (incoming.1, none), t1⟩) =
    some ⟨some (.cleanupField 2), (incoming.1, none), t2⟩ at h2
  rw [hf2] at h2
  have h3 := (RawInitialMachinePhases.cleanupFieldInTime 2 t2 (incoming.1, none)).evals_in_steps
  have hf3 : t2 (.field 2) = encodeWord (fieldValue c 2) := by
    simp [t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t2 (.field 2)).length + 1]
    (some ⟨some (.cleanupField 2), (incoming.1, none), t2⟩) =
    some ⟨some (.cleanupField 3), (incoming.1, none), t3⟩ at h3
  rw [hf3] at h3
  have h4 := (RawInitialMachinePhases.cleanupFieldInTime 3 t3 (incoming.1, none)).evals_in_steps
  have hf4 : t3 (.field 3) = encodeWord (fieldValue c 3) := by
    simp [t3, t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t3 (.field 3)).length + 1]
    (some ⟨some (.cleanupField 3), (incoming.1, none), t3⟩) =
    some ⟨some (.cleanupField 4), (incoming.1, none), t4⟩ at h4
  rw [hf4] at h4
  have h5 := (RawInitialMachinePhases.cleanupFieldInTime 4 t4 (incoming.1, none)).evals_in_steps
  have hf5 : t4 (.field 4) = encodeWord (fieldValue c 4) := by
    simp [t4, t3, t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t4 (.field 4)).length + 1]
    (some ⟨some (.cleanupField 4), (incoming.1, none), t4⟩) =
    some ⟨some (.cleanupField 5), (incoming.1, none), t5⟩ at h5
  rw [hf5] at h5
  have h6 := (RawInitialMachinePhases.cleanupFieldInTime 5 t5 (incoming.1, none)).evals_in_steps
  have hf6 : t5 (.field 5) = encodeWord (fieldValue c 5) := by
    simp [t5, t4, t3, t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t5 (.field 5)).length + 1]
    (some ⟨some (.cleanupField 5), (incoming.1, none), t5⟩) =
    some ⟨some .incrementIndex, (incoming.1, none), t6⟩ at h6
  rw [hf6] at h6
  have last := incrementIndexTrace t6 (incoming.1, none)
  have total := trace_trans_inline_RawInitialMachineCleanup _ (trace_trans_inline_RawInitialMachineCleanup _ (trace_trans_inline_RawInitialMachineCleanup _ (trace_trans_inline_RawInitialMachineCleanup _
    (trace_trans_inline_RawInitialMachineCleanup _ (trace_trans_inline_RawInitialMachineCleanup _ h1 h2) h3) h4) h5) h6) last
  have htime :
      ((((((encodeWord (fieldValue c 0)).length + 1 +
        ((encodeWord (fieldValue c 1)).length + 1)) +
        ((encodeWord (fieldValue c 2)).length + 1)) +
        ((encodeWord (fieldValue c 3)).length + 1)) +
        ((encodeWord (fieldValue c 4)).length + 1)) +
        ((encodeWord (fieldValue c 5)).length + 1)) + 1 =
      (encodeWords (Complexity.clauseWords c)).length + 7 := by
    simp [fieldValue, Complexity.clauseWords, Complexity.literalWords, encodeWords]
    omega
  rw [htime] at total
  have frame : Function.update t6 .index (true :: t6 .index) =
      Function.update (Function.update base .input suffix) .index (encodeWord (i + 1)) := by
    funext k
    cases k with
    | field j =>
      fin_cases j <;> simp [t6, t5, t4, t3, t2, t1, r, recordTapes, hempty]
    | index =>
      simp [t6, t5, t4, t3, t2, t1, r, recordTapes, hindex,
        encodeWord, List.replicate_succ]
    | _ => simp [t6, t5, t4, t3, t2, t1, r, recordTapes]
  rw [frame] at total
  exact total

end MaxCutGames.Foundations.PCP.RawInitialMachineCleanup

/-! One complete clause iteration of the actual initial graph machine. -/

namespace MaxCutGames.Foundations.PCP.RawInitialMachineBody

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineReadClause RawInitialMachineRows RawInitialMachineBudget

theorem guardTrace_succ (n i remaining : Nat) (input reversed : List Bool)
    (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .guard, state, loopTapes n i (remaining + 1) input reversed⟩) =
      some ⟨some (.fieldStart 0), (state.1, none),
        loopTapes n i remaining input reversed⟩ := by
  have h := MachineUnaryCounter.guardTrace_succ Tape.counter Label.guard
    (.fieldStart 0) (.scan .dummyVariables) program rfl
    (loopTapes n i remaining input reversed) remaining [] state.1 state.2
  have heq (r : Nat) : MachineUnaryCounter.counterTapes Tape.counter
      (loopTapes n i remaining input reversed) r [] = loopTapes n i r input reversed := by
    funext tape
    cases tape <;> simp [MachineUnaryCounter.counterTapes, loopTapes]
  simpa only [heq, Prod.mk.eta] using h

theorem guardTrace_zero (n i : Nat) (input reversed : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .guard, state, loopTapes n i 0 input reversed⟩) =
      some ⟨some (.scan .dummyVariables), (state.1, none),
        loopTapes n i 0 input reversed⟩ := by
  have h := MachineUnaryCounter.guardTrace_zero Tape.counter Label.guard
    (.fieldStart 0) (.scan .dummyVariables) program rfl
    (loopTapes n i 0 input reversed) [] state.1 state.2
  have heq : MachineUnaryCounter.counterTapes Tape.counter
      (loopTapes n i 0 input reversed) 0 [] = loopTapes n i 0 input reversed := by
    funext tape
    cases tape <;> simp [MachineUnaryCounter.counterTapes, loopTapes]
  simpa only [heq, Prod.mk.eta] using h

theorem bodyTrace {n : Nat} (i remaining : Nat) (c : Clause n)
    (suffix reversed : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[bodyTime i c]
      (some ⟨some .guard, state,
        loopTapes n i (remaining + 1)
          (encodeWords (Complexity.clauseWords c) ++ suffix) reversed⟩) =
      some ⟨some .guard, (RawInitialRows.clauseSigns c, none),
        loopTapes n (i + 1) remaining suffix
          ((encodeWords (RawInitialRows.clauseWords n i
            (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c))).reverse ++ reversed)⟩ := by
  let input := encodeWords (Complexity.clauseWords c) ++ suffix
  let base := loopTapes n i remaining input reversed
  let chunk := (encodeWords (RawInitialRows.clauseWords n i
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c))).reverse
  let emitted := loopTapes n i remaining input (chunk ++ reversed)
  have first := guardTrace_succ n i remaining input reversed state
  have read := readClauseTrace base c suffix rfl (fun _ => rfl) (state.1, none)
  have rows := rowsTrace (recordTapes base c suffix) n i
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c)
    rfl rfl rfl rfl rfl rfl
  have frame : outputTapes (recordTapes base c suffix) chunk =
      recordTapes emitted c suffix := by
    funext tape
    cases tape <;> simp [outputTapes, recordTapes, emitted, base, loopTapes]
  change (MachineComposition.advance (TM2.step program))^[6 * n + 18 * i +
      2 * nameSum c + 48]
    (some ⟨some (.scan (.tailVariables 0)), (RawInitialRows.clauseSigns c, none),
      recordTapes base c suffix⟩) =
    some ⟨some (.cleanupField 0), (RawInitialRows.clauseSigns c, none),
    outputTapes (recordTapes base c suffix) chunk⟩ at rows
  rw [frame] at rows
  have cleanup := RawInitialMachineCleanup.cleanupTrace emitted c suffix i
    (fun _ => rfl) rfl (RawInitialRows.clauseSigns c, none)
  have finalFrame : Function.update (Function.update emitted .input suffix)
      .index (encodeWord (i + 1)) =
      loopTapes n (i + 1) remaining suffix (chunk ++ reversed) := by
    funext tape
    cases tape <;> simp [emitted, loopTapes]
  rw [finalFrame] at cleanup
  have total := trace_trans_inline_RawInitialMachineBody _ (trace_trans_inline_RawInitialMachineBody _ (trace_trans_inline_RawInitialMachineBody _ first read) rows) cleanup
  have time : 1 + ((encodeWords (Complexity.clauseWords c)).length + 7) +
      (6 * n + 18 * i + 2 * nameSum c + 48) +
      ((encodeWords (Complexity.clauseWords c)).length + 7) = bodyTime i c := by
    simp only [bodyTime, nameSum]
    omega
  simpa only [time] using total

end MaxCutGames.Foundations.PCP.RawInitialMachineBody

/-! Exact execution of the dummy-row and final cleanup/reversal phases. -/

namespace MaxCutGames.Foundations.PCP.RawInitialMachineFinish

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases

def tapes_inline_RawInitialMachineFinish (varsWord counter index reversed output : List Bool) : Tape → List Bool
  | .«variables» => varsWord
  | .counter => counter
  | .index => index
  | .reversed => reversed
  | .output => output
  | _ => []

def finishTapes (n m : Nat) (rev : List Bool) : Tape → List Bool :=
  tapes_inline_RawInitialMachineFinish (encodeWord n) [false] (encodeWord m) rev []

theorem update_reversed_inline_RawInitialMachineFinish (varsWord counter index rev out word : List Bool) :
    Function.update (tapes_inline_RawInitialMachineFinish varsWord counter index rev out) .reversed word =
      tapes_inline_RawInitialMachineFinish varsWord counter index word out := by
  funext k
  cases k <;> simp [tapes_inline_RawInitialMachineFinish]

theorem cleanupTrace_inline_RawInitialMachineFinish (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[n + m + 6]
      (some ⟨some (.cleanupFinal 0), state, finishTapes n m rev⟩) =
      some ⟨some .reset, (state.1, none), tapes_inline_RawInitialMachineFinish [] [] [] rev []⟩ := by
  have h0 := (cleanupFinalInTime 0 (finishTapes n m rev) state).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[(encodeWord n).length + 1]
    (some ⟨some (.cleanupFinal 0), state, finishTapes n m rev⟩) = _ at h0
  rw [encodeWord_length] at h0
  have f0 : Function.update (finishTapes n m rev) .«variables» [] =
      tapes_inline_RawInitialMachineFinish [] [false] (encodeWord m) rev [] := by
    funext k
    cases k <;> simp [finishTapes, tapes_inline_RawInitialMachineFinish]
  change (MachineComposition.advance (TM2.step program))^[n + 2]
    (some ⟨some (.cleanupFinal 0), state, finishTapes n m rev⟩) =
    some ⟨some (.cleanupFinal 1), (state.1, none),
      Function.update (finishTapes n m rev) .«variables» []⟩ at h0
  rw [f0] at h0
  have h1 := (cleanupFinalInTime 1 (tapes_inline_RawInitialMachineFinish [] [false] (encodeWord m) rev [])
    (state.1, none)).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[2]
    (some ⟨some (.cleanupFinal 1), (state.1, none),
      tapes_inline_RawInitialMachineFinish [] [false] (encodeWord m) rev []⟩) = _ at h1
  have f1 : Function.update (tapes_inline_RawInitialMachineFinish [] [false] (encodeWord m) rev []) .counter [] =
      tapes_inline_RawInitialMachineFinish [] [] (encodeWord m) rev [] := by
    funext k
    cases k <;> simp [tapes_inline_RawInitialMachineFinish]
  change (MachineComposition.advance (TM2.step program))^[2]
    (some ⟨some (.cleanupFinal 1), (state.1, none), tapes_inline_RawInitialMachineFinish [] [false] (encodeWord m) rev []⟩) =
    some ⟨some (.cleanupFinal 2), (state.1, none),
      Function.update (tapes_inline_RawInitialMachineFinish [] [false] (encodeWord m) rev []) .counter []⟩ at h1
  rw [f1] at h1
  have h2 := (cleanupFinalInTime 2 (tapes_inline_RawInitialMachineFinish [] [] (encodeWord m) rev [])
    (state.1, none)).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[(encodeWord m).length + 1]
    (some ⟨some (.cleanupFinal 2), (state.1, none),
      tapes_inline_RawInitialMachineFinish [] [] (encodeWord m) rev []⟩) = _ at h2
  rw [encodeWord_length] at h2
  have f2 : Function.update (tapes_inline_RawInitialMachineFinish [] [] (encodeWord m) rev []) .index [] =
      tapes_inline_RawInitialMachineFinish [] [] [] rev [] := by
    funext k
    cases k <;> simp [tapes_inline_RawInitialMachineFinish]
  change (MachineComposition.advance (TM2.step program))^[m + 2]
    (some ⟨some (.cleanupFinal 2), (state.1, none), tapes_inline_RawInitialMachineFinish [] [] (encodeWord m) rev []⟩) =
    some ⟨some .reset, (state.1, none),
      Function.update (tapes_inline_RawInitialMachineFinish [] [] (encodeWord m) rev []) .index []⟩ at h2
  rw [f2] at h2
  have total := trace_trans_inline_RawInitialMachineFinish _ (trace_trans_inline_RawInitialMachineFinish _ h0 h1) h2
  simpa only [show (n + 2) + 2 + (m + 2) = n + m + 6 by omega] using total

theorem resetReverseTrace_inline_RawInitialMachineFinish (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[rev.length + 2]
      (some ⟨some .reset, state, tapes_inline_RawInitialMachineFinish [] [] [] rev []⟩) =
      some (haltList machine rev.reverse) := by
  have reset : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .reset, state, tapes_inline_RawInitialMachineFinish [] [] [] rev []⟩) =
      some ⟨some .finalReverse, initialState, tapes_inline_RawInitialMachineFinish [] [] [] rev []⟩ := rfl
  have transfer := (Reduction.MachineTransfer.transferAtInTime
    .reversed .output (by decide) id false .finalReverse none program rfl
    (tapes_inline_RawInitialMachineFinish [] [] [] rev []) (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[rev.length + 1]
    (some ⟨some .finalReverse, initialState, tapes_inline_RawInitialMachineFinish [] [] [] rev []⟩) = _ at transfer
  have frame : Reduction.MachineTransfer.tapesAt .reversed .output
      (tapes_inline_RawInitialMachineFinish [] [] [] rev []) [] (rev.reverse.map id ++ []) =
      (haltList machine rev.reverse).stk := by
    funext k
    change Tape at k
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, tapes_inline_RawInitialMachineFinish, haltList, machine]
    rfl
  change (MachineComposition.advance (TM2.step program))^[rev.length + 1]
    (some ⟨some .finalReverse, initialState, tapes_inline_RawInitialMachineFinish [] [] [] rev []⟩) =
    some ⟨none, initialState, Reduction.MachineTransfer.tapesAt .reversed .output
      (tapes_inline_RawInitialMachineFinish [] [] [] rev []) [] (rev.reverse.map id ++ [])⟩ at transfer
  rw [frame] at transfer
  have total := trace_trans_inline_RawInitialMachineFinish _ reset transfer
  rw [show 1 + (rev.length + 1) = rev.length + 2 by omega] at total
  change (MachineComposition.advance (TM2.step program))^[rev.length + 2]
    (some ⟨some .reset, state, tapes_inline_RawInitialMachineFinish [] [] [] rev []⟩) =
    some ⟨none, initialState, (haltList machine rev.reverse).stk⟩
  exact total

theorem update_finish_inline_RawInitialMachineFinish (n m : Nat) (rev word : List Bool) :
    Function.update (finishTapes n m rev) .reversed word = finishTapes n m word :=
  update_reversed_inline_RawInitialMachineFinish _ _ _ _ _ _

theorem copyFinishTrace_inline_RawInitialMachineFinish (n m r : Nat) (rev : List Bool) (phase : CopyPhase)
    (hsource : finishTapes n m rev (copySource phase) = encodeWord r) (state : State) :
    (MachineComposition.advance (TM2.step program))^[2 * r + 2]
      (some ⟨some (.scan phase), state, finishTapes n m rev⟩) =
      some ⟨some (copyNext phase), (state.1, none),
        finishTapes n m (List.replicate (copyScale phase * r) true ++ rev)⟩ := by
  have h := (copyInTime phase (finishTapes n m rev) r []
    (by simpa only [List.append_nil] using hsource) rfl state).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[2 * r + 2]
    (some ⟨some (.scan phase), state, finishTapes n m rev⟩) =
    some ⟨some (copyNext phase), (state.1, none),
      Function.update (finishTapes n m rev) .reversed
        (List.replicate (copyScale phase * r) true ++ rev)⟩ at h
  rw [update_finish_inline_RawInitialMachineFinish] at h
  exact h

theorem closeDummyTailTrace_inline_RawInitialMachineFinish (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .closeDummyTail, state, finishTapes n m rev⟩) =
      some ⟨some (.scan .dummyReverse), state, finishTapes n m (false :: rev)⟩ := by
  change some (TM2.stepAux (program .closeDummyTail) state (finishTapes n m rev)) = _
  simp only [program, TM2.stepAux]
  congr 2
  exact update_finish_inline_RawInitialMachineFinish _ _ _ _

theorem closeDummyReverseTrace_inline_RawInitialMachineFinish (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .closeDummyReverse, state, finishTapes n m rev⟩) =
      some ⟨some .dummyRelation, state, finishTapes n m (false :: rev)⟩ := by
  change some (TM2.stepAux (program .closeDummyReverse) state (finishTapes n m rev)) = _
  simp only [program, TM2.stepAux]
  congr 2
  exact update_finish_inline_RawInitialMachineFinish _ _ _ _

theorem dummyRelationTrace_inline_RawInitialMachineFinish (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .dummyRelation, state, finishTapes n m rev⟩) =
      some ⟨some (.cleanupFinal 0), state,
        finishTapes n m ((encodeWords (List.replicate 4096 1)).reverse ++ rev)⟩ := by
  change some (TM2.stepAux (program .dummyRelation) state (finishTapes n m rev)) = _
  rw [program, Reduction.MachineSubstitution.stepAux_pushWord, trueRelationWords]
  simp only [TM2.stepAux]
  congr 2
  exact update_finish_inline_RawInitialMachineFinish _ _ _ _

/-- The three actual prefix scans and three emitting transitions append the complete dummy row. -/
theorem dummyTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 4 * m + 9]
      (some ⟨some (.scan .dummyVariables), state, finishTapes n m rev⟩) =
      some ⟨some (.cleanupFinal 0), (state.1, none),
        finishTapes n m ((encodeWords (RawInitialRows.dummyWords n m)).reverse ++ rev)⟩ := by
  let a := List.replicate n true ++ rev
  let b := List.replicate m true ++ a
  let c := false :: b
  let d := List.replicate (6 * m) true ++ c
  let e := false :: d
  have h0 := copyFinishTrace_inline_RawInitialMachineFinish n m n rev .dummyVariables rfl state
  simp only [copyScale, copyNext, Nat.one_mul] at h0
  have h1 := copyFinishTrace_inline_RawInitialMachineFinish n m m a .dummyIndex rfl (state.1, none)
  simp only [copyScale, copyNext, Nat.one_mul] at h1
  have h2 := closeDummyTailTrace_inline_RawInitialMachineFinish n m b (state.1, none)
  have h3 := copyFinishTrace_inline_RawInitialMachineFinish n m m c .dummyReverse rfl (state.1, none)
  simp only [copyScale, copyNext] at h3
  have h4 := closeDummyReverseTrace_inline_RawInitialMachineFinish n m d (state.1, none)
  have h5 := dummyRelationTrace_inline_RawInitialMachineFinish n m e (state.1, none)
  have total := trace_trans_inline_RawInitialMachineFinish _ (trace_trans_inline_RawInitialMachineFinish _ (trace_trans_inline_RawInitialMachineFinish _
    (trace_trans_inline_RawInitialMachineFinish _ (trace_trans_inline_RawInitialMachineFinish _ h0 h1) h2) h3) h4) h5
  have output : (encodeWords (List.replicate 4096 1)).reverse ++ e =
      (encodeWords (RawInitialRows.dummyWords n m)).reverse ++ rev := by
    have rep : List.replicate m true ++ (List.replicate n true ++ rev) =
        List.replicate (n + m) true ++ rev := by
      rw [← List.append_assoc, ← List.replicate_add, Nat.add_comm m n]
    simp only [RawInitialRows.dummyWords, encodeWords_append, encodeWords,
      List.append_nil, List.reverse_append,
      encodeWord, List.reverse_cons,
      List.reverse_replicate, List.append_assoc, List.singleton_append,
      a, b, c, d, e]
    rw [rep]
    simp only [List.reverse_nil, List.nil_append, List.cons_append]
  rw [output] at total
  simpa only [show (((((2 * n + 2) + (2 * m + 2)) + 1) + (2 * m + 2)) + 1) + 1 =
    2 * n + 4 * m + 9 by omega] using total

/-- Exact final execution, including all tape cleanup and the canonical halt state. -/
theorem finishTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[
        3 * n + 5 * m + 17 + (encodeWords (RawInitialRows.dummyWords n m)).length + rev.length]
      (some ⟨some (.scan .dummyVariables), state, finishTapes n m rev⟩) =
      some (haltList machine (rev.reverse ++ encodeWords (RawInitialRows.dummyWords n m))) := by
  let emitted := (encodeWords (RawInitialRows.dummyWords n m)).reverse ++ rev
  have total := trace_trans_inline_RawInitialMachineFinish _ (trace_trans_inline_RawInitialMachineFinish _ (dummyTrace n m rev state)
    (cleanupTrace_inline_RawInitialMachineFinish n m emitted (state.1, none)))
    (resetReverseTrace_inline_RawInitialMachineFinish emitted (state.1, none))
  have hout : emitted.reverse = rev.reverse ++ encodeWords (RawInitialRows.dummyWords n m) := by
    simp only [emitted, List.reverse_append, List.reverse_reverse]
  rw [hout] at total
  have htime : (2 * n + 4 * m + 9) + (n + m + 6) + (emitted.length + 2) =
      3 * n + 5 * m + 17 + (encodeWords (RawInitialRows.dummyWords n m)).length + rev.length := by
    simp only [emitted, List.length_append, List.length_reverse]
    omega
  rwa [htime] at total

end MaxCutGames.Foundations.PCP.RawInitialMachineFinish

/-! Exact execution of the clause loop, in the original occurrence order. -/

namespace MaxCutGames.Foundations.PCP.RawInitialMachineLoop

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineBudget RawInitialMachineBody RawInitialMachineFinish

def finalSigns {n : Nat} (incoming : RawInitialMachineModel.Signs) :
    List (Clause n) → RawInitialMachineModel.Signs
  | [] => incoming
  | c :: cs => finalSigns (RawInitialRows.clauseSigns c) cs

theorem empty_loopTapes (n i : Nat) (rev : List Bool) :
    loopTapes n i 0 [] rev = finishTapes n i rev := by
  funext tape
  cases tape <;> rfl

/-- The complete actual loop: every clause is read once, emits six rows, and
leaves clean field tapes before the next guard. The final zero guard is included. -/
theorem loopTrace {n : Nat} (i : Nat) (cs : List (Clause n))
    (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[loopTime i cs]
      (some ⟨some .guard, state, loopTapes n i cs.length (clauseInput cs) rev⟩) =
      some ⟨some (.scan .dummyVariables), (finalSigns state.1 cs, none),
        finishTapes n (i + cs.length) ((encodeWords (clauseOutput n i cs)).reverse ++ rev)⟩ := by
  induction cs generalizing i rev state with
  | nil =>
      have h := RawInitialMachineBody.guardTrace_zero n i [] rev state
      rw [empty_loopTapes] at h
      simpa only [loopTime, List.length_nil, clauseInput_nil, clauseOutput_nil,
        finalSigns, encodeWords, List.reverse_nil, List.nil_append, Nat.add_zero,
        empty_loopTapes] using h
  | cons c cs ih =>
      have first := bodyTrace i cs.length c (clauseInput cs) rev state
      have rest := ih (i + 1)
        ((encodeWords (RawInitialRows.clauseWords n i
          (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c))).reverse ++ rev)
        (RawInitialRows.clauseSigns c, none)
      have total := trace_trans_inline_RawInitialMachineLoop _ first rest
      have hi : i + 1 + cs.length = i + (cs.length + 1) := by omega
      simpa only [loopTime, List.length_cons, clauseInput_cons, clauseOutput_cons,
        encodeWords_append, List.reverse_append, List.append_assoc, finalSigns, hi] using total

end MaxCutGames.Foundations.PCP.RawInitialMachineLoop

/-! The actual finite machine computing the initial graph's full serialized
table. The runtime bound counts every parse, row, cleanup and output reversal. -/

namespace MaxCutGames.Foundations.PCP.MachineRawInitialTable

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineBudget RawInitialMachineLoop

def prefixBits (F : Formula) : List Bool :=
  encodeWords ([F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
    clauseOutput F.«variables» 0 F.clauses)

theorem outputBits (F : Formula) :
    GraphTables.tableBits (RawInitialTables.table F) = prefixBits F ++
      encodeWords (RawInitialRows.dummyWords F.«variables» F.clauses.length) := by
  change encodeWords (GraphTables.tableWords (RawInitialTables.table F)) = _
  rw [tableWords_decomposition, encodeWords_append]
  rfl

theorem machineTrace (F : Formula) :
    (MachineComposition.advance (TM2.step program))^[fullBudget F]
      (some (initList machine (formulaBits F))) =
      some (haltList machine (GraphTables.tableBits (RawInitialTables.table F))) := by
  have startup := RawInitialMachineStart.formulaStartTrace F
  rw [startTapes_eq] at startup
  have loop := loopTrace 0 F.clauses
    (encodeWords [F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1]).reverse
    initialState
  have hprefix : (encodeWords (clauseOutput F.«variables» 0 F.clauses)).reverse ++
      (encodeWords [F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1]).reverse =
      (prefixBits F).reverse := by
    simp only [prefixBits, encodeWords_append, List.reverse_append]
  rw [hprefix, Nat.zero_add] at loop
  have finish := RawInitialMachineFinish.finishTrace F.«variables» F.clauses.length
    (prefixBits F).reverse (finalSigns initialState.1 F.clauses, none)
  rw [List.reverse_reverse, ← outputBits F] at finish
  have total := trace_trans_inline_MachineRawInitialTable _ (trace_trans_inline_MachineRawInitialTable _ startup loop) finish
  have time : (3 * F.«variables» + 5 * F.clauses.length + 13 + loopTime 0 F.clauses) +
      (3 * F.«variables» + 5 * F.clauses.length + 17 +
        (encodeWords (RawInitialRows.dummyWords F.«variables» F.clauses.length)).length +
        (prefixBits F).reverse.length) = fullBudget F := by
    rw [fullBudget, outputBits, List.length_append, List.length_reverse]
    omega
  simpa only [time] using total

def outputsInTime (F : Formula) :
    TM2OutputsInTime machine (formulaBits F)
      (some (GraphTables.tableBits (RawInitialTables.table F)))
      (timePolynomial.eval (formulaBits F).length) where
  steps := fullBudget F
  evals_in_steps := machineTrace F
  steps_le_m := fullBudget_le F

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime formulaEncoding.encode GraphTables.encoding.encode
      RawInitialTables.table where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun F := by
    change TM2OutputsInTime machine ((formulaBits F).map id)
      (some ((GraphTables.tableBits (RawInitialTables.table F)).map id))
      (timePolynomial.eval (formulaBits F).length)
    have hi := @List.map_id (machine.Γ machine.k₀) (formulaBits F)
    have ho := @List.map_id (machine.Γ machine.k₁)
      (GraphTables.tableBits (RawInitialTables.table F))
    rw [hi, ho]
    exact outputsInTime F

end MaxCutGames.Foundations.PCP.MachineRawInitialTable

/-!
Actual finite-machine phases for the final twelve-query verifier conversion.
The graph codec stores a relation bit as the unary natural 0 or 1. The reader
below consumes those variable-length codewords, rather than treating the row
as an already available raw Boolean block. Its finite register size is fixed
at 4096 for the final alphabet, independent of the graph input size.
-/

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_PreprocessingStageMaps
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Executable, codec-compatible stage maps for the actual preprocessing
constructor. The decomposition below is an equality of its existing functions;
runtime certificates must be supplied by the respective concrete machines. -/
namespace MaxCutGames.Foundations.PCP.PreprocessingStageMaps
open PreprocessingRegularTables

def regular (H : BaseTable) (t : GraphTables.Table) : PortTables.Input (internalDegree + 1) :=
  ⟨vertexCount t (PreprocessingRegularTables.padding t), regularize H t⟩

end MaxCutGames.Foundations.PCP.PreprocessingStageMaps

end OAI
end

section
-- module Solutions.OAIQ087_MC.MaxCut_PCP_TableIteration
attribute [-instance] _root_.OAI.MaxCutGames.Gadget.OrientationVectors.nonzeroAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iteration of the concrete stored-table round, with the original formula's
actual initial graph size controlling the number of rounds. -/

namespace MaxCutGames.Foundations.PCP.TableIteration

open RoundTables
open Target Complexity

def iterationCount (F : Formula) : Nat := AmplificationIteration.rounds (size (initial F))

def outputTable (H : BaseTable) (F : Formula) : GraphTables.Table :=
  runTables H (iterationCount F) (RawInitialTables.table F)

def gapMap (H : BaseTable) (F : Formula) : Formula := FinalTableFormula.output (outputTable H F)

end MaxCutGames.Foundations.PCP.TableIteration

/-! Exact transport of powering through a change of ports. The target's actual
address selector is pulled back, so no compatibility of enumeration orders or
consistency restriction on raw padded labels is needed. -/

/-! Gap amplification for the actual numbered table round. The fixed base
expander is the only supplied construction datum with a spectral certificate. -/

/-! Both semantic implications for the actual stored-table 3SAT gap map.
The positive clause gap follows from the full actual repeated transformation.
The full map's polynomial-time machine is certified separately. -/

end OAI
end


