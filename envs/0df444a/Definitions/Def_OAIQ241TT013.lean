-- Prove2me | Definitions.Def_OAIQ241TT013
-- name    : OAIQ241TT013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T23:04:47.162359+00:00
-- url     : https://prove2.me/theorems/987ba5ff-9fc7-44f3-bda9-76a39073b514
-- title:
--   Definitions bundle OAIQ241TT013 of the split of OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 147 declarations of OpenAI's Lean: 144 definitions, 2 instances and 1 theorem. The definitions and types are `OAI.AlgorithmicThinTrees.GreedyTree.Stack.connectedProgram`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.deleteProgram`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.eraseBit`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.eraseProgram`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.expands`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.incident`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.initBit`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.next`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.reachedAll`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.start`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.treeProgram`, `OAI.AlgorithmicThinTrees.GreedyTree.Stack.walk`, `OAI.AlgorithmicThinTrees.InputStack.bCount`, `OAI.AlgorithmicThinTrees.InputStack.bCountBinary`, `OAI.AlgorithmicThinTrees.InputStack.bEndpointBlock`, `OAI.AlgorithmicThinTrees.InputStack.bLefts`, `OAI.AlgorithmicThinTrees.InputStack.bPrepare`, `OAI.AlgorithmicThinTrees.InputStack.bRecords`, `OAI.AlgorithmicThinTrees.InputStack.bRights`, `OAI.AlgorithmicThinTrees.InputStack.formatTest`, `OAI.AlgorithmicThinTrees.Iteration.Stack.finish`, `OAI.AlgorithmicThinTrees.Iteration.Stack.initialCountProgram`, `OAI.AlgorithmicThinTrees.Iteration.Stack.large`, `OAI.AlgorithmicThinTrees.Iteration.Stack.nextCountBinary`, `OAI.AlgorithmicThinTrees.Iteration.Stack.nextCountProgram`, `OAI.AlgorithmicThinTrees.Iteration.Stack.selectState`, `OAI.AlgorithmicThinTrees.Iteration.Stack.startProgram`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.coefficients`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.gridMesh`, `OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.gridStep`, `OAI.AlgorithmicThinTrees.Normalization.Stack.fixedStep`, `OAI.AlgorithmicThinTrees.Normalization.Stack.gram`, `OAI.AlgorithmicThinTrees.Normalization.Stack.multiplierProgram`, `OAI.AlgorithmicThinTrees.Normalization.Stack.testProgram`, `OAI.AlgorithmicThinTrees.Normalization.Stack.thresholdProgram`, `OAI.AlgorithmicThinTrees.Normalization.Stack.updated`, `OAI.AlgorithmicThinTrees.Signing.Stack.factorRows`, `OAI.AlgorithmicThinTrees.Signing.Stack.outerFields`, `OAI.AlgorithmicThinTrees.Signing.Stack.signerInput`, `OAI.AlgorithmicThinTrees.Signing.Stack.whiten` and 104 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `MatrixSigning_Realization_CoordinateRealization`, `MatrixSigning_Realization_CurvatureRealization`, `MatrixSigning_Realization_EndpointRealization`, `MatrixSigning_Realization_FaceArrayRealization`, `MatrixSigning_Realization_FaceChoiceRealization`, `MatrixSigning_Realization_FaceQueryRealization`, `MatrixSigning_Realization_FaceRunRealization`, `MatrixSigning_Realization_LevelPencilRealization`, `MatrixSigning_Realization_OptimizeRealization`, `MatrixSigning_Realization_OriginalFieldsRealization`, `MatrixSigning_Realization_OriginalSignRealization`, `MatrixSigning_Realization_PotentialRealization`, `MatrixSigning_Realization_RootRealization`, `MatrixSigning_Realization_ScheduleRealization`, `MatrixSigning_Realization_SelectionRealization`, `MatrixSigning_Realization_StencilRealization`, `MatrixSigning_Realization_ValueDataRealization`, `MatrixSigning_Realization_ValueEvalRealization`, `MatrixSigning_Realization_ValueObjectiveRealization`, `MatrixSigning_Realization_ValueQueryRealization`, `MatrixSigning_Realization_VarianceRealization`, `MatrixSigning_Realization_WitnessRealization`, `ThinTrees_Arithmetic_BinaryArithmetic`, `ThinTrees_Arithmetic_BoolPrograms`, `ThinTrees_Arithmetic_ScalarRealization`, `ThinTrees_Arithmetic_WordHead`, `ThinTrees_Continuation_BitBound`, `ThinTrees_Encoding_GreedyRealization`, `ThinTrees_Encoding_InputDispatch`, `ThinTrees_Encoding_InputExpansion`, `ThinTrees_Normalization_Realization`, `ThinTrees_Pencil_SearchRealization`, `ThinTrees_RationalMatrix_InverseRealization`, `ThinTrees_RationalMatrix_MatrixRealization`, `ThinTrees_RationalMatrix_SchurHistory`, `ThinTrees_Signing_GramRealization`, `ThinTrees_Signing_Realization`, `ThinTrees_Sparsification_IterationRealization`, `ThinTrees_Sparsification_Realization`.
--
--   **Imports.** It imports the published bundle `Def_AlgorithmicThinTrees`; the bundles `OAIQ241TT010` and `OAIQ241TT011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ241TT014`.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT010
import Definitions.Def_OAIQ241TT011

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_CoordinateRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def reEntry : Realizes (prodCode (prodCode matrixCode natCode) natCode) ratCode reEntryData :=
  let ctx := prodCode matrixCode natCode
  let p := first ctx natCode
  let M := p.then (first matrixCode natCode)
  let i := p.then (second matrixCode natCode)
  let j := second ctx natCode
  let ij := (M.both (i.both j)).then matrixEntry
  let ji := (M.both (j.both i)).then matrixEntry
  (((i.both j).then natLE).ite ij ji).congr (by intro p;simp [reEntryData])

def imEntry : Realizes (prodCode (prodCode matrixCode natCode) natCode) ratCode imEntryData :=
  let ctx := prodCode matrixCode natCode
  let p := first ctx natCode
  let M := p.then (first matrixCode natCode)
  let i := p.then (second matrixCode natCode)
  let j := second ctx natCode
  let ij := (M.both (i.both j)).then matrixEntry
  let ji := (M.both (j.both i)).then matrixEntry
  (((i.both j).then natLT).ite ji (((j.both i).then natLT).ite ij.neg
    (constant _ ratCode 0))).congr (by intro p;simp [imEntryData])

def realDecode : Realizes (prodCode natCode matrixCode) matrixCode realDecodeData :=
  let re := squareTabulate reEntry
  let im := squareTabulate imEntry
  ((re.both (im.then negateMatrix)).both (im.both re)).then fromBlocks

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceArrayRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

def activeIndices : Realizes vectorCode indicesCode activeData :=
  let xs := first vectorCode natCode
  let j := second vectorCode natCode
  let value := (j.both xs).then (getD ratCode 0)
  let test := value.abs.lt (constant (prodCode vectorCode natCode) ratCode 1)
  (((identity vectorCode).both ((lengthList ratCode).then range)).then test.filterCtx)

def extendEntry : Realizes (prodCode extendDataCode natCode) ratCode extendEntryData :=
  let pc := prodCode extendDataCode natCode
  let data := first extendDataCode natCode
  let e := data.then (first indicesCode (prodCode vectorCode vectorCode))
  let vecs := data.then (second indicesCode (prodCode vectorCode vectorCode))
  let base := vecs.then (first vectorCode vectorCode)
  let y := vecs.then (second vectorCode vectorCode)
  let i := second extendDataCode natCode
  let fallback := (i.both base).then (getD ratCode 0)
  let ctx := first pc natCode
  let j := second pc natCode
  let test := ((((j.both (ctx.then e)).then (getD natCode 0)).both (ctx.then i)).then natEq)
  let val := (j.both (ctx.then y)).then (getD ratCode 0)
  (((identity pc).both (fallback.both ((e.then (lengthList natCode)).then range))).then
    (test.findValue val)).congr (by intro p;simp only [extendEntryData,beq_eq_decide,id_eq])

def extendVector : Realizes extendDataCode vectorCode extendData :=
  let base := (second indicesCode (prodCode vectorCode vectorCode)).then (first vectorCode vectorCode)
  (((identity extendDataCode).both (base.then (lengthList ratCode))).then extendEntry.tabulate)

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RootRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def rootStepRealizes (pow : ℕ) : Realizes rootStateCode rootStateCode (rootStep pow) :=
  let q := first ratCode (prodCode ratCode ratCode)
  let s := second ratCode (prodCode ratCode ratCode)
  let lo := s.then (first ratCode ratCode)
  let hi := s.then (second ratCode ratCode)
  let mid := (lo.add hi).div (constant rootStateCode ratCode 2)
  (q.both (((mid.pow pow).le q).ite (mid.both hi) (lo.both mid))).congr (by
    intro p;simp [rootStep])

def rootRun (pow : ℕ) : Realizes (prodCode ratCode natCode)
    (prodCode ratCode ratCode) (fun p => ((rootStep pow)^[p.2] (p.1,(0,1))).2) :=
  let q := first ratCode natCode
  let fuel := second ratCode natCode
  let init := q.both (constant (prodCode ratCode natCode) (prodCode ratCode ratCode) (0,1))
  ((fuel.both init).then (rootStepRealizes pow).iterate).then
    (second ratCode (prodCode ratCode ratCode))

def upperSqrt : Realizes (prodCode ratCode ratCode) ratCode
    (fun p => RationalRoot.upperSqrt p.1 p.2) :=
  let q := first ratCode ratCode
  let fuel := (second ratCode ratCode).then ratDenSize
  (((q.both fuel).then (rootRun 2)).then (second ratCode ratCode)).congr (by
    intro p
    simp only [square_iterate,RationalRoot.upperSqrt])

def approxPsi : Realizes (prodCode ratCode ratCode) ratCode
    (fun p => Scalar.approxPsi p.1 p.2) :=
  let x := first ratCode ratCode
  let fuel := (second ratCode ratCode).then ratDenSize
  let q := (constant (prodCode ratCode ratCode) ratCode 1).sub (x.pow 2)
  (((q.both fuel).then (rootRun 3)).then (first ratCode ratCode)).congr (by
    intro p
    simp only [cube_iterate,Scalar.approxPsi])

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_LevelPencilRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix

variable {α : Type*}
def withLevel : Realizes levelInputCode pencilCode withLevelData :=
  let B := first pencilCode (prodCode vectorCode ratCode)
  let f := (second pencilCode (prodCode vectorCode ratCode)).then (first vectorCode ratCode)
  let q := (second pencilCode (prodCode vectorCode ratCode)).then (second vectorCode ratCode)
  let C := B.then (first matrixCode (listCode matrixCode))
  let coeff := B.then (second matrixCode (listCode matrixCode))
  let one := ((first matrixCode ratCode).both (second matrixCode ratCode).neg).then blockScalar
  ((C.both q).then blockScalar).both ((coeff.both f).then (one.zipWith [] 0))

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_WitnessRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def witnessEvaluation : Realizes witnessStateCode matrixObjectCode
    (fun a => (⟨a.m,a.B.eval a.y⟩ : MatrixObject)) :=
  let B := witnessStateView.then (first pencilCode vectorCode)
  let size := B.then ((first matrixCode (listCode matrixCode)).then (lengthList vectorCode))
  let evaluation := witnessStateView.then evalPencil
  (size.both evaluation).changeOutput matrixObjectCode
    (fun a => ⟨a.m,a.B.eval a.y⟩) (by
      intro a
      change prodCode natCode matrixCode ((matrixData a.B.constant).length,
        evalPencilData (pencilData a.B,List.ofFn a.y))=_
      rw [evalPencil_data]
      simp only [matrixData,List.length_ofFn,matrixObjectCode])

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_OptimizeRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def optLevel : Realizes (prodCode optCode natCode) ratCode
    (fun p => RationalSDP.level p.1.delta p.1.U p.2) :=
  let p := first optCode natCode
  let k := (second optCode natCode).then natToRat
  (p.then optUpper).neg.add (k.mul (p.then optDelta))
def optLevelPencil : Realizes (prodCode optCode natCode) pencilCode
    (fun p => pencilData (p.1.B.withLevel p.1.f (RationalSDP.level p.1.delta p.1.U p.2))) :=
  let p := first optCode natCode
  (((p.then optB).both ((p.then optF).both optLevel)).then withLevel).congr
    (fun p => withLevel_data p.1.B p.1.f _)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueDataRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def matrixVariable (second : Bool) : Realizes matrixVarCode matrixCode (matrixVariableData second) :=
  ((first natCode vectorCode).both (coordinates second)).then realDecode

def sandwich : Realizes (prodCode matrixCode matrixCode) matrixCode sandwichData :=
  (matrixMul.both (first matrixCode matrixCode)).then matrixMul

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueEvalRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def veEye := veN.then identityMatrix
def veVariable (second : Bool) := (veD.both veY).then (matrixVariable second)

def veSum : Realizes valueEvalCode matrixCode (fun p => sumData p.1) :=
  (veN.both ((veP.then vdX).both (veP.then vdAtoms))).then weightedSum
def eta : Realizes (prodCode valueDataCode matrixCode) matrixCode etaData :=
  let p := first valueDataCode matrixCode
  let Z := second valueDataCode matrixCode
  let n := (p.then vdD).then realDimension
  let weights := (p.then vdTheta).then ((constant ratCode ratCode 384).mul (identity ratCode)).map
  let atomSandwich := ((second matrixCode matrixCode).both (first matrixCode matrixCode)).then sandwich
  let atoms := (Z.both (p.then vdAtoms)).then atomSandwich.mapCtx
  (n.both (weights.both atoms)).then weightedSum
def schurEval (second : Bool) : Realizes valueEvalCode matrixCode (schurEvalData second) :=
  let S := (constant valueEvalCode boolCode second).ite veSum (veSum.then negateMatrix)
  let etaZ := (veP.both (veVariable (!second))).then eta
  let top := (((veTime.scaleMatrix veEye).both S).then matrixAdd).both etaZ |>.then matrixSub
  ((top.both veEye).both (veEye.both (veVariable second))).then fromBlocks

def lowerBox (second : Bool) : Realizes valueEvalCode matrixCode (lowerBoxData second) :=
  ((veVariable second).both ((constant valueEvalCode ratCode (1/400)).scaleMatrix veEye)).then matrixSub

def upperBox (second : Bool) : Realizes valueEvalCode matrixCode (upperBoxData second) :=
  ((((constant valueEvalCode ratCode 200).div veEps).scaleMatrix veEye).both (veVariable second)).then matrixSub

def valueEval : Realizes valueEvalCode matrixCode valueEvalData :=
  (((((((schurEval false).blockWith (schurEval true)).blockWith (lowerBox false)).blockWith
    (upperBox false)).blockWith (lowerBox true)).blockWith (upperBox true)).blockWith
    (veTime.then tinyMatrix)).blockWith (((constant valueEvalCode ratCode 100).sub veTime).then tinyMatrix)

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueObjectiveRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine Matrix
open scoped BigOperators

def traceMatrix : Realizes matrixCode ratCode traceData :=
  let M := first matrixCode natCode
  let i := second matrixCode natCode
  let entry := (M.both (i.both i)).then matrixEntry
  ((((identity matrixCode).both (lengthList vectorCode)).then entry.tabulate).then sumRationals)

def valueObjective : Realizes valueEvalCode ratCode valueObjectiveData :=
  let dy := veD.both veY
  let t0 := (dy.then (coordinates false)).then traceMatrix
  let t1 := (dy.then (coordinates true)).then traceMatrix
  veTime.add (veEps.mul (t0.add t1))
def valueCoeffs : Realizes valueDataCode vectorCode valueCoeffsData :=
  let p := first valueDataCode natCode
  let n := (p.then vdD).then valueDimension
  let i := second valueDataCode natCode
  let basis := (n.both i).then basisVector
  let one := (p.both basis).then valueObjective
  ((identity valueDataCode).both (vdD.then valueDimension)).then one.tabulate
def valuePencil : Realizes valueDataCode pencilCode valuePencilData :=
  ((identity valueDataCode).both (vdD.then valueDimension)).then valueEval.pencilFromEval

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ValueQueryRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def valueLipschitz : Realizes valueDataCode ratCode
    (fun p => RationalSDP.valueLipschitz p.1 p.2.2.2.2) :=
  let one := constant valueDataCode ratCode 1
  let two := constant valueDataCode ratCode 2
  let d := vdD.then natToRat
  let n := (vdD.then valueDimension).then natToRat
  (n.add one).mul (one.add ((two.mul vdEps).mul d))
def valueOuterRadius : Realizes valueDataCode ratCode
    (fun p => RationalSDP.valueOuterRadius p.1 p.2.2.2.2) :=
  let c (q : ℚ) := constant valueDataCode ratCode q
  let d := vdD.then natToRat
  let n := (vdD.then valueDimension).then natToRat
  (n.add (c 1)).mul ((c 100).add (((c 400).div vdEps).mul (d.add (c 1))))
def valueInnerRadius : Realizes valueDataCode ratCode
    (fun p => RationalSDP.valueInnerRadius p.1) :=
  let c (q : ℚ) := constant valueDataCode ratCode q
  (c 1).div ((c 4000).mul (((vdD.then natToRat).pow 2).add (c 1)))

def vqOpt : Realizes valueQueryCode optCode ValueQueryParams.opt :=
  let L := vqData.then valueLipschitz
  let R := vqData.then valueOuterRadius
  let r := vqData.then valueInnerRadius
  let near := (vqDelta.div (L.mul (((constant valueQueryCode ratCode 2).mul R).add r))).mul r
  let B := vqData.then valuePencil
  let f := vqData.then valueCoeffs
  (B.both (f.both (vqDelta.both (near.both (R.both (constant valueQueryCode ratCode 100)))))).changeOutput
    optCode ValueQueryParams.opt (by
      intro p
      simp only [valuePencil_data,valueCoeffs_data]
      rfl)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_PotentialRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

def ppRootTolerance : Realizes potentialCode ratCode
    (fun p => RationalSDP.rootTolerance p.d p.N p.lam p.error) :=
  let c (q : ℚ) := constant potentialCode ratCode q
  ppError.div ((c 2).mul ((((c 38400).mul (ppD.then natToRat)).add (ppLam.mul (ppN.then natToRat))).add (c 1)))
def ppTheta : Realizes potentialCode vectorCode (fun p => List.ofFn p.theta) :=
  let one := ((second ratCode ratCode).both (first ratCode ratCode)).then approxPsi
  ((ppRootTolerance.both ppX).then one.mapCtx).congr (by
    intro p
    simp only [List.map_ofFn,Function.comp_def]
    rfl)
def ppQuery : Realizes potentialCode valueQueryCode PotentialParams.query :=
  let v := ppD.both (ppAtoms.both (ppX.both (ppTheta.both (ppNu.div (ppD.then natToRat)))))
  (v.both (ppError.div (constant potentialCode ratCode 4))).changeOutput valueQueryCode
    PotentialParams.query (fun _ => rfl)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ScheduleRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α : Type*} {ea : α → Word} {f g : α → ℚ}

def Realizes.inv (r : Realizes ea ratCode f) : Realizes ea ratCode (fun x => (f x)⁻¹) :=
  ((constant ea ratCode 1).div r).congr (by intro x;exact one_div _)

def movementBudget : Realizes (prodCode natCode ratCode) ratCode
    (fun p => Schedule.movementBudget p.1 p.2) :=
  let c (q : ℚ) := constant (prodCode natCode ratCode) ratCode q
  let n := (first natCode ratCode).then natToRat
  let eps := second natCode ratCode
  let J := (c 1).add ((((c 3).mul n).pow 2).div (eps.div (c 40000)))
  let E := ((c 2).mul (J.pow 2)).mul (((c 1).add ((c 3).mul n)).pow 2)
  (c 1).max ((((c 48).mul E).div (c 23)).max ((c 4).mul ((c 1).add ((c 9).mul (n.pow 2)))))

def saThreshold :=
  saLam.div ((constant scheduleArgsCode ratCode 512).mul
    (((saN.both saEpsilon).then movementBudget).pow 2))

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceQueryRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def fIndices : Realizes faceCode indicesCode
    (fun p => List.ofFn (fun j => (RationalFace.activeIndex p.base j).val)) :=
  (fBase.then activeIndices).congr (fun p => activeIndex_data p.base)
def fN : Realizes faceCode natCode FaceParams.n :=
  (fIndices.then (lengthList natCode)).congr (fun _ => List.length_ofFn)
def fState : Realizes faceCode vectorCode (fun p => List.ofFn (RationalFace.faceState p.base)) :=
  ((fBase.both fIndices).then gather).congr (fun p => gather_data p.base (RationalFace.activeIndex p.base))

def fpExtend : Realizes facePointCode vectorCode
    (fun s => List.ofFn (RationalFace.extend (RationalFace.activeIndex s.p.base) s.p.base s.y)) :=
  (((fpP.then fIndices).both ((fpP.then fBase).both fpY)).then extendVector).congr
    (fun s => extendData_data (RationalFace.activeIndex s.p.base) s.p.base s.y)
def fpPotential : Realizes (prodCode facePointCode ratCode) potentialCode FacePoint.potential :=
  let s := first facePointCode ratCode
  let p := s.then fpP
  let err := second facePointCode ratCode
  ((p.then fD).both ((p.then fAtoms).both ((s.then fpExtend).both
    ((p.then fNu).both ((p.then fLam).both err))))).changeOutput potentialCode
    FacePoint.potential (fun _ => rfl)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_StencilRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α : Type*}

def vectorNeg : Realizes vectorCode vectorCode (List.map (fun q : ℚ => -q)) :=
  (identity ratCode).neg.map
def fiBasis : Realizes faceIndexCode vectorCode
    (fun s : FaceIndex => List.ofFn (Difference.rationalBasis s.2)) :=
  (((fiP.then fN).both fiI).then basisVector).congr (fun s => basis_data s.2)

def fdBasisI := fdS.then fiBasis
def fdBasisJ : Realizes faceDoubleCode vectorCode
    (fun s : FaceDouble => List.ofFn (Difference.rationalBasis s.2)) :=
  (((fdP.then fN).both fdJ).then basisVector).congr (fun s => basis_data s.2)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_CurvatureRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

def squareSum : Realizes vectorCode ratCode squareSumData := (identity ratCode).pow 2 |>.map.then sumRationals

def vectorDivide : Realizes (prodCode ratCode vectorCode) vectorCode
    (fun p => p.2.map (fun x => x/p.1)) :=
  ((second ratCode ratCode).div (first ratCode ratCode)).mapCtx

def initialScale : Realizes vectorCode vectorCode initialScaleData :=
  (((constant vectorCode ratCode 1).add squareSum).both (identity vectorCode)).then vectorDivide
def normalizeVector : Realizes (prodCode ratCode vectorCode) vectorCode normalizeData :=
  let beta := first ratCode vectorCode
  let u := (second ratCode vectorCode).then initialScale
  let ss := u.then squareSum
  ((((ss.both (beta.mul ss)).then upperSqrt).both u).then vectorDivide)

def intCeil : Realizes ratCode ratCode (fun q => (⌈q⌉ : ℚ)) :=
  (((identity ratCode).neg.then ratFloor).neg).congr (by intro q;simp [Int.floor_neg])
def nearest : Realizes ratCode ratCode (fun q => (RationalRoot.nearest q : ℚ)) :=
  let t := identity ratCode
  let half := constant ratCode ratCode (1/2)
  (((constant ratCode ratCode 0).le t).ite ((t.sub half).then intCeil)
    (((t.neg.sub half).then intCeil).neg)).congr (by
      intro q;simp only [RationalRoot.nearest,decide_eq_true_eq,id_eq];split_ifs <;> simp)
def nearestMesh : Realizes (prodCode ratCode ratCode) ratCode
    (fun p => p.1*(RationalRoot.nearest (p.2/p.1) : ℚ)) :=
  let rho := first ratCode ratCode
  rho.mul (((second ratCode ratCode).div rho).then nearest)
def roundMesh := nearestMesh.mapCtx

def cuShift : Realizes curvatureCode matrixObjectCode
    (fun p => ⟨p.n,RationalRoot.shiftedHessian p.H p.a⟩) :=
  let c (q : ℚ) := constant curvatureCode ratCode q
  let shift := ((cuH.both ((((c 7).mul cuA).both (cuN.then identityMatrix)).then matrixScale)).then matrixAdd)
  (cuN.both shift).changeOutput matrixObjectCode
    (fun p => ⟨p.n,RationalRoot.shiftedHessian p.H p.a⟩) (by
      intro p
      simp only [identityMatrix_data,matrixScale_data]
      change prodCode natCode matrixCode (p.n,
        zipDefault (zipDefault (fun z : ℚ×ℚ => z.1+z.2) 0 0) [] []
          (matrixData p.H,matrixData ((7*p.a) • (1 : Matrix (Fin p.n) (Fin p.n) ℚ))))=_
      rw [matrixAdd_data]
      rfl)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_EndpointRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def updateVector : Realizes vectorUpdateCode vectorCode updateData :=
  let p := first vectorUpdateCode natCode
  let xs := p.then (first vectorCode (prodCode natCode ratCode))
  let args := p.then (second vectorCode (prodCode natCode ratCode))
  let i := args.then (first natCode ratCode)
  let t := args.then (second natCode ratCode)
  let j := second vectorUpdateCode natCode
  let old := (j.both xs).then (getD ratCode 0)
  let one := ((j.both i).then natEq).ite t old
  (((identity vectorUpdateCode).both ((first vectorCode (prodCode natCode ratCode)).then (lengthList ratCode))).then one.tabulate).congr (by
    intro p;simp only [updateData,id_eq,decide_eq_true_eq])

def endpointEntry : Realizes (prodCode vectorCode natCode) (listCode vectorCode)
    (fun p => [updateData (p.1,(p.2,-1)),updateData (p.1,(p.2,1))]) :=
  let x := first vectorCode natCode
  let i := second vectorCode natCode
  let point (t : ℚ) := ((x.both (i.both (constant (prodCode vectorCode natCode) ratCode t))).then updateVector)
  ((point (-1)).both ((point 1).then (singleton vectorCode))).then (consList vectorCode)
def endpointCandidates : Realizes vectorCode (listCode vectorCode) endpointData :=
  ((((identity vectorCode).both ((lengthList ratCode).then range)).then endpointEntry.mapCtx).then (joinList vectorCode)).congr
    (fun _ => rfl)

def freezeScalar : Realizes (prodCode ratCode ratCode) ratCode (fun p => freezeScalarData p.1 p.2) :=
  let sigma := first ratCode ratCode
  let t := second ratCode ratCode
  let c (q : ℚ) := constant (prodCode ratCode ratCode) ratCode q
  let endpoint := (((c 0).le t).ite (c 1) (c (-1)))
  ((((c 1).sub t.abs).le sigma).ite endpoint t).congr (by
    intro p;simp only [freezeScalarData,RationalFace.nearestEndpoint,decide_eq_true_eq])
def freezeVector := freezeScalar.mapCtx

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_SelectionRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α β : Type*}

def chooseCoordinate : Realizes vectorCode natCode chooseCoordinateData :=
  let xs := first vectorCode natCode
  let i := second vectorCode natCode
  let score := (((i.both xs).then (getD ratCode 0)).abs).neg
  let all := (((identity vectorCode).both ((lengthList ratCode).then range)).then (i.both score).mapCtx)
  let initialScore := ((constant vectorCode natCode 0).both (identity vectorCode)).then (getD ratCode 0)
  let init := (constant vectorCode natCode 0).both initialScore.abs.neg
  (((init.both all).then (selectScored natCode)).then (first natCode ratCode)).congr (by
    intro xs
    change ((List.map (fun i => (i,-|xs.getD i 0|)) (List.range xs.length)).foldl
      (fun s x => betterData (s,x)) (0,-|xs.getD 0 0|)).1=_
    exact congrArg Prod.fst (selectScored_data (fun i => -|xs.getD i 0|) id (List.range xs.length) 0))
def gradientDirection : Realizes vectorCode vectorCode gradientDirectionData :=
  let x := ((chooseCoordinate.both (identity vectorCode)).then (getD ratCode 0))
  let s := (((constant vectorCode ratCode 0).le x).ite
    (constant vectorCode ratCode (-1)) (constant vectorCode ratCode 1))
  let b := (((lengthList ratCode).both chooseCoordinate).then basisVector)
  ((s.both b).then vectorScale).congr (by intro xs;simp only [gradientDirectionData,decide_eq_true_eq,id_eq])

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceChoiceRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def curvatureCandidates : Realizes (prodCode vectorCode vectorCode) (listCode vectorCode) curvatureCandidatesData :=
  let empty := ((second vectorCode vectorCode).then (lengthList ratCode)).then natIsZero
  let pair := (vectorAdd.both (vectorSub.then (singleton vectorCode))).then (consList vectorCode)
  (empty.ite (constant (prodCode vectorCode vectorCode) (listCode vectorCode) []) pair).congr (by
    intro p;simp only [curvatureCandidatesData,decide_eq_true_eq];rfl)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_FaceRunRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

def faceStart : Realizes faceCode faceCode FaceParams.start :=
  let zeros := ((constant faceCode ratCode 0).both (fBase.then (lengthList ratCode))).then (replicateList ratCode)
  let sigma := (fLam.pow 2).div fNu
  let frozen := ((sigma.both zeros).then freezeVector).congr (by
    intro p
    rw [List.length_ofFn,← List.ofFn_const]
    exact freezeVector_data _ _)
  packFace (identity faceCode) frozen

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_OriginalFieldsRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

def recordCoordinate : Realizes recordPointCode ratCode recordCoordinateData :=
  let r := (first (prodCode recordCode natCode) natCode).then (first recordCode natCode)
  let i := (first (prodCode recordCode natCode) natCode).then (second recordCode natCode)
  let j := second (prodCode recordCode natCode) natCode
  (((i.both j).then natLE).ite (recordEntry false) (((r.both j).both i).then (recordEntry true))).congr
    (by intro p;simp only [recordCoordinateData,decide_eq_true_eq])

def recordCoordinates : Realizes recordCode matrixCode recordCoordinatesData :=
  let d := first natCode vectorCode
  (((identity recordCode).both d).both d).then recordCoordinate.matrixTabulate

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_VarianceRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

def mgShift : Realizes (prodCode matrixGridCode ratCode) matrixObjectCode
    (fun p => ⟨p.1.n,p.2 • 1-p.1.M⟩) :=
  let p := first matrixGridCode ratCode
  let q := second matrixGridCode ratCode
  let M := ((q.both ((p.then mgN).then identityMatrix)).then matrixScale).both (p.then mgM) |>.then matrixSub
  ((p.then mgN).both M).changeOutput matrixObjectCode (fun p => ⟨p.1.n,p.2 • 1-p.1.M⟩) (by
    intro p
    simp only [identityMatrix_data,matrixScale_data]
    change prodCode natCode matrixCode (p.1.n,
      matrixSubData (matrixData (p.2 • (1 : Matrix (Fin p.1.n) (Fin p.1.n) ℚ)),matrixData p.1.M))=_
    rw [matrixSub_data]
    rfl)

def fVariance : Realizes faceCode matrixCode
    (fun p => matrixData (RationalSDP.rationalVariance p.coords)) :=
  let squares := fAtoms.then ((identity matrixCode).both (identity matrixCode) |>.then matrixMul).map
  let zero := ((fD.both fD).then natAdd).then zeroMatrix
  ((zero.both squares).then matrixAdd.fold).congr (by
    intro p
    change ((List.ofFn fun i => matrixData (RationalSDP.realFinDecode p.d (p.coords i))).map
      (fun M => matrixMulData (M,M))).foldl
        (fun A B => zipDefault (zipDefault (fun z : ℚ×ℚ => z.1+z.2) 0 0) [] [] (A,B))
        (matrixData (0 : Matrix (Fin (p.d+p.d)) (Fin (p.d+p.d)) ℚ))=_
    simp only [List.map_ofFn,Function.comp_def,matrixMul_data]
    rw [matrix_fold_sum]
    rfl)

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_OriginalSignRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_changeOutput _root_.OAI.CurrentKS.Realization.poly_congr _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_constant _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_identity _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reindex _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine
open scoped BigOperators

def recordTrace : Realizes recordCode ratCode recordTraceData :=
  let p := first recordCode natCode
  let i := second recordCode natCode
  let entry := ((p.both i).both i).then (recordEntry false)
  ((((identity recordCode).both (first natCode vectorCode)).then entry.tabulate).then sumRationals)

def originalTrace : Realizes (finFamilyCode originalCode Input.N) ratCode
    (fun p => RationalInput.trace p.1 p.2) :=
  (originalRecord.then recordTrace).congr (fun p => recordTrace_data p.1 p.2)
def originalTraces : Realizes originalCode vectorCode (fun x => List.ofFn (RationalInput.trace x)) :=
  originalTrace.tabulateFin originalN

def originalScale : Realizes originalCode ratCode RationalInput.scale :=
  (originalTraces.then l1Rationals).congr (by intro x;simp only [List.map_ofFn,Function.comp_def,List.sum_ofFn];rfl)
def originalOrientation : Realizes (finFamilyCode originalCode Input.N) ratCode
    (fun p => RationalInput.orientation p.1 p.2) :=
  (((constant _ ratCode 0).le originalTrace).ite (constant _ ratCode 1) (constant _ ratCode (-1))).congr
    (by intro p;simp only [RationalInput.orientation,decide_eq_true_eq])

def originalIndices : Realizes originalCode indicesCode
    (fun x => List.ofFn (fun j => (RationalInput.index x j).val)) :=
  (originalTraces.then nonzeroIndices).congr nonzeroIndices_data

def originalCountRealizes : Realizes originalCode natCode originalCount :=
  (originalIndices.then (lengthList natCode)).congr (fun _ => List.length_ofFn)

def originalIndex : Realizes (finFamilyCode originalCode originalCount) (finFamilyCode originalCode Input.N)
    (fun p => ⟨p.1,RationalInput.index p.1 p.2⟩) :=
  let x : Realizes (finFamilyCode originalCode originalCount) originalCode (fun p => p.1) := familyFirst
  let i : Realizes (finFamilyCode originalCode originalCount) natCode (fun p => p.2.val) := familyIndex
  (x.both ((i.both (x.then originalIndices)).then (getD natCode 0))).changeOutput
    (finFamilyCode originalCode Input.N) (fun p => ⟨p.1,RationalInput.index p.1 p.2⟩)
    (by intro p;rw [getD_ofFn];rfl)

def originalNormalizedMatrix : Realizes (finFamilyCode originalCode originalCount) matrixCode
    (fun p => matrixData (RationalSDP.realFinDecode p.1.d (RationalInput.normalizedCoordinates p.1 p.2))) :=
  let x : Realizes (finFamilyCode originalCode originalCount) originalCode (fun p => p.1) := familyFirst
  let scale := (constant _ ratCode 1).div (x.then originalScale)
  let orient := originalIndex.then originalOrientation
  let coord := originalIndex.then (originalRecord.then recordCoordinates)
  let normalized := ((scale.mul orient).both coord).then matrixScale
  (((x.then originalD).both normalized).then realDecode).congr (by
    intro p
    erw [recordCoordinates_data,matrixScale_data]
    change realDecodeData (p.1.d,matrixData (fun j k => (1/RationalInput.scale p.1*RationalInput.orientation p.1 (RationalInput.index p.1 p.2))*RationalInput.coordinates p.1 (RationalInput.index p.1 p.2) (j,k)))=_
    have he : (fun j k => (1/RationalInput.scale p.1*RationalInput.orientation p.1 (RationalInput.index p.1 p.2))*RationalInput.coordinates p.1 (RationalInput.index p.1 p.2) (j,k))=
        (fun j k => RationalInput.normalizedCoordinates p.1 p.2 (j,k)) := by
      funext j k
      simp only [RationalInput.normalizedCoordinates,Pi.smul_apply,smul_eq_mul,one_div,mul_assoc]
    rw [he]
    exact realDecode_data _)

def originalFaceRealizes : Realizes originalCode faceCode originalFace :=
  let atoms := originalNormalizedMatrix.tabulateFin originalCountRealizes
  let zeros := ((constant originalCode ratCode 0).both originalCountRealizes).then (replicateList ratCode)
  (originalD.both (atoms.both (zeros.both (constant originalCode (prodCode ratCode ratCode) (0,0))))).changeOutput
    faceCode originalFace (by intro x;simp only [←List.ofFn_const];rfl)

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_BinaryArithmetic
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.CurrentKS.Realization.poly_matrixView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Binary arithmetic. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

def binaryDiv (d : ℕ) : Realizes binaryNatCode binaryNatCode (fun n => n/d) :=
  (((binaryToRat.div (constant binaryNatCode ratCode d)).then ratFloor).then ratNumBinary).congr
    (fun n => by
      simp only [Rat.num_intCast,Int.floor_div_natCast,Int.floor_natCast,
        ← Int.natCast_ediv,intPayload_natCast])

def binaryMod (d : ℕ) : Realizes binaryNatCode binaryNatCode (fun n => n%d) :=
  ((binaryToRat.sub ((constant binaryNatCode ratCode d).mul
    ((binaryDiv d).then binaryToRat))).then ratNumBinary).congr (fun n => by
      have he : (n:ℚ)-(d:ℚ)*(n/d:ℕ)=(n%d:ℕ) := by
        have h := Nat.mod_add_div n d
        have hh := congrArg (fun a : ℕ => (a:ℚ)) h
        push_cast at hh
        linarith
      rw [he,Rat.num_natCast,intPayload_natCast])

def binaryModUnary (d : ℕ) : Realizes binaryNatCode natCode (fun n => n%d) :=
  (binaryMod d).then binaryToNat

def ratDenRat : Realizes ratCode ratCode (fun q => (q.den:ℚ)) := ratDenBinary.then binaryToRat

def scalarProductBinary : Realizes ratCode binaryNatCode (fun q => q.num.natAbs*q.den) :=
  ((((identity ratCode).abs.mul (ratDenRat.pow 2))).then ratNumBinary).congr (fun q => by
    have he : |q| *(q.den:ℚ)^2=(q.num.natAbs*q.den:ℕ) := by
      rw [show |q|=|(q.num:ℚ)/(q.den:ℚ)| from congrArg abs (Rat.num_div_den q).symm,
        abs_div,abs_of_pos (by positivity : (0:ℚ)<q.den)]
      push_cast
      rw [Nat.cast_natAbs,Int.cast_abs]
      field_simp
    change KS.W01.intPayload (|q| * (q.den:ℚ)^2).num=_
    rw [he,Rat.num_natCast,intPayload_natCast])

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization realization. -/

section


namespace AlgorithmicThinTrees.Normalization.Stack
open CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open Matrix

def gram : Realizes stateCode matrixCode
    (fun s => matrixData (covariance s.params.v (weights s.scales))) :=
  (((params.then dim).both
    ((scales.then ((identity ratCode).pow 2).map).both
      ((params.then columns).then outer.map))).then weightedSum).congr (by
        intro s
        change weightedSumData (s.params.d,
          ((List.ofFn s.scales).map (fun q => q^2),
            (matrixData s.params.v).map (fun xs => xs.map (fun q => xs.map (fun r => q*r)))))=_
        simp only [matrixData,List.map_ofFn,Function.comp_def]
        change weightedSumData (s.params.d,
          (List.ofFn (weights s.scales),List.ofFn (fun e => matrixData (vecMulVec (s.params.v e) (s.params.v e)))))=_
        exact weightedSum_data _ _)

def thresholdProgram : Realizes paramsCode ratCode (fun p => threshold p.q p.t) :=
  let c (q : ℚ) := constant paramsCode ratCode q
  ((c 1).div (count.then natToRat)).add
    ((c 4).mul ((c 1).sub (factor.pow 2)))

def testProgram : Realizes columnCode matrixObjectCode
    (fun x => ⟨x.1.params.d,testMatrix x.1.params.q x.1.params.t
      x.1.params.v x.1.scales x.2⟩) :=
  let firstPart := (((colParams.then thresholdProgram).both (colState.then gram)).then matrixScale)
  let secondPart := (((scale.pow 2).both (column.then outer)).then matrixScale)
  ((colParams.then dim).both ((firstPart.both secondPart).then matrixSub)).changeOutput
    matrixObjectCode (fun x => ⟨x.1.params.d,testMatrix x.1.params.q x.1.params.t
      x.1.params.v x.1.scales x.2⟩) (by
        intro x
        simp only [matrixScale_data,outer_data]
        change prodCode natCode matrixCode (x.1.params.d,
          matrixSubData
            (matrixData (threshold x.1.params.q x.1.params.t •
              covariance x.1.params.v (weights x.1.scales)),
            matrixData ((x.1.scales x.2)^2 • vecMulVec (x.1.params.v x.2) (x.1.params.v x.2))))=_
        rw [matrixSub_data]
        rfl)

def updated : Realizes columnCode vectorCode
    (fun x => List.ofFn (Function.update x.1.scales x.2 (x.1.params.t*x.1.scales x.2))) :=
  (((colState.then scales).both (colIndex.both ((colParams.then factor).mul scale))).then
    updateVector).congr (fun _ => update_data _ _ _)

def multiplierProgram : Realizes natCode ratCode multiplier :=
  let c (q : ℚ) := constant natCode ratCode q
  (c 1).sub ((c 1).div ((c 16).mul (natToRat.pow 2)))
def fixedStep : Realizes fixedCode paramsCode fixedStepParams :=
  ((fixedParams.then dim).both ((fixedParams.then count).both
    ((fixedR.then multiplierProgram).both (fixedParams.then columns)))).changeOutput
      paramsCode fixedStepParams (fun _ => rfl)

end AlgorithmicThinTrees.Normalization.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_MatrixRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix realization. -/

section


namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
variable {ι α β : Type*} {L : ι → ℕ} {ea : α → Word} {eb : β → Word}

def schurEntry : Realizes entryCode ratCode
    (fun p =>
      let A := matrixData p.1.1.2
      (A.getD (p.1.2+1) []).getD (p.2+1) 0 -
        (A.getD (p.1.2+1) []).getD 0 0 * (A.getD 0 []).getD (p.2+1) 0 /
          (A.getD 0 []).getD 0 0) :=
  let A := entryBase.then matrixEntries
  let i := entryI.then natSucc
  let j := entryJ.then natSucc
  let z := constant entryCode natCode 0
  let e {f g : (MatrixObject×ℕ)×ℕ → ℕ}
      (k : Realizes entryCode natCode f) (l : Realizes entryCode natCode g) :=
    (A.both (k.both l)).then matrixEntry
  (e i j).sub (((e i z).mul (e z j)).div (e z z))

def schur : Realizes matrixObjectCode matrixObjectCode schurData :=
  let d := matrixDim.then natPred
  let B := (((identity matrixObjectCode).both d).both d).then schurEntry.matrixTabulate
  (d.both B).changeOutput matrixObjectCode schurData (by
    intro a
    rcases a with ⟨n,A⟩
    cases n with
    | zero => simp [matrixObjectCode,schurData,matrixData]
    | succ n =>
      change prodCode natCode matrixCode (n,
        (List.range n).map (fun i => (List.range n).map (fun j => _)))=_
      simp only [range_map_fin, id_eq]
      have he : (List.ofFn fun (i : Fin n) => List.ofFn fun (j : Fin n) =>
          ((matrixData A).getD (i.val+1) []).getD (j.val+1) 0 -
            ((matrixData A).getD (i.val+1) []).getD 0 0 *
            ((matrixData A).getD 0 []).getD (j.val+1) 0 /
            ((matrixData A).getD 0 []).getD 0 0)=matrixData (KS.W17.schurTail A) := by
        change List.ofFn _=List.ofFn _
        apply congrArg List.ofFn
        funext i
        apply congrArg List.ofFn
        funext j
        change ((matrixData A).getD i.succ.val []).getD j.succ.val 0 -
          ((matrixData A).getD i.succ.val []).getD (0 : Fin (n+1)).val 0 *
          ((matrixData A).getD (0 : Fin (n+1)).val []).getD j.succ.val 0 /
          ((matrixData A).getD (0 : Fin (n+1)).val []).getD (0 : Fin (n+1)).val 0 = _
        rw [matrix_entry_data A i.succ j.succ,matrix_entry_data A i.succ 0,
          matrix_entry_data A 0 j.succ,matrix_entry_data A 0 0]
        rfl
      rw [he]
      rfl)

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_SchurHistory
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Schur history. -/

section


namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
open AlgorithmicThinTrees

def schurNext : Realizes schurStackCode schurStackCode schurNextData :=
  let z := ((schurCurrent.then matrixDim).both (constant schurStackCode natCode 0)).then natEq
  (z.ite (identity schurStackCode)
    ((schurCurrent.then schur).both ((schurCurrent.both schurOld).then (consList matrixObjectCode)))).congr
    (fun s => by simp only [schurNextData]; split_ifs <;> simp_all)

def schurHistory : Realizes matrixObjectCode (listCode matrixObjectCode) schurHistoryData :=
  (((matrixDim.both ((identity matrixObjectCode).both
    (constant matrixObjectCode (listCode matrixObjectCode) []))).then schurNext.iterate).then
      schurOld).congr (fun a => by simpa only [List.append_nil,id_eq] using schurHistory_iterate a [])

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_BoolPrograms
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bool programs. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23
variable {α : Type*} {ea : α → Word}

def anyTrue : Realizes boolsCode boolCode (fun bs => decide (true ∈ bs)) :=
  ((constant boolsCode natCode 0).nlt
    ((((constant boolsCode boolCode false).both (identity boolsCode)).then
      (second boolCode boolCode).filterCtx).then (lengthList boolCode))).congr (by
      intro bs
      simp [List.length_pos_iff, List.filter_eq_nil_iff, Bool.forall_bool])

def allTrue : Realizes boolsCode boolCode (fun bs => decide (∀b∈bs,b=true)) :=
  (((identity boolCode).ite (constant boolCode boolCode false)
    (constant boolCode boolCode true)).map.then anyTrue).not.congr (by
      intro bs
      simp)

variable {n : α → ℕ} {P : (a : α) → Fin (n a) → Prop} [∀a,DecidablePred (P a)]
def Realizes.existsFin
    (r : Realizes (finFamilyCode ea n) boolCode (fun p => decide (P p.1 p.2)))
    (rn : Realizes ea natCode n) : Realizes ea boolCode (fun a => decide (∃i,P a i)) :=
  ((r.tabulateFin rn).then anyTrue).congr (by
    intro a;simp only [List.mem_ofFn,decide_eq_true_eq])

def Realizes.forallFin
    (r : Realizes (finFamilyCode ea n) boolCode (fun p => decide (P p.1 p.2)))
    (rn : Realizes ea natCode n) : Realizes ea boolCode (fun a => decide (∀i,P a i)) :=
  ((r.tabulateFin rn).then allTrue).congr (by
    intro a;simp only [List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,decide_eq_true_eq])

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_ScalarRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 AlgorithmicThinTrees.RationalGram

def squareScan : Realizes squareScanCode squareScanCode squareScanStep :=
  (squarePayload.then (binaryDiv 4)).both
    (((constant squareScanCode ratCode 2).mul squarePower).both
      ((squareAccum.both ((squarePower.both (squarePayload.then (binaryModUnary 4))).then
        (replicateList ratCode))).then (appendList ratCode)))

def scalarFactorProgram : Realizes ratCode vectorCode scalarFactors :=
  let n := scalarProductBinary
  let a := (constant ratCode ratCode 1).div ratDenRat
  let start := n.both (a.both (constant ratCode vectorCode []))
  ((((n.then binarySize).both start).then squareScan.iterate).then squareAccum).congr (fun q => by
    rw [squareScan_correct]
    simp only [List.nil_append,scalarFactors]
    apply List.map_congr_left
    intro x hx
    ring)

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_SearchRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Search realization. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

def gridStep := graphRadius.div ((graphDim.then natToRat).add (constant graphCode ratCode 1))

def gridMesh := (gridStep.pow 2).div
  (((constant graphCode ratCode 16).mul ((graphDim.then natToRat).add (constant graphCode ratCode 1))).mul
    ((graphBound.add gridStep).add (constant graphCode ratCode 1)))
end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_BitBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation bit bound. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack

abbrev coefficients :=
  let t := extractionGraph.then graphStep
  ((constant extractionInputCode ratCode 1).add t).cons
    (((constant extractionInputCode ratCode 1).sub t).cons
      (((((constant extractionInputCode ratCode 2).mul (extractionCount.then gainProgram)).mul
        (extractionCount.then natToRat)).mul t).cons
          (t.cons ((extractionGraph.then graphBaseline).then (singleton ratCode)))))

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_InverseRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverse realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
open AlgorithmicThinTrees

def solveRhs : Realizes rhsCode ratCode
    (fun p =>
      (if p.2+1=p.1.2 then 1 else 0)-
        ((matrixData p.1.1.2.2).getD (p.2+1) []).getD 0 0 *
          ((if 0=p.1.2 then 1 else 0)/((matrixData p.1.1.2.2).getD 0 []).getD 0 0)) :=
  let A := rhsBase.then solveColumnEntries
  let i := rhsIndex.then natSucc
  let j := rhsBase.then solveColumnIndex
  let zero := constant rhsCode natCode 0
  let ij := (i.both j).then identityEntry
  let zj := (zero.both j).then identityEntry
  let iz := (A.both (i.both zero)).then matrixEntry
  let zz := (A.both (zero.both zero)).then matrixEntry
  ij.sub (iz.mul (zj.div zz))

def liftColumn : Realizes solveColumnCode vectorCode liftColumnData :=
  let n := solveColumnDim.then natPred
  let args := (identity solveColumnCode).both n
  let y := (solveColumnB.both (args.then solveRhs.tabulate)).then matVec
  let row := args.then solveTopRow.tabulate
  let zero := constant solveColumnCode natCode 0
  let b := (zero.both solveColumnIndex).then identityEntry
  let pivot := (solveColumnEntries.both (zero.both zero)).then matrixEntry
  (((b.sub ((row.both y).then dot)).div pivot).both y).then (consList ratCode)

def inverseLift : Realizes backSolveCode matrixCode inverseLiftData :=
  (((identity backSolveCode).both (solveParent.then matrixDim)).then liftColumn.tabulate).then transposeMatrix

def rationalInverseProgram : Realizes matrixObjectCode matrixObjectCode
    (fun a => ⟨a.1,RationalInverse.inverse a.1 a.2⟩) :=
  (matrixDim.both (((constant matrixObjectCode matrixCode []).both schurHistory).then inverseLift.fold)).changeOutput
    matrixObjectCode (fun a => ⟨a.1,RationalInverse.inverse a.1 a.2⟩)
    (fun a => by rw [inverse_fold_correct];rfl)

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_GramRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix AlgorithmicThinTrees

def gramLift : Realizes gramLiftCode matrixCode gramLiftData :=
  let A := gramParent.then matrixEntries
  let z := constant gramLiftCode natCode 0
  let pivot := (A.both (z.both z)).then matrixEntry
  let factors := (((constant gramLiftCode ratCode 1).div pivot).then scalarFactorProgram)
  let scale := ((second vectorCode ratCode).both (first vectorCode ratCode)).then vectorScale
  let cap := ((A.then firstColumn).both factors).then scale.mapCtx
  let lift := ((constant vectorCode ratCode 0).both (identity vectorCode)).then (consList ratCode)
  ((cap.both (gramChild.then lift.map)).then (appendList vectorCode)).congr
    (fun _ => by simp only [gramLiftData,one_div,id_eq])

def gramColumnsProgram : Realizes matrixObjectCode matrixCode
    (fun a => (RationalGram.factorColumns a.1 a.2).map List.ofFn) :=
  (((constant matrixObjectCode matrixCode []).both schurHistory).then gramLift.fold).congr
    gram_fold_correct

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signing realization. -/

section

namespace AlgorithmicThinTrees.Signing.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix

def outerFields : Realizes vectorCode vectorCode
    (fun xs : List ℚ => (xs.map (fun q =>
      (xs.map (fun r => [q*r,0])).flatten)).flatten) :=
  ((Normalization.Stack.outer.then complexField.map.map).then (joinList vectorCode)).then
    (joinList ratCode) |>.congr (by
      intro xs
      simp only [List.map_map,Function.comp_def,List.flatten_flatten])

def signerInput : Realizes frameCode originalCode (fun a => RationalSigning.input a.v) :=
  (frameDim.both (frameRows.then outerFields.map)).changeOutput originalCode
    (fun a => RationalSigning.input a.v) (by
      intro a
      change frameDataCode (a.d,_) = originalDataCode (originalData _)
      congr 1
      change (a.d,_)=(a.d,List.ofFn (fieldValues (RationalSigning.input a.v)))
      apply congrArg (fun xs => (a.d,xs))
      change (matrixData a.v).map _ = _
      change (List.ofFn (fun e => List.ofFn (a.v e))).map _ = _
      rw [List.map_ofFn]
      exact congrArg List.ofFn (funext (outerFields_data a.v)))

def factorRows : Realizes matrixObjectCode matrixCode
    (fun a => matrixData (GramWhitening.rationalFactor a.2)ᵀ) :=
  (rationalInverseProgram.then gramColumnsProgram).congr
    (fun a => factorColumns_data ⟨a.1,RationalInverse.inverse a.1 a.2⟩)

def whiten : Realizes formCode frameCode FormFrame.whiten :=
  let R := formMatrix.then factorRows
  let cols := (R.both formRows).then matVec.mapCtx
  ((R.then (lengthList vectorCode)).both cols).changeOutput frameCode FormFrame.whiten (by
    intro a
    change frameDataCode (_,_) = frameDataCode (Frame.data _)
    congr 1
    dsimp only [FormFrame.data,Frame.data,FormFrame.whiten]
    refine Prod.ext (List.length_ofFn) ?_
    change List.map _ (List.ofFn (fun e => List.ofFn (a.v e)))=matrixData _
    rw [List.map_ofFn]
    simp only [Function.comp_def,matVec_data]
    rfl)

def whitenPair : Realizes formsCode pairCode FormPair.whiten :=
  ((formsLeft.then whiten).both (formsRight.then whiten)).changeOutput
    pairCode FormPair.whiten (fun _ => rfl)

end AlgorithmicThinTrees.Signing.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_Realization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparsification realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

def ratNatFloorBinary : Realizes ratCode binaryNatCode (fun q => ⌊q⌋₊) :=
  ((((constant ratCode ratCode 0).max (identity ratCode)).then ratFloor).then
    ratNumBinary).congr (by
      intro q
      have he : (⌊max 0 q⌋ : ℤ)=(⌊q⌋₊ : ℤ) := by
        by_cases hq : 0 ≤ q
        · rw [max_eq_right hq,Int.natCast_floor_eq_floor hq]
        · rw [max_eq_left (le_of_not_ge hq),Int.floor_zero,Nat.floor_eq_zero.mpr (by linarith)]
          rfl
      change KS.W01.intPayload ⌊max 0 q⌋=⌊q⌋₊
      rw [he,intPayload_natCast])

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_GreedyRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Greedy realization. -/

section

namespace AlgorithmicThinTrees.GreedyTree.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Finset StrongThinTree
open GraphStack

def incident : Realizes arcCode boolCode (fun a => decide
    (a.2 ∈ a.1.1.subgraph.A ∧
      ((a.1.1.subgraph.graph.G.left a.2=a.1.2 ∧ a.1.1.subgraph.graph.G.right a.2 ∈ a.1.1.U) ∨
       (a.1.1.subgraph.graph.G.right a.2=a.1.2 ∧ a.1.1.subgraph.graph.G.left a.2 ∈ a.1.1.U)))) :=
  (arcSubedge.then selected).and
    (((arcLeft.finEq (arcVertex.then vertexIndex)).and rightReached).or
      ((arcRight.finEq (arcVertex.then vertexIndex)).and leftReached))

def expands : Realizes vertexCode boolCode
    (fun v => decide (v.2 ∈ expand v.1.subgraph.graph.G v.1.subgraph.A v.1.U)) :=
  (reached.or (incident.existsFin (P:=fun a e => e ∈ a.1.subgraph.A ∧
    ((a.1.subgraph.graph.G.left e=a.2 ∧ a.1.subgraph.graph.G.right e ∈ a.1.U) ∨
     (a.1.subgraph.graph.G.right e=a.2 ∧ a.1.subgraph.graph.G.left e ∈ a.1.U)))
    (vertexContext.then reachM))).congr (by
    intro v
    congr 1
    apply propext
    simp only [expand,mem_union,mem_image,mem_filter]
    constructor
    · rintro (h|⟨e,he,h|h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨e,⟨he,h.2⟩,h.1⟩)
      · exact Or.inr ⟨e,⟨he,h.2⟩,h.1⟩
    · rintro ((h|⟨e,⟨he,hu⟩,hv⟩)|⟨e,⟨he,hu⟩,hv⟩)
      · exact Or.inl h
      · exact Or.inr ⟨e,he,Or.inl ⟨hv,hu⟩⟩
      · exact Or.inr ⟨e,he,Or.inr ⟨hv,hu⟩⟩)
def next : Realizes reachCode reachCode ReachState.next :=
  (reachSubgraph.both (expands.tabulateFin reachN)).changeOutput reachCode ReachState.next (fun _ => rfl)
def initBit : Realizes initVertexCode boolCode (fun p => decide (p.2.val=0)) :=
  (familyIndex.neq (constant initVertexCode natCode 0))
def start : Realizes subgraphCode reachCode Subgraph.start :=
  ((identity subgraphCode).both (initBit.tabulateFin subgraphN)).changeOutput reachCode Subgraph.start (by
    intro s
    change prodCode subgraphCode boolsCode (s,List.ofFn (fun v : Fin s.graph.n => decide (v.val=0)))=_
    simp +instances only [reachCode,Subgraph.start,ReachState.bits,mem_filter,mem_univ,true_and])
def walk : Realizes subgraphCode reachCode Walk := (subgraphN.both start).then next.iterate

def reachedAll : Realizes reachCode boolCode (fun s => decide (s.U=univ)) :=
  (reached.forallFin (P:=fun s v => v ∈ s.U) reachN).congr (by intro s;simp only [Finset.eq_univ_iff_forall])

def connectedProgram : Realizes subgraphCode boolCode (fun s => connected s.graph.G s.A) :=
  (walk.then reachedAll).congr (by
    intro s
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq,connected_correct] using walk_connected s)

def eraseBit : Realizes eraseEdgeCode boolCode
    (fun p => decide (p.2 ∈ p.1.1.A ∧ p.2.val ≠ p.1.2)) :=
  (eraseSubedge.then selected).and ((eraseEdgeIndex.neq (eraseEdgeContext.then eraseIndex)).not)
def eraseProgram : Realizes eraseInputCode subgraphCode erase :=
  ((eraseContext.then subgraphGraph).both
    (eraseBit.tabulateFin (eraseContext.then subgraphM))).changeOutput subgraphCode erase (by
      intro p
      simp +instances only [subgraphCode,Subgraph.bits,erase,mem_filter])

def deleteProgram : Realizes eraseInputCode subgraphCode deleteAt :=
  (eraseProgram.then connectedProgram).ite eraseProgram eraseContext

def treeProgram : Realizes graphCode boolsCode (fun g => List.ofFn (fun e => decide (e ∈ tree g.G))) :=
  ((((whole.both (numEdges.then range)).then deleteProgram.fold).then subgraphBits)).congr (by
    intro g
    have he : List.range g.m=(List.finRange g.m).map Fin.val := by simp
    change Subgraph.bits ((List.range g.m).foldl (fun s i => deleteAt (s,i)) ⟨g,univ⟩)=_
    rw [he,fold_deletes]
    rfl)

end AlgorithmicThinTrees.GreedyTree.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_WordHead
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Word head. -/

section

namespace CurrentKS.WordHead
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open CleanRoutine PairRoutine

lemma flag_spec (w : Word) : RunSpec flag (io w) (smallState w [w.headD false] []) 1 := by
  intro bits hbits
  obtain ⟨coin,rfl⟩ := List.length_eq_one_iff.mp hbits
  change (compile (0 : Fin 1) 0 1 dispatch).step ⟨some (0 : Fin 1),io w⟩ coin=_
  rw [step_compile]
  apply KS.W19.FixedRun.config_ext
  · rfl
  · intro j
    fin_cases j <;> simp [dispatch,KS.W01.FixedStack.Instruction.action,KS.W29.StackAction.apply,
      io,smallState,observedHeads]
    cases w with
    | nil => rfl
    | cons b bs => cases b <;> rfl

def routine : Routine (fun w : Word => w) (fun w => [w.headD false]) (fun w => w.length+6) where
  scratch := 2
  program := program
  spec w := by
    have h := (flag_spec w).compose ((PairRoutine.clear_first [w.headD false] w).compose
      (PairRoutine.take_first [w.headD false]))
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | ((try rfl))
    simp
    omega
end CurrentKS.WordHead

namespace CurrentKS.Realization
open CleanRoutine KS.W23
def wordHead : Realizes wordCode boolCode (fun w => w.headD false) where
  cost := fun w => w.length+6
  routine := WordHead.routine
instance poly_wordHead : PolyTime wordHead := ⟨⟨NaturalPolynomial.variable+6,fun _ => le_rfl⟩⟩
end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputExpansion
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input expansion. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack GraphStack

def bCountBinary : Realizes bRecCode binaryNatCode (fun x => x.1.val.reduced.multiplicity x.2) :=
  let k := brInput.then bKBinary |>.then binaryToRat
  let n := brInput.then bNBinary |>.then binaryToRat
  let c := bMultiplicityRat
  let capped := (c.le k).ite c k
  ((((constant bRecCode ratCode 2).mul (n.pow 2)).mul capped).div k |>.then ratNatFloorBinary)
    |>.congr (by
      intro x
      have he : (if decide ((x.1.val.multiplicity x.2:ℚ)≤(x.1.val.k:ℚ))
          then (x.1.val.multiplicity x.2:ℚ) else (x.1.val.k:ℚ)) =
          (min (x.1.val.multiplicity x.2) x.1.val.k:ℕ) := by
        simp only [Nat.cast_le,decide_eq_true_eq]
        split_ifs with h
        · rw [min_eq_left h]
        · rw [min_eq_right (le_of_not_ge h)]
      change ⌊2*(x.1.val.n:ℚ)^2*(if decide _ then _ else _)/(x.1.val.k:ℚ)⌋₊ = _
      have hex : (2:ℚ)*(x.1.val.n:ℚ)^2*(min (x.1.val.multiplicity x.2) x.1.val.k:ℕ) =
          (2*x.1.val.n^2*min (x.1.val.multiplicity x.2) x.1.val.k:ℕ) := by push_cast; rfl
      rw [he,hex,Nat.floor_div_natCast,Nat.floor_natCast])

def bCount := bCountBinary.then binaryToNat

def bEndpointBlock (right : Bool) : Realizes bRecCode (listCode natCode)
    (fun x => List.replicate (x.1.val.reduced.multiplicity x.2)
      (if right then (x.1.val.right x.2).val else (x.1.val.left x.2).val)) :=
  ((bEndpoint right).both bCount).then (replicateList natCode)

def bLefts : Realizes bCode (listCode natCode)
    (fun x => List.ofFn (fun e => (x.val.reduced.expanded.left e).val)) :=
  (((bEndpointBlock false).tabulateFin bP).then (joinList natCode)).congr
    (fun x => x.val.reduced.expanded_lefts.symm)
def bRights : Realizes bCode (listCode natCode)
    (fun x => List.ofFn (fun e => (x.val.reduced.expanded.right e).val)) :=
  (((bEndpointBlock true).tabulateFin bP).then (joinList natCode)).congr
    (fun x => x.val.reduced.expanded_rights.symm)
def bRecords : Realizes bCode (listCode natCode)
    (fun x => List.ofFn (fun e : Fin x.val.reduced.copies.length =>
      (x.val.reduced.copies.get e).1.val)) :=
  ((((brIndex.both bCount).then (replicateList natCode)).tabulateFin bP).then
    (joinList natCode)).congr (fun x => x.val.reduced.expanded_records.symm)

def bPrepare : Realizes bCode problemCode bProblem :=
  ((bN.both (bLefts.both bRights)).both (bN.nmul bN)).changeOutput problemCode bProblem (by
    intro x
    rw [makeProblem_code]
    simp only [pow_two]
    rfl)

end AlgorithmicThinTrees.InputStack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_IterationRealization
attribute [-instance] _root_.OAI.CurrentKS.Realization.poly_wordHead
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iteration realization. -/

section

namespace AlgorithmicThinTrees.Iteration.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 StrongThinTree Finset
open GraphStack GraphicHalf GraphicHalf.Stack MetricTests.RationalStep MetricTests.RationalStep.Stack OrderedGraph

def nextCountBinary : Realizes natCode binaryNatCode nextCount :=
  ((((constant natCode ratCode 1).sub ((constant natCode ratCode 16).mul
    ((constant natCode ratCode 1).div ((unaryRoot 16 (by decide)).then natToRat)))).mul natToRat).div
      (constant natCode ratCode 2)).then ratNatFloorBinary

def nextCountProgram : Realizes natCode natCode nextCount := nextCountBinary.then binaryToNat

def selectState : Realizes (prodCode stateCode boolsCode) stateCode
    (fun p => p.1.restrict (univ.filter (fun e => p.2.getD e.val false))) := by
  let a := first stateCode boolsCode
  let b := second stateCode boolsCode

  let entry : Realizes (prodCode (prodCode stateCode boolsCode) natCode) boolCode
      (fun q => q.1.2.getD q.2 false) :=
    ((second (prodCode stateCode boolsCode) natCode).both
      ((first (prodCode stateCode boolsCode) natCode).then b)).then (getD boolCode false)
  let bits := (((identity (prodCode stateCode boolsCode)).both
    (a.then graph |>.then numEdges)).then entry.tabulate)
  let ls := (bits.both (a.then graph |>.then lefts)).then (maskArray natCode 0)
  let rs := (bits.both (a.then graph |>.then rights)).then (maskArray natCode 0)
  let labs := (bits.both (a.then labels)).then (maskArray natCode 0)
  let gg := (a.then graph |>.then numVertices).both (ls.both rs)
  exact ((gg.both (a.then count |>.then nextCountProgram)).both labs).changeOutput stateCode
    (fun p => p.1.restrict (univ.filter (fun e => p.2.getD e.val false))) (by
      intro p
      let A := univ.filter (fun e : Fin p.1.problem.m => p.2.getD e.val false)
      have hb : (List.range p.1.problem.m).map (fun i => p.2.getD i false)=
          List.ofFn (fun e => decide (e ∈ A)) := by
        rw [range_map_fin]
        simp [A]
      change prodCode (prodCode graphDataCode natCode) indicesCode
        ((_,_),_) = _
      dsimp only [id,Problem.graph,Graph.data]
      rw [hb,maskArray_data,maskArray_data,maskArray_data]
      rfl)

def large (R : ℕ) : Realizes stateCode boolCode (fun s => decide (R ≤ s.problem.r)) :=
  ((constant stateCode natCode R).both count).then natLE
def finish : Realizes stateCode indicesCode finishData :=
  ((((graph.then GreedyTree.Stack.treeProgram).both labels).then (maskArray natCode 0))).congr
    (fun s => maskArray_data _ s.labels 0)

end AlgorithmicThinTrees.Iteration.Stack

namespace AlgorithmicThinTrees.Iteration.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 StrongThinTree Finset
open GraphStack GraphicHalf GraphicHalf.Stack MetricTests.RationalStep OrderedGraph

def initialCountProgram : Realizes natCode natCode initialCount :=
  let h := (identity natCode).ndiv (constant natCode natCode 2)
  (((constant natCode natCode 1).nlt h).ite h (constant natCode natCode 1)).congr (by
    intro k
    simp only [decide_eq_true_eq,initialCount,id_eq]
    split_ifs with hh
    · exact (max_eq_right (by omega)).symm
    · exact (max_eq_left (by omega)).symm)
def startProgram : Realizes problemCode (prodCode natCode stateCode) start :=
  let r := problemCount.then initialCountProgram
  let lab := problemM.then CurrentKS.Realization.range
  (r.both ((problemGraph.both r).both lab)).changeOutput
    (prodCode natCode stateCode) start (by
      intro p
      change prodCode natCode (prodCode (prodCode graphCode natCode) indicesCode)
        (_,(_,List.range p.m))=_
      have he : List.range p.m=List.ofFn (fun e : Fin p.m => e.val) := by
        simpa only [List.map_id, id_eq] using (range_map_fin (n:=p.m) (f:=id))
      rw [he]
      rfl)

end AlgorithmicThinTrees.Iteration.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_InputDispatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Input dispatch. -/

section

namespace AlgorithmicThinTrees.InputStack
open StrongThinTree Finset CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open GraphicHalf.Stack

def formatTest : Realizes largeCode boolCode (fun x => decide (isBinary x.val=true)) :=
  (wordHead.reindex largeCode largeCode (fun _ => rfl)).congr (by
    rintro ⟨x|x,h⟩ <;> rfl)
instance poly_formatTest : PolyTime formatTest := by unfold formatTest;infer_instance

end AlgorithmicThinTrees.InputStack
end

end OAI
end


