-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CircuitProvisionalWriter
-- name    : QMAPerfectCompleteness_Proof_CircuitProvisionalWriter
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:21:44.535013+00:00
-- url     : https://prove2.me/theorems/5542c152-3695-4273-92a0-46bdcc1116f7
-- title:
--   Verifier serialization with a count placeholder
-- statement:
--   Defines the provisional verifier encoding and its finite writer: register sizes and output address precede the generated gate body, with a placeholder gate count. A separate recounting pass replaces that placeholder after the body has been emitted.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CircuitProvisionalWriter.lean, retained declaration span lines 10–24.

/- Generated from Solutions.CircuitProvisionalWriter by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_BoundedWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitExprTM
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ConditionalWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_CountedWriterLoops
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeCompositeWriters
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeLeafWriter
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeNormalization
import Definitions.Def_QMAPerfectCompleteness_Proof_RecipeWriterContext
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_StackEmbedding
import Definitions.Def_QMAPerfectCompleteness_Proof_StackTransfers
import Definitions.Def_QMAPerfectCompleteness_Proof_StreamWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryEvaluator
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryStackOps
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Generate the complete verifier header and body with a zero count placeholder. A final
finite parser counts the emitted gates and replaces this one field. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CircuitRecipe
open QMAPerfectCompleteness.Uniformity.StructuredStack
open QAlgorithms.Complexity (encNat)

abbrev Circuit.provisionalCode (C : Circuit) (x : Context 0) : List Bool :=
  encNat (C.proofQubits.eval (inputEnvironment x.values) []) ++
  encNat (C.ancillaQubits.eval (inputEnvironment x.values) []) ++
  encNat (C.output.eval (inputEnvironment x.values) []) ++ encNat 0 ++ C.gates.codeAt x

/-- A literal finite writer for the entire provisional circuit encoding, including all headers. -/
noncomputable def Circuit.provisionalWriter (source : SourceWriters) (C : Circuit) :
    RecipeWriter 0 C.provisionalCode := by
  let H := Writer.append (fieldWriter 0 C.proofQubits)
    (Writer.append (fieldWriter 0 C.ancillaQubits)
      (Writer.append (fieldWriter 0 C.output) (Writer.literal (encNat 0))))
  let W := Writer.append H (C.gates.compiledWriter source 0)
  apply W.congr
  intro x B hx
  simp only [Circuit.provisionalCode,inputContext,List.ofFn_zero,List.append_assoc]

end QMAPerfectCompleteness.Main.CircuitRecipe


