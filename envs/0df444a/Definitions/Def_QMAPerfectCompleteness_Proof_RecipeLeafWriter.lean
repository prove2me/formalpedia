-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RecipeLeafWriter
-- name    : QMAPerfectCompleteness_Proof_RecipeLeafWriter
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:16:17.056952+00:00
-- url     : https://prove2.me/theorems/e886fd03-d83f-4ccf-910a-f5d9fe94bafb
-- title:
--   Serialization of literal recipe instructions
-- statement:
--   Defines writer primitives for expression-valued unary wire fields and literal gate templates. The evaluated tag and address fields are appended to the reversed output buffer using the shared recipe context.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RecipeLeafWriter.lean, retained declaration span lines 8–30.

/- Generated from Solutions.RecipeLeafWriter by authoritative Stage-2 skeleton subtraction.
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



/-! Serialize the literal gate templates in a circuit recipe using checked unary evaluators. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CircuitRecipe
open QMAPerfectCompleteness.Uniformity.StructuredStack

abbrev readInputs {d : ℕ} : Inputs d ↪ ReadOnly d := Function.Embedding.inl

noncomputable def fieldWriter (d : ℕ) (e : Expr) :
    RecipeWriter d (fun x=>QAlgorithms.Complexity.encNat (e.eval (inputEnvironment x.values) (inputContext x.values))) := by
  let W := (Writer.field (e.evaluator d)).adapt Context.encode Context.Valid readInputs
    Context.values Polynomial.X (by intro x a; rfl)
    (by intro x B hx; simpa using hx.1)
  apply W.congr
  intro x B hx
  simp only [Expr.value,inputAddress,hx.2.1]

noncomputable def wireFieldsWriter (d : ℕ) (wires : List Expr) :
    RecipeWriter d (fun x=>wires.flatMap (fun e=>QAlgorithms.Complexity.encNat
      (e.eval (inputEnvironment x.values) (inputContext x.values)))) :=
  match wires with
  | [] => Writer.empty
  | e::es => (fieldWriter d e).append (wireFieldsWriter d es)

noncomputable def gateWriter (d : ℕ) (tag : ℕ) (wires : List Expr) :
    RecipeWriter d (fun x=>((Recipe.emit tag wires).eval (inputEnvironment x.values)
      (inputContext x.values) x.source).flatMap RawEncoding.Instruction.encode) := by
  simpa [Recipe.eval,RawEncoding.Instruction.encode,List.flatMap_map,Function.comp_def] using
    (Writer.literal (QAlgorithms.Complexity.encNat tag)).append (wireFieldsWriter d wires)

end QMAPerfectCompleteness.Main.CircuitRecipe


