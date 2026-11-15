-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_SourceWriterBounds
-- name    : QMAPerfectCompleteness_Proof_SourceWriterBounds
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:20:15.087208+00:00
-- url     : https://prove2.me/theorems/b66f8066-ed86-49be-920e-ba493f1e4bce
-- title:
--   Size bounds for unary source traversal
-- statement:
--   Provides the retained inequalities bounding source wire addresses and instruction counts by encoded byte length. Instruction-order reversal preserves that length, and the per-instruction bound controls the size of an expression-remapped source body.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/SourceWriterBounds.lean, retained declaration span lines 7–72.

/- Generated from Solutions.SourceWriterBounds by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_SourceInstructionMapper
import Definitions.Def_QMAPerfectCompleteness_Proof_SourceWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_StackEmbedding
import Definitions.Def_QMAPerfectCompleteness_Proof_StackTransfers
import Definitions.Def_QMAPerfectCompleteness_Proof_StreamWriterTM
import Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryDispatch
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryEvaluator
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryFieldCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryStackOps
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Unary source-code width and mapped-output bounds used by the concrete source writer. -/
namespace QMAPerfectCompleteness.Main.CircuitRecipe.SourceTM
open QAlgorithms.Complexity (Str encNat)

lemma instruction_code_pos (i : RawEncoding.Instruction) : 0 < i.encode.length := by
  simp only [RawEncoding.Instruction.encode,List.length_append,Main.Encoding.encNat_length]
  omega

lemma wire_le_instruction_length (i : RawEncoding.Instruction) (w : ℕ) (hw : w∈i.wires) :
    w ≤ i.encode.length := by
  have aux : ∀ ws : List ℕ,w∈ws → w+1≤(ws.flatMap encNat).length := by
    intro ws
    induction ws with
    | nil => simp
    | cons v ws ih =>
      intro h
      rcases List.mem_cons.mp h with rfl|h
      · simp only [List.flatMap_cons,List.length_append,Main.Encoding.encNat_length]
        omega
      · have ht := ih h
        simp only [List.flatMap_cons,List.length_append,Main.Encoding.encNat_length]
        omega
  have h := aux i.wires hw
  simp only [RawEncoding.Instruction.encode,List.length_append,Main.Encoding.encNat_length]
  omega

lemma instruction_length_le_source (is : List RawEncoding.Instruction) (i : RawEncoding.Instruction) (hi : i∈is) :
    i.encode.length≤(is.flatMap RawEncoding.Instruction.encode).length := by
  induction is with
  | nil => simp at hi
  | cons j js ih =>
    rcases List.mem_cons.mp hi with rfl|hi
    · simp only [List.flatMap_cons,List.length_append]; omega
    · have h := ih hi
      simp only [List.flatMap_cons,List.length_append]
      omega

lemma source_wire_le_length (is : List RawEncoding.Instruction) :
    ∀ i∈is,∀ w∈i.wires,w≤(is.flatMap RawEncoding.Instruction.encode).length := by
  intro i hi w hw
  exact (wire_le_instruction_length i w hw).trans (instruction_length_le_source is i hi)

lemma source_count_le_length (is : List RawEncoding.Instruction) :
    is.length≤(is.flatMap RawEncoding.Instruction.encode).length := by
  induction is with
  | nil => simp
  | cons i is ih =>
    have h := instruction_code_pos i
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

lemma source_reverse_length (is : List RawEncoding.Instruction) :
    (is.reverse.flatMap RawEncoding.Instruction.encode).length =
      (is.flatMap RawEncoding.Instruction.encode).length := by
  simp only [List.length_flatMap,List.map_reverse,List.sum_reverse]

lemma mapped_source_length_le (e : Expr) (d : ℕ) (x : Context d) (B : ℕ) (hx : x.Valid B)
    (is : List RawEncoding.Instruction) (hvalid : Context.SourceValid is)
    (hwire : ∀ i∈is,∀ w∈i.wires,w≤B) :
    ((is.map (mappedInstruction e x)).flatMap RawEncoding.Instruction.encode).length ≤
      is.length*gateGrowth e d*(B+1) := by
  induction is with
  | nil => simp
  | cons i is ih =>
    have hv := hvalid i (by simp)
    have hi := mappedInstruction_length_le e d x B hx i hv.1 hv.2 (hwire i (by simp))
    have hs := ih (by intro j hj; exact hvalid j (by simp [hj]))
      (by intro j hj; exact hwire j (by simp [hj]))
    simp only [List.map_cons,List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith

end QMAPerfectCompleteness.Main.CircuitRecipe.SourceTM


