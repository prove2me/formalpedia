-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RecipeCompositeWriters
-- name    : QMAPerfectCompleteness_Proof_RecipeCompositeWriters
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:19:11.142687+00:00
-- url     : https://prove2.me/theorems/cf7474c0-0925-4e96-b79a-0099a750f84b
-- title:
--   Writers for bounded circuit recipes
-- statement:
--   Constructs finite writers for recipe concatenation, increasing and decreasing bounded loops, and conditional branches. A supplied source-circuit writer completes the recursive compiler after normalization of wire mappings.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RecipeCompositeWriters.lean, retained declaration span lines 10–121.

/- Generated from Solutions.RecipeCompositeWriters by authoritative Stage-2 skeleton subtraction.
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



/-! Assemble actual finite writers for the bounded loop and branch structure of the paper's
circuit construction. No general polynomial-time function-composition theorem is used. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CircuitRecipe
open QMAPerfectCompleteness.Uniformity.StructuredStack

namespace Recipe
abbrev codeAt (p : Recipe) {d : ℕ} (x : Context d) : List Bool :=
  (p.eval (inputEnvironment x.values) (inputContext x.values) x.source).flatMap RawEncoding.Instruction.encode
end Recipe

namespace RecipeWriter

noncomputable def nil (d : ℕ) : RecipeWriter d (Recipe.nil.codeAt) := Writer.empty

noncomputable def append {d : ℕ} {p q : Recipe}
    (P : RecipeWriter d p.codeAt) (Q : RecipeWriter d q.codeAt) :
    RecipeWriter d (p.append q).codeAt := by
  apply (Writer.append P Q).congr
  intro x B hx
  simp [Recipe.codeAt,Recipe.eval]

lemma upWords_range (F : ℕ → List Bool) (j n : ℕ) :
    Code.upWords F j n=(List.range' j n).flatMap F := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => simp [Code.upWords,List.range'_succ,ih]

lemma downWords_range (F : ℕ → List Bool) (n : ℕ) :
    Code.downWords F n=(List.range n).reverse.flatMap F := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Code.downWords,List.range_succ,List.reverse_append,ih]

noncomputable def forUp {d : ℕ} (bound : Expr) {body : Recipe}
    (W : RecipeWriter (d+1) body.codeAt) : RecipeWriter d (Recipe.forUp bound body).codeAt := by
  let E := bound.evaluator d
  let R := Polynomial.C (E.growth+1)*(Polynomial.X+1)
  let P := Writer.forUp (encode := Context.encode) (valid := Context.Valid) E readInputs Context.values (by intro x a; rfl)
    (by intro x B hx; exact hx.1) W.indexed R (by
      intro x B hx j hj
      apply Context.valid_push x j B (R.eval B) hx
      · simp only [R,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
        nlinarith
      · have hn := E.bound x.values B hx.1
        simp only [R,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
        nlinarith)
  apply P.congr
  intro x B hx
  rw [upWords_range,← List.range_eq_range']
  have he : bound.value d x.values=bound.eval (inputEnvironment x.values) (inputContext x.values) := by
    simp [Expr.value,inputAddress,hx.2.1]
  rw [he]
  simp only [Recipe.codeAt,Context.push_context,Context.push_environment,Context.push_source,
    Recipe.eval,List.flatMap_assoc]

noncomputable def forDown {d : ℕ} (bound : Expr) {body : Recipe}
    (W : RecipeWriter (d+1) body.codeAt) : RecipeWriter d (Recipe.forDown bound body).codeAt := by
  let E := bound.evaluator d
  let R := Polynomial.C (E.growth+1)*(Polynomial.X+1)
  let P := Writer.forDown (encode := Context.encode) (valid := Context.Valid) E readInputs Context.values (by intro x a; rfl)
    (by intro x B hx; exact hx.1) W.indexed R (by
      intro x B hx j hj
      apply Context.valid_push x j B (R.eval B) hx
      · simp only [R,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
        nlinarith
      · have hn := E.bound x.values B hx.1
        simp only [R,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
        nlinarith)
  apply P.congr
  intro x B hx
  rw [downWords_range]
  have he : bound.value d x.values=bound.eval (inputEnvironment x.values) (inputContext x.values) := by
    simp [Expr.value,inputAddress,hx.2.1]
  rw [he]
  simp only [Recipe.codeAt,Context.push_context,Context.push_environment,Context.push_source,
    Recipe.eval,List.flatMap_assoc]

noncomputable def ifLt {d : ℕ} (a b : Expr) {yes no : Recipe}
    (Y : RecipeWriter d yes.codeAt) (N : RecipeWriter d no.codeAt) :
    RecipeWriter d (Recipe.ifLt a b yes no).codeAt := by
  let E := Evaluator.binary (b.evaluator d) (a.evaluator d) false
  let W := Writer.ifNonzero E readInputs Context.values (by intro x a; rfl)
    (by intro x B hx; exact hx.1) Y N
  apply W.congr
  intro x B hx
  have ha : a.value d x.values=a.eval (inputEnvironment x.values) (inputContext x.values) := by
    simp [Expr.value,inputAddress,hx.2.1]
  have hb : b.value d x.values=b.eval (inputEnvironment x.values) (inputContext x.values) := by
    simp [Expr.value,inputAddress,hx.2.1]
  simp only [Bool.false_eq_true,ite_false,ha,hb,Recipe.codeAt,Recipe.eval]
  split_ifs <;> first | rfl | omega

end RecipeWriter

/-- The sole primitive supplied by the source-circuit traversal machine. -/
abbrev SourceWriters := ∀ (d : ℕ) (reverse : Bool) (wireMap : Expr),
  RecipeWriter d (Recipe.source reverse wireMap).codeAt

/-- Compile a finite recipe structurally, composing its wire maps before emitting addresses. -/
noncomputable def Recipe.writer (source : SourceWriters) :
    (p : Recipe) → (d : ℕ) → (wireMap : Expr) → RecipeWriter d (p.mapNormalize wireMap).codeAt
  | .nil,d,_ => RecipeWriter.nil d
  | .emit tag wires,d,m => gateWriter d tag (wires.map (m.replaceAddr ·))
  | .append a b,d,m => RecipeWriter.append (a.writer source d m) (b.writer source d m)
  | .forUp n body,d,m => RecipeWriter.forUp n (body.writer source (d+1) m.lift)
  | .forDown n body,d,m => RecipeWriter.forDown n (body.writer source (d+1) m.lift)
  | .ifLt a b y n,d,m => RecipeWriter.ifLt a b (y.writer source d m) (n.writer source d m)
  | .source reverse m,d,w => source d reverse (w.replaceAddr m)
  | .mapWires m body,d,w => body.writer source d (w.replaceAddr m)

/-- Any finite recipe has a literal finite polynomial-time writer once source traversal is supplied. -/
noncomputable def Recipe.compiledWriter (source : SourceWriters) (p : Recipe) (d : ℕ) :
    RecipeWriter d p.codeAt :=
  (p.writer source d .addr).congr (by
    intro x B hx
    change (p.normalize.eval (inputEnvironment x.values) (inputContext x.values) x.source).flatMap
      RawEncoding.Instruction.encode=p.codeAt x
    rw [Recipe.eval_normalize])

end QMAPerfectCompleteness.Main.CircuitRecipe


