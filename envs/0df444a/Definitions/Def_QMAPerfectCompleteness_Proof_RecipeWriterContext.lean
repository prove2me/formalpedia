-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_RecipeWriterContext
-- name    : QMAPerfectCompleteness_Proof_RecipeWriterContext
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:13:18.121945+00:00
-- url     : https://prove2.me/theorems/b8af660b-f328-4848-bd9a-97d08c314126
-- title:
--   Read-only contexts for recipe writers
-- statement:
--   Defines the parameter and loop-index inputs, current-address slot, and forward and reverse instruction streams available to a writer. Validity bounds all unary inputs and source-code size; indexed-context embeddings add one loop variable while preserving the original inputs.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/RecipeWriterContext.lean, retained declaration span lines 11–104.

/- Generated from Solutions.RecipeWriterContext by authoritative Stage-2 skeleton subtraction.
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



/-! The concrete read-only register interface shared by cyclic recipe writers and their
serializer wrapper. Source streams are encoded in both instruction orders. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CircuitRecipe
open QMAPerfectCompleteness.Uniformity.StructuredStack

abbrev ReadOnly (d : ℕ) := Inputs d ⊕ Fin 2
structure Context (d : ℕ) where
  values : Inputs d → ℕ
  source : List RawEncoding.Instruction

namespace Context

def code {d : ℕ} (x : Context d) (reverse : Bool := false) : List Bool :=
  (if reverse then x.source.reverse else x.source).flatMap RawEncoding.Instruction.encode

def encode {d : ℕ} (x : Context d) : ReadOnly d → List Bool
  | .inl a => Code.unary (x.values a)
  | .inr s => x.code (s ≠ 0)

def SourceValid (src : List RawEncoding.Instruction) : Prop :=
  ∀ g ∈ src,g.gate<4 ∧ g.wires.length=RawEncoding.g2Table[g.gate]?.getD 0

def Valid {d : ℕ} (x : Context d) (B : ℕ) : Prop :=
  (∀ a,x.values a≤B) ∧ x.values (.inr (.inr ()))=0 ∧ (x.code).length≤B ∧ SourceValid x.source

/-- Add one read-only loop index as the innermost context variable. -/
def push {d : ℕ} (x : Context d) (j : ℕ) : Context (d+1) where
  values
    | .inl p => x.values (.inl p)
    | .inr (.inl k) => Fin.cases j (fun k=>x.values (.inr (.inl k))) k
    | .inr (.inr ()) => x.values (.inr (.inr ()))
  source := x.source

@[simp] theorem push_environment {d : ℕ} (x : Context d) (j : ℕ) :
    inputEnvironment (x.push j).values=inputEnvironment x.values := rfl
@[simp] theorem push_context {d : ℕ} (x : Context d) (j : ℕ) :
    inputContext (x.push j).values=j::inputContext x.values := by
  simp [inputContext,push,List.ofFn_succ]


@[simp] theorem push_source {d : ℕ} (x : Context d) (j : ℕ) :
    (x.push j).source=x.source := rfl

 theorem valid_push {d : ℕ} (x : Context d) (j B B' : ℕ) (hx : x.Valid B)
    (hBB : B≤B') (hj : j≤B') : (x.push j).Valid B' := by
  refine ⟨?_,hx.2.1,hx.2.2.1.trans hBB,hx.2.2.2⟩
  intro a
  rcases a with (p|k|u)
  · exact (hx.1 _).trans hBB
  · refine Fin.cases hj (fun k=>?_) k
    exact (hx.1 _).trans hBB
  · cases u; exact (hx.1 _).trans hBB

end Context

abbrev RecipeWriter (d : ℕ) (f : Context d → List Bool) :=
  Writer (ReadOnly d) (Context d) Context.encode Context.Valid f

/-- Identify a nested recipe's extra index input with a caller-owned unary loop counter. -/
def innerInput {d : ℕ} : ReadOnly (d+1) → (ReadOnly d ⊕ Unit)
  | .inl (.inl p) => .inl (.inl (.inl p))
  | .inl (.inr (.inl k)) => Fin.cases (.inr ()) (fun k=>.inl (.inl (.inr (.inl k)))) k
  | .inl (.inr (.inr ())) => .inl (.inl (.inr (.inr ())))
  | .inr s => .inl (.inr s)

def outerInput {d : ℕ} : (ReadOnly d ⊕ Unit) → ReadOnly (d+1)
  | .inl (.inl (.inl p)) => .inl (.inl p)
  | .inl (.inl (.inr (.inl k))) => .inl (.inr (.inl k.succ))
  | .inl (.inl (.inr (.inr ()))) => .inl (.inr (.inr ()))
  | .inl (.inr s) => .inr s
  | .inr () => .inl (.inr (.inl 0))

@[simp] theorem outer_inner {d : ℕ} (a : ReadOnly (d+1)) : outerInput (innerInput a)=a := by
  rcases a with ((p|k|u)|s)
  · rfl
  · refine Fin.cases ?_ (fun k=>?_) k <;> rfl
  · cases u; rfl
  · rfl

abbrev innerInputEmb {d : ℕ} : ReadOnly (d+1) ↪ (ReadOnly d ⊕ Unit) :=
  ⟨innerInput,Function.LeftInverse.injective outer_inner⟩

@[simp] theorem encode_push {d : ℕ} (x : Context d) (j : ℕ) (a : ReadOnly (d+1)) :
    Writer.indexedEncoding Context.encode (x,j) (innerInput a)=(x.push j).encode a := by
  rcases a with ((p|k|u)|s)
  · rfl
  · refine Fin.cases ?_ (fun k=>?_) k <;> rfl
  · cases u; rfl
  · rfl

/-- Reinterpret a nested recipe writer as an indexed writer in its parent's register frame. -/
noncomputable def RecipeWriter.indexed {d : ℕ} {f : Context (d+1) → List Bool}
    (W : RecipeWriter (d+1) f) :
    Writer (ReadOnly d ⊕ Unit) (Context d × ℕ) (Writer.indexedEncoding Context.encode)
      (fun x B=>(x.1.push x.2).Valid B) (fun x=>f (x.1.push x.2)) :=
  W.adapt (Writer.indexedEncoding Context.encode) (fun x B=>(x.1.push x.2).Valid B)
    innerInputEmb (fun x=>x.1.push x.2) Polynomial.X
    (by intro x a; exact encode_push x.1 x.2 a) (by simpa)

end QMAPerfectCompleteness.Main.CircuitRecipe


