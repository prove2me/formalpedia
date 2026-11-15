-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_CircuitExprTM
-- name    : QMAPerfectCompleteness_Proof_CircuitExprTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:02:12.351254+00:00
-- url     : https://prove2.me/theorems/43da53ec-1693-4b3e-bf42-2d0534ea83b4
-- title:
--   Unary evaluators for circuit expressions
-- statement:
--   Defines the parameter, loop-index and current-address inputs of a circuit recipe, and constructs a finite unary evaluator for every address expression. Evaluation supports constants, addition, subtraction, fixed scaling, halving and conditional comparisons.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/CircuitExprTM.lean, retained declaration span lines 9–33.

/- Generated from Solutions.CircuitExprTM by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitRecipe
import Definitions.Def_QMAPerfectCompleteness_Proof_CircuitUnitary
import Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
import Definitions.Def_QMAPerfectCompleteness_Proof_ControlCircuits
import Definitions.Def_QMAPerfectCompleteness_Proof_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Proof_EuclideanStates
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_RawCircuitEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_Repetition
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionCircuit
import Definitions.Def_QMAPerfectCompleteness_Proof_RepetitionEncoding
import Definitions.Def_QMAPerfectCompleteness_Proof_ReversibleGadgets
import Definitions.Def_QMAPerfectCompleteness_Proof_StackEmbedding
import Definitions.Def_QMAPerfectCompleteness_Proof_StackTransfers
import Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryEvaluator
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryStackOps
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Actual finite unary machines for every arithmetic expression in a circuit recipe. -/
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Main.CircuitRecipe
open QMAPerfectCompleteness.Uniformity.StructuredStack

/-- Parameters, the bounded loop-index context, and a current source-wire address. -/
abbrev Inputs (depth : ℕ) := Param ⊕ (Fin depth ⊕ Unit)

def inputEnvironment {d : ℕ} (v : Inputs d → ℕ) : Environment := fun p=>v (.inl p)
def inputContext {d : ℕ} (v : Inputs d → ℕ) : List ℕ := List.ofFn (fun j=>v (.inr (.inl j)))
def inputAddress {d : ℕ} (v : Inputs d → ℕ) : ℕ := v (.inr (.inr ()))

namespace Expr
abbrev value (e : Expr) (d : ℕ) (v : Inputs d → ℕ) : ℕ :=
  e.eval (inputEnvironment v) (inputContext v) (inputAddress v)

noncomputable def evaluator (e : Expr) (d : ℕ) : Evaluator (Inputs d) (e.value d) :=
  match e with
  | .lit n => Evaluator.literal n
  | .param p => Evaluator.input (A := Inputs d) (.inl p)
  | .bound j => if h : j<d then
      Evaluator.cast (by funext v; simp [value,eval,inputContext,h])
        (Evaluator.input (A := Inputs d) (.inr (.inl ⟨j,h⟩)))
    else Evaluator.cast (by funext v; simp [value,eval,inputContext,h]) (Evaluator.literal 0)
  | .addr => Evaluator.input (A := Inputs d) (.inr (.inr ()))
  | .add a b => Evaluator.cast (by rfl) (Evaluator.binary (a.evaluator d) (b.evaluator d) true)
  | .sub a b => Evaluator.cast (by rfl) (Evaluator.binary (a.evaluator d) (b.evaluator d) false)
  | .scale n a => Evaluator.scaling (a.evaluator d) n
  | .half a => Evaluator.halving (a.evaluator d)
  | .ifLt a b y n => Evaluator.lessThan (a.evaluator d) (b.evaluator d) (y.evaluator d) (n.evaluator d)



end Expr
end QMAPerfectCompleteness.Main.CircuitRecipe


