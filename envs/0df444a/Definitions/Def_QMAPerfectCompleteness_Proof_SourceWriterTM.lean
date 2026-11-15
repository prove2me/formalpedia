-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_SourceWriterTM
-- name    : QMAPerfectCompleteness_Proof_SourceWriterTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:15:49.764589+00:00
-- url     : https://prove2.me/theorems/98966e9d-0832-4e00-882c-8473c535897d
-- title:
--   The unary source-address mapping primitive
-- statement:
--   Defines the parser and evaluator register embedding for one source address. The primitive reads a terminated unary field, evaluates an arbitrary recipe address expression with the original parameters, emits the mapped field and clears all evaluator and address scratch.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/SourceWriterTM.lean, retained declaration span lines 16–134.

/- Generated from Solutions.SourceWriterTM by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryFieldCode
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryStackOps
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Concrete source-instruction mapper for recipe writers. Original source streams and all
parameter/context registers are preserved; the current source address is parsed in scratch. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.CircuitRecipe.SourceTM
open QAlgorithms.Complexity (Str encNat)
open QMAPerfectCompleteness.Uniformity.StructuredStack
open Code
noncomputable section

abbrev Slots (e : Expr) (d : ℕ) := (e.evaluator d).slots+5
abbrev K (e : Expr) (d : ℕ) := WriterStacks (ReadOnly d) (Slots e d)

def scratch (e : Expr) (d : ℕ) (j : Fin 5) : K e d :=
  .inr (.inr ⟨j.val,by change j.val<(e.evaluator d).slots+5; have := j.isLt; omega⟩)
abbrev input (e : Expr) (d : ℕ) : K e d := scratch e d 0
abbrev reverseBuffer (e : Expr) (d : ℕ) : K e d := scratch e d 1
abbrev temporary (e : Expr) (d : ℕ) : K e d := scratch e d 2
abbrev tag (e : Expr) (d : ℕ) : K e d := scratch e d 3
abbrev address (e : Expr) (d : ℕ) : K e d := scratch e d 4
abbrev output (e : Expr) (d : ℕ) : K e d := writerOutput

def evalInput (e : Expr) (d : ℕ) : (Inputs d ⊕ Fin (e.evaluator d).slots) → K e d
  | .inl (.inl p) => .inl (.inl (.inl p))
  | .inl (.inr (.inl k)) => .inl (.inl (.inr (.inl k)))
  | .inl (.inr (.inr ())) => address e d
  | .inr j => .inr (.inr ⟨5+j.val,by change 5+j.val<(e.evaluator d).slots+5; have := j.isLt; omega⟩)

abbrev evalEmb (e : Expr) (d : ℕ) : (Inputs d ⊕ Fin (e.evaluator d).slots) ↪ K e d :=
  ⟨evalInput e d,by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        rcases a with (p|k|u) <;> rcases b with (p'|k'|u') <;>
          simp_all [evalInput,scratch,address,Fin.ext_iff]
      | inr b =>
        rcases a with (p|k|u) <;> simp_all [evalInput,scratch,address,Fin.ext_iff]
        all_goals omega
    | inr a =>
      cases b with
      | inl b =>
        rcases b with (p|k|u) <;> simp_all [evalInput,scratch,address,Fin.ext_iff]
        all_goals omega
      | inr b => simpa [evalInput,Fin.ext_iff] using h⟩

def values {d : ℕ} (x : Context d) (w : ℕ) : Inputs d → ℕ :=
  Function.update x.values (.inr (.inr ())) w

def mappedWire {d : ℕ} (e : Expr) (x : Context d) (w : ℕ) : ℕ :=
  e.eval (inputEnvironment x.values) (inputContext x.values) w

lemma values_bound {d : ℕ} (x : Context d) (B w : ℕ) (hx : x.Valid B) (hw : w≤B) :
    ∀ a,values x w a≤B := by
  intro a
  by_cases ha : a=.inr (.inr ())
  · subst a; simpa [values] using hw
  · simpa [values,ha] using hx.1 a

lemma value_values {d : ℕ} (e : Expr) (x : Context d) (w : ℕ) :
    e.value d (values x w)=mappedWire e x w := by
  have he : inputEnvironment (values x w)=inputEnvironment x.values := rfl
  have hc : inputContext (values x w)=inputContext x.values := rfl
  change e.eval (inputEnvironment (values x w)) (inputContext (values x w))
    (inputAddress (values x w)) = mappedWire e x w
  rw [he,hc]
  simp only [mappedWire,inputAddress,values,Function.update_self]

noncomputable def oneAddress (e : Expr) (d : ℕ) : Code (K e d) :=
  seq (readField (input e d) (address e d))
    (seq ((e.evaluator d).emitCode (evalEmb e d) (output e d)) (clear (address e d)))

lemma eval_ne_output (e : Expr) (d : ℕ) :
    evalEmb e d (.inr (e.evaluator d).result) ≠ output e d := by simp [evalEmb,evalInput,output]

lemma scratch_ne (e : Expr) (d : ℕ) (i j : Fin 5) (h : i≠j) : scratch e d i ≠ scratch e d j := by
  simpa [scratch,Fin.ext_iff] using h

lemma evalWork_ne_output (e : Expr) (d : ℕ) (j : Fin (e.evaluator d).slots) :
    evalEmb e d (.inr j) ≠ output e d := by simp [evalEmb,evalInput,output]

lemma evalWork_ne_scratch (e : Expr) (d : ℕ) (j : Fin (e.evaluator d).slots) (i : Fin 5) :
    evalEmb e d (.inr j) ≠ scratch e d i := by
  intro h
  have he : 5+j.val=i.val := by simpa [evalEmb,evalInput,scratch,Fin.ext_iff] using h
  have := i.isLt
  omega

lemma oneAddress_exec (e : Expr) (d : ℕ) (x : Context d) (B w : ℕ) (hx : x.Valid B) (hw : w≤B)
    (tail : Str) (S : K e d → Str) (q : Option Bool)
    (hin : ∀ a,S (.inl a)=x.encode a)
    (hparse : S (input e d)=encNat w++tail) (ha : S (address e d)=[])
    (heval : ∀ j,S (evalEmb e d (.inr j))=[]) :
    (oneAddress e d).Exec (q,S)
      (none,Function.update (Function.update S (input e d) tail) (output e d)
        ((encNat (mappedWire e x w)).reverse++S (output e d)))
      ((2*w+3)+((e.evaluator d).cost+2*(e.evaluator d).growth+2)*(B+1)+(2*w+1)) := by
  let S0 := Function.update (Function.update S (input e d) tail) (address e d) (unary w)
  have h0 := readField_exec (input e d) (address e d)
    (scratch_ne e d 0 4 (by decide)) w tail S q hparse
  have h0' : (readField (input e d) (address e d)).Exec (q,S) (none,S0) (2*w+3) := by
    simpa only [ha,List.append_nil,unary,S0] using h0
  have hinput : ∀ a,S0 (evalEmb e d (.inl a))=unary (values x w a) := by
    intro a
    rcases a with (p|k|u)
    · simpa [S0,evalEmb,evalInput,input,address,scratch,values,Context.encode] using hin (.inl (.inl p))
    · simpa [S0,evalEmb,evalInput,input,address,scratch,values,Context.encode] using hin (.inl (.inr (.inl k)))
    · cases u; simp [S0,evalEmb,evalInput,input,address,scratch,values]
  have hwork : ∀ j,S0 (evalEmb e d (.inr j))=[] := by
    intro j
    simpa only [S0,Function.update_of_ne (evalWork_ne_scratch e d j 4),
      Function.update_of_ne (evalWork_ne_scratch e d j 0)] using heval j
  have h1 := (e.evaluator d).emitIn (evalEmb e d) (output e d) (eval_ne_output e d)
    (values x w) B (values_bound x B w hx hw) S0 none hinput hwork
  rw [value_values] at h1
  let S1 := Function.update S0 (output e d) ((encNat (mappedWire e x w)).reverse++S (output e d))
  have hout : S0 (output e d)=S (output e d) := by simp [S0,input,address,scratch,output]
  rw [hout] at h1
  have h2 := clear_exec (address e d) (unary w) S1 none (by simp [S1,S0,input,address,scratch,output])
  have he : Function.update S1 (address e d) [] =
      Function.update (Function.update S (input e d) tail) (output e d)
        ((encNat (mappedWire e x w)).reverse++S (output e d)) := by
    funext k
    by_cases hi : k=input e d <;> by_cases ha' : k=address e d <;>
      by_cases ho : k=output e d <;> simp_all [S1,S0,input,address,scratch,output]
  rw [he] at h2
  simpa only [oneAddress,unary,List.length_replicate,Nat.add_assoc] using
    seq_exec _ _ h0' (seq_exec _ _ h1 h2)

end
end QMAPerfectCompleteness.Main.CircuitRecipe.SourceTM


