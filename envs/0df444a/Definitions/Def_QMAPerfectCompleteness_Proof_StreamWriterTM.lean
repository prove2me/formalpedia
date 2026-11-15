-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_StreamWriterTM
-- name    : QMAPerfectCompleteness_Proof_StreamWriterTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:02:11.85134+00:00
-- url     : https://prove2.me/theorems/706e27c4-3fd5-466f-8948-2f424b69ec2a
-- title:
--   Compositional finite output writers
-- statement:
--   Defines a writer specification with read-only inputs, a reversed output buffer, clean finite workspace and polynomial time and size bounds. Literal, field, concatenation, renaming and context-adaptation constructions compose these specifications through actual finite programs.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/StreamWriterTM.lean, retained declaration span lines 10–154.

/- Generated from Solutions.StreamWriterTM by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Proof_BinaryComposition
import Definitions.Def_QMAPerfectCompleteness_Proof_BlockEncoding
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



/-! Compositional finite TM2 writers. Inputs are read-only encoded values; output is accumulated
in reverse order, with a finite clean workspace and polynomial bounds on time and output size. -/
open Turing StateTransition
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Uniformity.StructuredStack
open Code

abbrev WriterStacks (I : Type) (n : ℕ) := I ⊕ (Unit ⊕ Fin n)
abbrev writerOutput {I : Type} {n : ℕ} : WriterStacks I n := .inr (.inl ())

structure Writer (I X : Type) [DecidableEq I] (encode : X → I → List Bool)
    (valid : X → ℕ → Prop) (f : X → List Bool) where
  slots : ℕ
  code : Code (WriterStacks I slots)
  time : Polynomial ℕ
  size : Polynomial ℕ
  length_bound : ∀ x B, valid x B → (f x).length ≤ size.eval B
  run : ∀ x B, valid x B → ∀ (S : WriterStacks I slots → List Bool) (q : Option Bool),
    (∀ i,S (.inl i)=encode x i) → (∀ w,S (.inr (.inr w))=[]) →
    code.Exec (q,S) (none,Function.update S writerOutput ((f x).reverse++S writerOutput)) (time.eval B)

namespace Writer
variable {I X : Type} [DecidableEq I] {encode : X → I → List Bool} {valid : X → ℕ → Prop}

abbrev frameEmb {n N : ℕ} (i : Fin n ↪ Fin N) : WriterStacks I n ↪ WriterStacks I N where
  toFun := Sum.map id (Sum.map id i)
  inj' := by
    intro x y h
    cases x with
    | inl x => cases y <;> simp_all
    | inr x => cases y with
      | inl y => simp_all
      | inr y => cases x <;> cases y <;> simp_all [i.injective.eq_iff]

noncomputable def runIn {f : X → List Bool} (W : Writer I X encode valid f) {N : ℕ}
    (i : Fin W.slots ↪ Fin N) (x : X) (B : ℕ) (hv : valid x B)
    (S : WriterStacks I N → List Bool) (q : Option Bool)
    (hin : ∀ a,S (.inl a)=encode x a) (hw : ∀ w,S (.inr (.inr (i w)))=[]) :
    (W.code.embed (frameEmb i)).Exec (q,S)
      (none,Function.update S writerOutput ((f x).reverse++S writerOutput)) (W.time.eval B) := by
  exact Code.embed_exec_update (frameEmb i) W.code S q none writerOutput _ _
    (W.run x B hv (S ∘ frameEmb i) q hin hw)

noncomputable def empty : Writer I X encode valid (fun _=>[]) where
  slots := 0
  code := Code.load none
  time := 1
  size := 0
  length_bound x B hv := by simp
  run x B hv S q hin hw := by simpa using Code.load_exec none (q,S)

noncomputable def append {f g : X → List Bool} (W : Writer I X encode valid f)
    (V : Writer I X encode valid g) : Writer I X encode valid (fun x=>f x++g x) where
  slots := W.slots+V.slots
  code := Code.seq (W.code.embed (frameEmb (Evaluator.block W.slots 0 (W.slots+V.slots) (by omega))))
    (V.code.embed (frameEmb (Evaluator.block V.slots W.slots (W.slots+V.slots) (by omega))))
  time := W.time+V.time
  size := W.size+V.size
  length_bound x B hv := by
    simpa only [List.length_append,Polynomial.eval_add] using Nat.add_le_add (W.length_bound x B hv) (V.length_bound x B hv)
  run x B hv S q hin hw := by
    let i := Evaluator.block W.slots 0 (W.slots+V.slots) (by omega)
    let j := Evaluator.block V.slots W.slots (W.slots+V.slots) (by omega)
    have h₁ := W.runIn i x B hv S q hin (fun w=>hw _)
    let S₁ := Function.update S writerOutput ((f x).reverse++S writerOutput)
    have h₂ := V.runIn j x B hv S₁ none
      (by intro a; simpa [S₁] using hin a)
      (by intro w; simpa [S₁] using hw (j w))
    have hh := Code.seq_exec _ _ h₁ h₂
    simpa [S₁,Function.update_idem,List.reverse_append,List.append_assoc,Polynomial.eval_add] using hh

abbrev pushListStmt {K : Type} (out : K) (bits : List Bool) :
    TM2.Stmt (fun _ : K=>Bool) Unit (Option Bool) :=
  bits.foldr (fun b q=>.push out (fun _=>b) q) (.load (fun _=>none) .halt)

lemma pushList_effect {K : Type} [DecidableEq K] (out : K) (bits : List Bool)
    (S : K → List Bool) (q : Option Bool) :
    TM2.stepAux (pushListStmt out bits) q S =
      ⟨none,none,Function.update S out (bits.reverse++S out)⟩ := by
  induction bits generalizing S with
  | nil => simp [pushListStmt,TM2.stepAux,Function.update_eq_self]
  | cons b bs ih =>
    simp only [pushListStmt,List.foldr_cons,TM2.stepAux]
    rw [ih]
    congr 1
    funext k
    by_cases hk : k=out <;> simp_all [List.reverse_cons,List.append_assoc]

noncomputable def literal (bits : List Bool) : Writer I X encode valid (fun _=>bits) where
  slots := 0
  code := Code.atomic (pushListStmt writerOutput bits)
  time := 1
  size := Polynomial.C bits.length
  length_bound x B hv := by simp
  run x B hv S q hin hw := by
    have hh := Code.atomic_exec (pushListStmt writerOutput bits) (q,S) (by rw [pushList_effect])
    simpa [Code.effect,pushList_effect] using hh

abbrev unaryInputs {A : Type} : (A → ℕ) → A → List Bool := fun v a=>unary (v a)
abbrev unaryValid {A : Type} : (A → ℕ) → ℕ → Prop := fun v B=>∀ a,v a≤B

/-- Emit an evaluated unary field using the actual arithmetic machine, then clear its workspace. -/
noncomputable def field {A : Type} [DecidableEq A] {f : (A → ℕ) → ℕ} (E : Evaluator A f) :
    Writer A (A → ℕ) unaryInputs unaryValid (fun v=>QAlgorithms.Complexity.encNat (f v)) := by
  let i : (A ⊕ Fin E.slots) ↪ WriterStacks A E.slots :=
    ⟨(fun a=>match a with |.inl a=>.inl a|.inr w=>.inr (.inr w)),by
      intro a b h; cases a <;> cases b <;> simp_all⟩
  refine { slots := E.slots, code := Evaluator.emitCode E i writerOutput, time := Polynomial.C (E.cost+2*E.growth+2)*(Polynomial.X+1), size := Polynomial.C (E.growth+1)*(Polynomial.X+1), length_bound := ?_, run := ?_ }
  · intro v B hv
    have hb := E.bound v B hv
    simp only [QAlgorithms.Complexity.encNat,List.length_append,List.length_replicate,List.length_singleton,
      Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    nlinarith
  · intro v B hv S q hin hw
    simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using
      E.emitIn i writerOutput (by simp [i]) v B hv S q hin hw

/-- Rename read-only inputs, change their semantic presentation and substitute a polynomial
bound on the input widths. The underlying finite machine and its output are unchanged. -/
noncomputable def adapt {f : X → List Bool} (W : Writer I X encode valid f)
    {J Y : Type} [DecidableEq J] (enc : Y → J → List Bool) (good : Y → ℕ → Prop)
    (i : I ↪ J) (decode : Y → X) (R : Polynomial ℕ)
    (henc : ∀ y a, enc y (i a)=encode (decode y) a)
    (hgood : ∀ y B,good y B → valid (decode y) (R.eval B)) :
    Writer J Y enc good (fun y=>f (decode y)) := by
  let e : WriterStacks I W.slots ↪ WriterStacks J W.slots :=
    ⟨Sum.map i id,by intro a b h; cases a <;> cases b <;> simp_all [i.injective.eq_iff]⟩
  refine { slots := W.slots, code := W.code.embed e, time := W.time.comp R, size := W.size.comp R, length_bound := ?_, run := ?_ }
  · intro y B hy
    simpa only [Polynomial.eval_comp] using W.length_bound (decode y) (R.eval B) (hgood y B hy)
  · intro y B hy S q hin hw
    have hh := Code.embed_exec_update e W.code S q none writerOutput _ _
      (W.run (decode y) (R.eval B) (hgood y B hy) (S ∘ e) q
        (by intro a; simpa [e,henc] using hin (i a))
        (by intro w; simpa [e] using hw w))
    change (W.code.embed e).Exec (q,S)
      (none,Function.update S writerOutput ((f (decode y)).reverse++S writerOutput))
      (W.time.eval (R.eval B)) at hh
    simpa only [Polynomial.eval_comp] using hh



/-- Replace the output specification by an equal one on the inputs used by the reduction. -/
noncomputable def congr {f g : X → List Bool} (W : Writer I X encode valid f)
    (h : ∀ x B,valid x B → f x=g x) : Writer I X encode valid g where
  slots := W.slots
  code := W.code
  time := W.time
  size := W.size
  length_bound x B hx := by rw [← h x B hx]; exact W.length_bound x B hx
  run x B hx S q hin hw := by rw [← h x B hx]; exact W.run x B hx S q hin hw

end Writer
end QMAPerfectCompleteness.Uniformity.StructuredStack


