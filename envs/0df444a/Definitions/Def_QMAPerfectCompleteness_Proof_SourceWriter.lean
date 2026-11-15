-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_SourceWriter
-- name    : QMAPerfectCompleteness_Proof_SourceWriter
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:23:39.476553+00:00
-- url     : https://prove2.me/theorems/860b57e5-0282-4686-9350-301049d452fb
-- title:
--   A bounded writer for mapped source circuits
-- statement:
--   Defines the source writer used by the recipe compiler in either forward or reverse instruction order. It copies the chosen read-only stream, traverses and remaps its instructions, restores all temporary registers and supplies quadratic time and output-size bounds.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/SourceWriter.lean, retained declaration span lines 17–190.

/- Generated from Solutions.SourceWriter by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_SourceInstructionMapper
import Definitions.Def_QMAPerfectCompleteness_Proof_SourceWriterBounds
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



/-! Preserve a readonly source circuit, traverse its instruction stream with an actual finite
parser, and emit the mapped circuit into the recipe writer's reversed output buffer. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
open Turing StateTransition
namespace QMAPerfectCompleteness.Main.CircuitRecipe.SourceTM
open QAlgorithms.Complexity (Str encNat)
open QMAPerfectCompleteness.Uniformity.StructuredStack
open Code
noncomputable section

def mappedBody {d : ℕ} (e : Expr) (x : Context d) (gs : List RawEncoding.Instruction) : Str :=
  (gs.map (mappedInstruction e x)).flatMap RawEncoding.Instruction.encode

abbrev gateLoop (e : Expr) (d : ℕ) : Code (K e d) := whilePeek (input e d) Option.isSome (gateCode e d)

lemma instruction_head (i : RawEncoding.Instruction) (tail : Str) :
    Option.isSome (i.encode++tail).head?=true := by
  cases hg : i.gate with
  | zero => simp [RawEncoding.Instruction.encode,hg,encNat]
  | succ n => simp [RawEncoding.Instruction.encode,hg,encNat,List.replicate_succ]

lemma gateLoop_exec (e : Expr) (d : ℕ) (x : Context d) (B : ℕ) (hx : x.Valid B)
    (gs : List RawEncoding.Instruction) (hvalid : Context.SourceValid gs)
    (hwire : ∀ i∈gs,∀ w∈i.wires,w≤B) (S : K e d → Str) (q : Option Bool)
    (hin : ∀ a,S (.inl a)=x.encode a) (hparse : S (input e d)=gs.flatMap RawEncoding.Instruction.encode)
    (htag : S (tag e d)=[]) (htmp : S (temporary e d)=[]) (ha : S (address e d)=[])
    (heval : ∀ j,S (evalEmb e d (.inr j))=[]) :
    (gateLoop e d).Exec (q,S)
      (none,Function.update (Function.update S (input e d) []) (output e d)
        ((mappedBody e x gs).reverse++S (output e d)))
      (gs.length*(gateCost e d*(B+1)+1)+1) := by
  induction gs generalizing S q with
  | nil =>
    have hh := while_false (input e d) Option.isSome (gateCode e d) (q,S) (by simp [hparse])
    have hs : Function.update (Function.update S (input e d) []) (output e d)
        ((mappedBody e x []).reverse++S (output e d))=S := by
      funext k
      by_cases hi : k=input e d <;> by_cases ho : k=output e d <;>
        simp_all [mappedBody,input,output,scratch]
    rw [hs]
    simpa [hparse] using hh
  | cons i gs ih =>
    have hi := hvalid i (by simp)
    have hv : Context.SourceValid gs := by intro i hi; exact hvalid i (by simp [hi])
    have hw : ∀ j∈gs,∀ w∈j.wires,w≤B := by intro j hj w hw; exact hwire j (by simp [hj]) w hw
    have hp : S (input e d)=i.encode++gs.flatMap RawEncoding.Instruction.encode := by
      simpa only [List.flatMap_cons] using hparse
    have hgate := gateCode_exec e d x B hx i hi.1 hi.2
      (hwire i (by simp)) (gs.flatMap RawEncoding.Instruction.encode) S
      (i.encode++gs.flatMap RawEncoding.Instruction.encode).head? hin hp htag htmp ha heval
    let S₀ := Function.update (Function.update S (input e d) (gs.flatMap RawEncoding.Instruction.encode))
      (output e d) ((mappedInstruction e x i).encode.reverse++S (output e d))
    have hin₀ : ∀ a,S₀ (.inl a)=x.encode a := by
      intro a; simpa [S₀,input,output,scratch] using hin a
    have hp₀ : S₀ (input e d)=gs.flatMap RawEncoding.Instruction.encode := by simp [S₀,input,output,scratch]
    have ht₀ : S₀ (tag e d)=[] := by simpa [S₀,input,tag,output,scratch] using htag
    have hm₀ : S₀ (temporary e d)=[] := by simpa [S₀,input,temporary,output,scratch] using htmp
    have ha₀ : S₀ (address e d)=[] := by simpa [S₀,input,address,output,scratch] using ha
    have he₀ : ∀ j,S₀ (evalEmb e d (.inr j))=[] := by
      intro j
      simpa only [S₀,Function.update_of_ne (evalWork_ne_output e d j),
        Function.update_of_ne (evalWork_ne_scratch e d j 0)] using heval j
    have htail := ih hv hw S₀ none hin₀ hp₀ ht₀ hm₀ ha₀ he₀
    have hh := while_true (input e d) Option.isSome (gateCode e d) (d := (q,S))
      (by change Option.isSome (S (input e d)).head?=true; rw [hp]; exact instruction_head i _)
      (by simpa only [hp] using hgate) htail
    have hs : Function.update (Function.update S₀ (input e d) []) (output e d)
        ((mappedBody e x gs).reverse++S₀ (output e d)) =
        Function.update (Function.update S (input e d) []) (output e d)
          ((mappedBody e x (i::gs)).reverse++S (output e d)) := by
      funext k
      by_cases hi : k=input e d <;> by_cases ho : k=output e d <;>
        simp_all [S₀,mappedBody,List.reverse_append,List.append_assoc,input,output,scratch]
    rw [hs] at hh
    convert hh using 1 <;> simp only [List.length_cons] <;> ring

abbrev prepare (e : Expr) (d : ℕ) (s : ReadOnly d) : Code (K e d) :=
  seq (copy (.inl s) (reverseBuffer e d) (temporary e d))
    (transfer (reverseBuffer e d) (input e d))

lemma prepare_exec (e : Expr) (d : ℕ) (s : ReadOnly d) (bits : Str)
    (S : K e d → Str) (q : Option Bool) (hin : S (.inl s)=bits)
    (hw : ∀ w,S (.inr (.inr w))=[]) :
    (prepare e d s).Exec (q,S) (none,Function.update S (input e d) bits) (6*bits.length+3) := by
  have hc := copy_exec (.inl s) (reverseBuffer e d) (temporary e d)
    (by simp [reverseBuffer,scratch]) (by simp [temporary,scratch])
    (scratch_ne e d 1 2 (by decide)) bits S q hin (hw _)
  have hr : S (reverseBuffer e d)=[] := hw _
  rw [hr,List.append_nil] at hc
  let S₀ := Function.update S (reverseBuffer e d) bits.reverse
  have ht := transfer_exec (reverseBuffer e d) (input e d)
    (scratch_ne e d 1 0 (by decide)) bits.reverse S₀ none (by simp [S₀])
  have hi : S₀ (input e d)=[] := by
    simpa [S₀,reverseBuffer,input,scratch] using hw (⟨0,by change 0<(e.evaluator d).slots+5; omega⟩)
  rw [hi,List.append_nil,List.reverse_reverse] at ht
  have hs : Function.update (Function.update S₀ (reverseBuffer e d) []) (input e d) bits =
      Function.update S (input e d) bits := by
    funext k
    by_cases hr : k=reverseBuffer e d <;> by_cases hi : k=input e d <;>
      simp_all [S₀,reverseBuffer,input,scratch]
  rw [hs] at ht
  have hh := seq_exec _ _ hc ht
  convert hh using 1 <;> simp only [List.length_reverse] <;> omega

def selectedSource {d : ℕ} (reverse : Bool) (x : Context d) : List RawEncoding.Instruction :=
  if reverse then x.source.reverse else x.source

def sourceIndex (reverse : Bool) : Fin 2 := if reverse then 1 else 0

abbrev sourceCode (e : Expr) (d : ℕ) (reverse : Bool) : Code (K e d) :=
  seq (prepare e d (.inr (sourceIndex reverse))) (gateLoop e d)

/-- The actual source-circuit traversal primitive used by every compiled recipe. -/
noncomputable def sourceWriter (d : ℕ) (reverse : Bool) (e : Expr) :
    RecipeWriter d (Recipe.source reverse e).codeAt := by
  let time : Polynomial ℕ := 6*Polynomial.X+3+
    Polynomial.X*(Polynomial.C (gateCost e d)*(Polynomial.X+1)+1)+1
  let size : Polynomial ℕ := Polynomial.X*Polynomial.C (gateGrowth e d)*(Polynomial.X+1)
  refine { slots := Slots e d, code := sourceCode e d reverse, time := time, size := size, length_bound := ?_, run := ?_ }
  · intro x B hx
    let gs := selectedSource reverse x
    have hl : (gs.flatMap RawEncoding.Instruction.encode).length≤B := by
      cases reverse <;> simpa [gs,selectedSource,Context.code,source_reverse_length] using hx.2.2.1
    have hv : Context.SourceValid gs := by
      intro i hi
      apply hx.2.2.2 i
      cases reverse <;> simpa [gs,selectedSource] using hi
    have hw : ∀ i∈gs,∀ w∈i.wires,w≤B := by
      intro i hi w hw
      exact (source_wire_le_length gs i hi w hw).trans hl
    have hs := mapped_source_length_le e d x B hx gs hv hw
    have hc := (source_count_le_length gs).trans hl
    have hm := Nat.mul_le_mul_right (gateGrowth e d*(B+1)) hc
    have hcode : (Recipe.source reverse e).codeAt x=mappedBody e x gs := rfl
    rw [hcode]
    change (mappedBody e x gs).length ≤ size.eval B
    simpa only [mappedBody,size,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C,
      Polynomial.eval_add,Polynomial.eval_one,Nat.mul_assoc] using hs.trans (by simpa [Nat.mul_assoc] using hm)
  · intro x B hx S q hin hw
    let gs := selectedSource reverse x
    let bits := gs.flatMap RawEncoding.Instruction.encode
    have hread : S (.inl (.inr (sourceIndex reverse)))=bits := by
      have hh := hin (.inr (sourceIndex reverse))
      cases reverse <;> simpa [Context.encode,Context.code,sourceIndex,bits,gs,selectedSource] using hh
    have hp := prepare_exec e d (.inr (sourceIndex reverse)) bits S q hread hw
    let S₀ := Function.update S (input e d) bits
    have hin₀ : ∀ a,S₀ (.inl a)=x.encode a := by
      intro a; simpa [S₀,input,scratch] using hin a
    have htag : S₀ (tag e d)=[] := by simpa [S₀,input,tag,scratch] using hw (⟨3,by change 3<(e.evaluator d).slots+5; omega⟩)
    have htmp : S₀ (temporary e d)=[] := by simpa [S₀,input,temporary,scratch] using hw (⟨2,by change 2<(e.evaluator d).slots+5; omega⟩)
    have ha : S₀ (address e d)=[] := by simpa [S₀,input,address,scratch] using hw (⟨4,by change 4<(e.evaluator d).slots+5; omega⟩)
    have heval : ∀ j,S₀ (evalEmb e d (.inr j))=[] := by
      intro j
      dsimp only [S₀]
      rw [Function.update_of_ne (evalWork_ne_scratch e d j 0)]
      exact hw _
    have hl : bits.length≤B := by
      cases reverse <;> simpa [bits,gs,selectedSource,Context.code,source_reverse_length] using hx.2.2.1
    have hv : Context.SourceValid gs := by
      intro i hi
      apply hx.2.2.2 i
      cases reverse <;> simpa [gs,selectedSource] using hi
    have hwire : ∀ i∈gs,∀ w∈i.wires,w≤B := by
      intro i hi w hw
      exact (source_wire_le_length gs i hi w hw).trans hl
    have hlo := gateLoop_exec e d x B hx gs hv hwire S₀ none hin₀
      (by simp [S₀,bits]) htag htmp ha heval
    have hs : Function.update (Function.update S₀ (input e d) []) (output e d)
        ((mappedBody e x gs).reverse++S₀ (output e d)) =
        Function.update S (output e d) ((mappedBody e x gs).reverse++S (output e d)) := by
      funext k
      by_cases hi : k=input e d <;> by_cases ho : k=output e d <;>
        simp_all [S₀,input,output,scratch,hw]
    rw [hs] at hlo
    have hh := seq_exec _ _ hp hlo
    have hcode : (Recipe.source reverse e).codeAt x=mappedBody e x gs := rfl
    rw [hcode]
    apply exec_mono _ hh
    have hc := (source_count_le_length gs).trans hl
    have hm := Nat.mul_le_mul_right (gateCost e d*(B+1)+1) hc
    simp only [time,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
    nlinarith

noncomputable def sourceWriters : SourceWriters := sourceWriter

end
end QMAPerfectCompleteness.Main.CircuitRecipe.SourceTM


