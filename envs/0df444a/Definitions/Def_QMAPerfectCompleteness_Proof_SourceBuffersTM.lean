-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_SourceBuffersTM
-- name    : QMAPerfectCompleteness_Proof_SourceBuffersTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:15:13.306034+00:00
-- url     : https://prove2.me/theorems/2e4281f1-71f3-473f-90e2-141b45763dca
-- title:
--   Forward and reverse instruction buffers
-- statement:
--   Defines the finite parser that reverses instruction order while retaining the ordinary encoding of each instruction. A backup stack allows the original forward source to be restored, and the execution specification clears the temporary buffer and preserves other registers.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/SourceBuffersTM.lean, retained declaration span lines 11–108.

/- Generated from Solutions.SourceBuffersTM by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QMAPerfectCompleteness_Main_Cyclic
import Definitions.Def_QMAPerfectCompleteness_Main_Compiler
import Definitions.Def_QMAPerfectCompleteness_Main_Classes
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Mathlib.Tactic.DeriveFintype
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
import Definitions.Def_QMAPerfectCompleteness_Proof_InstructionBuffersTM
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


set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.StructuredStack.Code
open QAlgorithms.Complexity (Str)
open Main.RawEncoding
variable {K : Type} [DecidableEq K]

abbrev bufferStep (L : Fin 4 ↪ K) : Code K :=
  seq (recordG2 (L 0) (L 1) (L 2)) (transfer (L 1) (L 3))
abbrev reverseBuffer (L : Fin 4 ↪ K) : Code K := whilePeek (L 0) Option.isSome (bufferStep L)

def bufferStore (L : Fin 4 ↪ K) (S : K→Str) (input backup reverse : Str) : K→Str :=
  Function.update (Function.update (Function.update S (L 0) input) (L 2) backup) (L 3) reverse

lemma bufferStep_exec (L : Fin 4 ↪ K) (i : Instruction) (hi : i.gate<4)
    (hw : i.wires.length=g2Table[i.gate]?.getD 0)
    (S : K→Str) (q : Option Bool) (tail : Str) (hx : S (L 0)=i.encode++tail) (ht : S (L 1)=[]) :
    (bufferStep L).Exec (q,S)
      (none,bufferStore L S tail (i.encode.reverse++S (L 2)) (i.encode++S (L 3))) (4*i.encode.length+2) := by
  have h01 : L 0≠L 1 := L.injective.ne (by decide)
  have h02 : L 0≠L 2 := L.injective.ne (by decide)
  have h12 : L 1≠L 2 := L.injective.ne (by decide)
  have h03 : L 0≠L 3 := L.injective.ne (by decide)
  have h13 : L 1≠L 3 := L.injective.ne (by decide)
  have h23 : L 2≠L 3 := L.injective.ne (by decide)
  let U := recordBits (L 0) (L 1) (L 2) S i.encode tail
  have h1 := recordG2_exec (L 0) (L 1) (L 2) h01 h02 h12 i hi hw S q tail hx
  have h2 := transfer_exec (L 1) (L 3) h13 i.encode.reverse U none (by
    simp [U,recordBits,Ne.symm h12,ht])
  have hh := seq_exec _ _ h1 h2
  have he : Function.update (Function.update U (L 1) []) (L 3) (i.encode.reverse.reverse++U (L 3)) =
      bufferStore L S tail (i.encode.reverse++S (L 2)) (i.encode++S (L 3)) := by
    funext k
    by_cases h0 : k=L 0 <;> by_cases h1 : k=L 1 <;> by_cases h2 : k=L 2 <;> by_cases h3 : k=L 3 <;>
      simp_all [U,recordBits,bufferStore]
  rw [he] at hh
  simp only [List.length_reverse] at hh
  convert hh using 1 <;> ring

lemma bufferStore_src (L : Fin 4 ↪ K) (S : K→Str) (input backup reverse : Str) :
    bufferStore L S input backup reverse (L 0)=input := by simp [bufferStore,L.injective.eq_iff]
lemma bufferStore_tmp (L : Fin 4 ↪ K) (S : K→Str) (input backup reverse : Str) :
    bufferStore L S input backup reverse (L 1)=S (L 1) := by simp [bufferStore,L.injective.eq_iff]
lemma bufferStore_backup (L : Fin 4 ↪ K) (S : K→Str) (input backup reverse : Str) :
    bufferStore L S input backup reverse (L 2)=backup := by simp [bufferStore,L.injective.eq_iff]
lemma bufferStore_reverse (L : Fin 4 ↪ K) (S : K→Str) (input backup reverse : Str) :
    bufferStore L S input backup reverse (L 3)=reverse := by simp [bufferStore]
lemma bufferStore_idem (L : Fin 4 ↪ K) (S : K→Str) (a b c x y z : Str) :
    bufferStore L (bufferStore L S a b c) x y z=bufferStore L S x y z := by
  funext k
  by_cases h0 : k=L 0 <;> by_cases h2 : k=L 2 <;> by_cases h3 : k=L 3 <;> simp_all [bufferStore]

lemma reverseBuffer_exec (L : Fin 4 ↪ K) (gs : List Instruction)
    (hv : Main.CircuitRecipe.Context.SourceValid gs) (S : K→Str) (q : Option Bool)
    (hx : S (L 0)=gs.flatMap Instruction.encode) (ht : S (L 1)=[]) :
    (reverseBuffer L).Exec (q,S)
      (none,bufferStore L S [] ((gs.flatMap Instruction.encode).reverse++S (L 2))
        (gs.reverse.flatMap Instruction.encode++S (L 3)))
      (4*(gs.flatMap Instruction.encode).length+3*gs.length+1) := by
  induction gs generalizing S q with
  | nil =>
    have he : bufferStore L S [] (([].flatMap Instruction.encode).reverse++S (L 2))
        ([].reverse.flatMap Instruction.encode++S (L 3))=S := by
      funext k
      by_cases h0 : k=L 0 <;> by_cases h2 : k=L 2 <;> by_cases h3 : k=L 3 <;>
        simp_all [bufferStore]
    rw [he]
    simpa [reverseBuffer,hx] using while_false (L 0) Option.isSome (bufferStep L) (q,S) (by simp [hx])
  | cons i gs ih =>
    have hi := hv i (by simp)
    let U := bufferStore L S (gs.flatMap Instruction.encode) (i.encode.reverse++S (L 2)) (i.encode++S (L 3))
    have hb := bufferStep_exec L i hi.1 hi.2 S (S (L 0)).head? (gs.flatMap Instruction.encode)
      (by simpa using hx) ht
    have htail := ih (by intro g hg; exact hv g (by simp [hg])) U none
      (bufferStore_src _ _ _ _ _) (by simpa [U,bufferStore_tmp] using ht)
    have hp : (S (L 0)).head?.isSome=true := by
      rw [hx]
      cases h : i.gate <;> simp [Instruction.encode,QAlgorithms.Complexity.encNat,h,List.replicate_succ]
    have hh := while_true (L 0) Option.isSome (bufferStep L) (d:=(q,S)) hp hb htail
    simp only [U,bufferStore_backup,bufferStore_reverse,bufferStore_idem] at hh
    convert hh using 1 <;> simp [reverseBuffer,List.reverse_cons,List.flatMap_append,List.reverse_append,List.append_assoc,
      List.length_append,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> ring

abbrev prepareBuffers (L : Fin 4 ↪ K) : Code K := seq (reverseBuffer L) (transfer (L 2) (L 0))
lemma prepareBuffers_exec (L : Fin 4 ↪ K) (gs : List Instruction)
    (hv : Main.CircuitRecipe.Context.SourceValid gs) (S : K→Str) (q : Option Bool)
    (hx : S (L 0)=gs.flatMap Instruction.encode) (ht : S (L 1)=[]) (hb : S (L 2)=[]) (hr : S (L 3)=[]) :
    (prepareBuffers L).Exec (q,S)
      (none,Function.update S (L 3) (gs.reverse.flatMap Instruction.encode))
      (6*(gs.flatMap Instruction.encode).length+3*gs.length+2) := by
  let U := bufferStore L S [] ((gs.flatMap Instruction.encode).reverse++S (L 2))
    (gs.reverse.flatMap Instruction.encode++S (L 3))
  have h1 := reverseBuffer_exec L gs hv S q hx ht
  have h2 := transfer_exec (L 2) (L 0) (L.injective.ne (by decide))
    ((gs.flatMap Instruction.encode).reverse) U none (by simp [U,bufferStore_backup,hb])
  have hh := seq_exec _ _ h1 h2
  have he : Function.update (Function.update U (L 2) []) (L 0)
      ((gs.flatMap Instruction.encode).reverse.reverse++U (L 0)) =
      Function.update S (L 3) (gs.reverse.flatMap Instruction.encode) := by
    funext k
    by_cases h0 : k=L 0 <;> by_cases h2 : k=L 2 <;> by_cases h3 : k=L 3 <;>
      simp_all [U,bufferStore]
  rw [he] at hh
  simp only [List.length_reverse] at hh
  convert hh using 1 <;> ring

end QMAPerfectCompleteness.Uniformity.StructuredStack.Code


