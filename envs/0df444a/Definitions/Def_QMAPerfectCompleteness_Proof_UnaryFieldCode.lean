-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_UnaryFieldCode
-- name    : QMAPerfectCompleteness_Proof_UnaryFieldCode
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:58:32.458304+00:00
-- url     : https://prove2.me/theorems/8a5fe94b-1488-4857-bc10-518db6980a85
-- title:
--   Parsing and emitting terminated unary fields
-- statement:
--   Defines shared-stack routines for reading and emitting a unary natural number followed by its delimiter. The execution specifications track the unconsumed source tail, accumulated destination contents and preservation of unrelated stacks.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/UnaryFieldCode.lean, retained declaration span lines 11–87.

/- Generated from Solutions.UnaryFieldCode by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_StackTransfers
import Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Shared-stack unary field parsing and emission for concrete compiler scripts. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.StructuredStack.Code
open QAlgorithms.Complexity (encNat)
variable {K : Type} [DecidableEq K]

abbrev readFieldBody (src dst : K) : Code K := atomic
  (.pop src (fun _ b=>b) (.push dst (fun _=>true) .halt))
abbrev readFieldLoop (src dst : K) : Code K :=
  whilePeek src (fun b => b==some true) (readFieldBody src dst)
abbrev readField (src dst : K) : Code K :=
  seq (readFieldLoop src dst) (seq (pop src) (load none))

lemma readField_loop_exec (src dst : K) (hsd : src≠dst) (n : ℕ) (tail : List Bool)
    (S : K→List Bool) (v : Option Bool) (hx : S src=encNat n++tail) :
    (readFieldLoop src dst).Exec (v,S)
      (some false,Function.update (Function.update S src (false::tail)) dst (List.replicate n true++S dst))
      (2*n+1) := by
  induction n generalizing S v with
  | zero =>
    have hh := while_false src (fun b => b==some true) (readFieldBody src dst) (v,S) (by simp [hx,encNat])
    have hs : Function.update (Function.update S src (false::tail)) dst (List.replicate 0 true++S dst)=S := by
      funext k
      by_cases hks : k=src <;> by_cases hkd : k=dst <;> simp_all [encNat]
    rw [hs]
    simpa [hx,encNat] using hh
  | succ n ih =>
    let S' := Function.update (Function.update S src (encNat n++tail)) dst (true::S dst)
    have hbody : (readFieldBody src dst).Exec (some true,S) (some true,S') 1 := by
      have hh := atomic_exec (.pop src (fun _ b=>b) (.push dst (fun _=>true) .halt)) (some true,S) rfl
      simpa [effect,TM2.stepAux,hx,encNat,List.replicate_succ,hsd,Ne.symm hsd,S'] using hh
    have htail := ih S' (some true) (by simp [S',hsd,Ne.symm hsd])
    have hh := while_true src (fun b => b==some true) (readFieldBody src dst)
      (d := (v,S)) (by simp [hx,encNat,List.replicate_succ])
      (by simpa [hx,encNat,List.replicate_succ] using hbody) htail
    have hs : Function.update (Function.update S' src (false::tail)) dst (List.replicate n true++S' dst) =
        Function.update (Function.update S src (false::tail)) dst (List.replicate (n+1) true++S dst) := by
      funext k
      by_cases hks : k=src <;> by_cases hkd : k=dst <;>
        simp_all [S',List.replicate_add,List.append_assoc]
    rw [hs] at hh
    simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Parse one terminated unary header, retaining every unrelated source/scratch stack. -/
theorem readField_exec (src dst : K) (hsd : src≠dst) (n : ℕ) (tail : List Bool)
    (S : K→List Bool) (v : Option Bool) (hx : S src=encNat n++tail) :
    (readField src dst).Exec (v,S)
      (none,Function.update (Function.update S src tail) dst (List.replicate n true++S dst)) (2*n+3) := by
  let T := Function.update (Function.update S src (false::tail)) dst (List.replicate n true++S dst)
  let U := Function.update (Function.update S src tail) dst (List.replicate n true++S dst)
  have h1 : (readFieldLoop src dst).Exec (v,S) (some false,T) (2*n+1) := readField_loop_exec src dst hsd n tail S v hx
  have h2 : (pop src).Exec (some false,T) (some false,U) 1 := by
    have hh := pop_exec src (some false,T)
    have he : Function.update T src (T src).tail=U := by
      funext k
      by_cases hks : k=src <;> by_cases hkd : k=dst <;> simp_all [T,U]
    rw [he] at hh
    simpa [T,hsd,Ne.symm hsd] using hh
  have h3 := load_exec none (some false,U)
  have hh := seq_exec _ _ h1 (seq_exec _ _ h2 h3)
  simpa only [readField,Nat.add_assoc,show (1+1 : ℕ)=2 from rfl] using hh

abbrev emitField (src dst : K) : Code K := seq (push dst false) (transfer src dst)

/-- Emit a unary counter and delimiter in front of existing output, consuming the counter. -/
theorem emitField_exec (src dst : K) (hsd : src≠dst) (n : ℕ)
    (S : K→List Bool) (v : Option Bool) (hx : S src=List.replicate n true) :
    (emitField src dst).Exec (v,S)
      (none,Function.update (Function.update S src []) dst (encNat n++S dst)) (2*n+2) := by
  let T := Function.update S dst (false::S dst)
  have h1 : (push dst false).Exec (v,S) (v,T) 1 := push_exec dst false (v,S)
  have h2 := transfer_exec src dst hsd (List.replicate n true) T v (by simp [T,hsd,hx])
  have hh := seq_exec _ _ h1 h2
  have he : Function.update (Function.update T src []) dst ((List.replicate n true).reverse++T dst) =
      Function.update (Function.update S src []) dst (encNat n++S dst) := by
    funext k
    by_cases hks : k=src <;> by_cases hkd : k=dst <;>
      simp_all [T,encNat,List.reverse_replicate,List.append_assoc]
  rw [he] at hh
  simp only [List.length_replicate] at hh
  have ht : 1+(2*n+1)=2*n+2 := by omega
  rw [ht] at hh
  exact hh





end QMAPerfectCompleteness.Uniformity.StructuredStack.Code


