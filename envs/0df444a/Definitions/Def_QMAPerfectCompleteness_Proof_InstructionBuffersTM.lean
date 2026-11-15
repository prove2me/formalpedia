-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_InstructionBuffersTM
-- name    : QMAPerfectCompleteness_Proof_InstructionBuffersTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:59:23.569511+00:00
-- url     : https://prove2.me/theorems/af24e148-9db7-4e47-a9e0-5c3df0325082
-- title:
--   Instruction-aware source buffering
-- statement:
--   Defines finite parsing kernels that record unary tags and address fields for the four G2 instruction arities. Unlike reversing individual bits, these routines retain the normal encoding within each instruction while supporting reversal of instruction order.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/InstructionBuffersTM.lean, retained declaration span lines 11–162.

/- Generated from Solutions.InstructionBuffersTM by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryFieldCode
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion


/-! Finite shared-stack parsing kernels for instruction-order source reversal. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.StructuredStack.Code
open QAlgorithms.Complexity (encNat)
variable {K : Type} [DecidableEq K]

abbrev recordBits (src tmp backup : K) (S : K→List Bool) (bits tail : List Bool) : K→List Bool :=
  Function.update (Function.update (Function.update S src tail) tmp (bits.reverse++S tmp))
    backup (bits.reverse++S backup)

lemma recordBits_append (src tmp backup : K) (hst : src≠tmp) (hsb : src≠backup) (htb : tmp≠backup)
    (S : K→List Bool) (a b mid tail : List Bool) :
    recordBits src tmp backup (recordBits src tmp backup S a mid) b tail =
      recordBits src tmp backup S (a++b) tail := by
  funext k
  by_cases hks : k=src <;> by_cases hkt : k=tmp <;> by_cases hkb : k=backup <;>
    simp_all [recordBits,List.reverse_append,List.append_assoc]

abbrev recordBit (src tmp backup : K) : Code K := atomic
  (.pop src (fun _ b=>b) (.push tmp (fun v=>v.getD false)
    (.push backup (fun v=>v.getD false) (.load (fun _=>none) .halt))))
lemma recordBit_exec (src tmp backup : K) (hst : src≠tmp) (hsb : src≠backup) (htb : tmp≠backup) (S : K→List Bool) (q : Option Bool)
    (b : Bool) (tail : List Bool) (hx : S src=b::tail) :
    (recordBit src tmp backup).Exec (q,S) (none,recordBits src tmp backup S [b] tail) 1 := by
  have h := atomic_exec (.pop src (fun _ b=>b) (.push tmp (fun v=>v.getD false)
    (.push backup (fun v=>v.getD false) (.load (fun _=>none) .halt)))) (q,S) rfl
  simpa [recordBit,effect,TM2.stepAux,hx,recordBits,hst,hsb,htb,Ne.symm hst,Ne.symm hsb,Ne.symm htb] using h

abbrev recordField (src tmp backup : K) : Code K :=
  seq (whilePeek src (fun b=>b==some true) (recordBit src tmp backup)) (recordBit src tmp backup)

lemma recordField_loop_exec (src tmp backup : K) (hst : src≠tmp) (hsb : src≠backup) (htb : tmp≠backup)
    (n : ℕ) (S : K→List Bool) (q : Option Bool) (tail : List Bool) (hx : S src=encNat n++tail) :
    (whilePeek src (fun b=>b==some true) (recordBit src tmp backup)).Exec (q,S)
      (some false,recordBits src tmp backup S (List.replicate n true) (false::tail)) (2*n+1) := by
  induction n generalizing S q with
  | zero =>
    have he : recordBits src tmp backup S (List.replicate 0 true) (false::tail)=S := by
      funext k
      by_cases hks : k=src <;> by_cases hkt : k=tmp <;> by_cases hkb : k=backup <;>
        simp_all [recordBits,encNat]
    rw [he]
    simpa [hx,encNat] using while_false src (fun b=>b==some true) (recordBit src tmp backup) (q,S) (by simp [hx,encNat])
  | succ n ih =>
    let U := recordBits src tmp backup S [true] (encNat n++tail)
    have hb := recordBit_exec src tmp backup hst hsb htb S (some true) true (encNat n++tail)
      (by simpa [encNat,List.replicate_succ] using hx)
    have ht := ih U none (by simp [U,recordBits,hst,hsb,Ne.symm hst,Ne.symm hsb])
    have hh := while_true src (fun b=>b==some true) (recordBit src tmp backup)
      (d:=(q,S)) (by simp [hx,encNat,List.replicate_succ])
      (by simpa [hx,encNat,List.replicate_succ,U] using hb) ht
    rw [recordBits_append src tmp backup hst hsb htb] at hh
    simpa [List.replicate_succ,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

lemma recordField_exec (src tmp backup : K) (hst : src≠tmp) (hsb : src≠backup) (htb : tmp≠backup)
    (n : ℕ) (S : K→List Bool) (q : Option Bool) (tail : List Bool) (hx : S src=encNat n++tail) :
    (recordField src tmp backup).Exec (q,S)
      (none,recordBits src tmp backup S (encNat n) tail) (2*n+2) := by
  have h1 := recordField_loop_exec src tmp backup hst hsb htb n S q tail hx
  have h2 := recordBit_exec src tmp backup hst hsb htb
    (recordBits src tmp backup S (List.replicate n true) (false::tail)) (some false) false tail
    (by simp [recordBits,hst,hsb,Ne.symm hst,Ne.symm hsb])
  have hh := seq_exec _ _ h1 h2
  rw [recordBits_append src tmp backup hst hsb htb] at hh
  simpa [recordField,encNat,Nat.add_assoc] using hh

abbrev recordFields (src tmp backup : K) : ℕ → Code K
  | 0 => load none
  | r+1 => seq (recordField src tmp backup) (recordFields src tmp backup r)

lemma recordFields_exec (src tmp backup : K) (hst : src≠tmp) (hsb : src≠backup) (htb : tmp≠backup)
    (ns : List ℕ) (S : K→List Bool) (q : Option Bool) (tail : List Bool)
    (hx : S src=ns.flatMap encNat++tail) :
    (recordFields src tmp backup ns.length).Exec (q,S)
      (none,recordBits src tmp backup S (ns.flatMap encNat) tail)
      (2*(ns.flatMap encNat).length+1) := by
  induction ns generalizing S q with
  | nil =>
    have he : recordBits src tmp backup S [] tail=S := by
      funext k
      by_cases hks : k=src <;> by_cases hkt : k=tmp <;> by_cases hkb : k=backup <;>
        simp_all [recordBits]
    simp only [List.flatMap_nil,List.length_nil,Nat.mul_zero,Nat.zero_add]
    rw [he]
    exact load_exec none (q,S)
  | cons n ns ih =>
    let U := recordBits src tmp backup S (encNat n) (ns.flatMap encNat++tail)
    have h1 := recordField_exec src tmp backup hst hsb htb n S q (ns.flatMap encNat++tail)
      (by simpa [List.append_assoc] using hx)
    have h2 := ih U none (by simp [U,recordBits,hst,hsb,Ne.symm hst,Ne.symm hsb])
    have hh := seq_exec _ _ h1 h2
    rw [recordBits_append src tmp backup hst hsb htb] at hh
    simpa [recordFields,List.length_append,Main.Encoding.encNat_length,Nat.mul_add,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

abbrev recordTag (src tmp backup : K) : List (Code K) → Code K
  | [] => load none
  | P::Ps => ifPeek src (fun b=>b==some true)
      (seq (recordBit src tmp backup) (recordTag src tmp backup Ps))
      (seq (recordBit src tmp backup) P)

lemma recordTag_exec (src tmp backup : K) (hst : src≠tmp) (hsb : src≠backup) (htb : tmp≠backup)
    (Ps : List (Code K)) (j : ℕ) (hj : j<Ps.length) (S : K→List Bool) (q : Option Bool)
    (tail : List Bool) (hx : S src=encNat j++tail) (e : Data K) (t : ℕ)
    (hb : (Ps[j]'hj).Exec (none,recordBits src tmp backup S (encNat j) tail) e t) :
    (recordTag src tmp backup Ps).Exec (q,S) e (2*j+2+t) := by
  induction Ps generalizing j S q with
  | nil => simp at hj
  | cons P Ps ih =>
    cases j with
    | zero =>
      have hbit := recordBit_exec src tmp backup hst hsb htb S (some false) false tail (by simpa [encNat] using hx)
      have hh := seq_exec _ _ hbit hb
      have hout := ifPeek_false src (fun b=>b==some true) (seq (recordBit src tmp backup) (recordTag src tmp backup Ps)) (seq (recordBit src tmp backup) P) (d:=(q,S))
        (by simp [hx,encNat]) (by simpa [hx,encNat] using hh)
      simpa only [recordTag,Nat.mul_zero,Nat.zero_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hout
    | succ j =>
      let U := recordBits src tmp backup S [true] (encNat j++tail)
      have hbit := recordBit_exec src tmp backup hst hsb htb S (some true) true (encNat j++tail)
        (by simpa [encNat,List.replicate_succ] using hx)
      have hj' : j<Ps.length := by simpa using hj
      have he : recordBits src tmp backup U (encNat j) tail =
          recordBits src tmp backup S (encNat (j+1)) tail := by
        rw [recordBits_append src tmp backup hst hsb htb]
        rfl
      have hbody : (Ps[j]'hj').Exec (none,recordBits src tmp backup U (encNat j) tail) e t := by
        rw [he]
        exact hb
      have htail := ih j hj' U none (by simp [U,recordBits,hst,hsb,Ne.symm hst,Ne.symm hsb]) hbody
      have hh := seq_exec _ _ hbit htail
      have hout := ifPeek_true src (fun b=>b==some true) (seq (recordBit src tmp backup) (recordTag src tmp backup Ps)) (seq (recordBit src tmp backup) P) (d:=(q,S))
        (by simp [hx,encNat,List.replicate_succ])
        (by simpa [hx,encNat,List.replicate_succ,U] using hh)
      convert hout using 1 <;> ring

abbrev g2RecordBranches (src tmp backup : K) : List (Code K) :=
  (List.ofFn fun j : Fin 4=>recordFields src tmp backup (Main.RawEncoding.g2Table[j.val]?.getD 0))
abbrev recordG2 (src tmp backup : K) : Code K := recordTag src tmp backup (g2RecordBranches src tmp backup)

lemma recordG2_exec (src tmp backup : K) (hst : src≠tmp) (hsb : src≠backup) (htb : tmp≠backup)
    (i : Main.RawEncoding.Instruction) (hi : i.gate<4)
    (hw : i.wires.length=Main.RawEncoding.g2Table[i.gate]?.getD 0)
    (S : K→List Bool) (q : Option Bool) (tail : List Bool) (hx : S src=i.encode++tail) :
    (recordG2 src tmp backup).Exec (q,S)
      (none,recordBits src tmp backup S i.encode tail) (2*i.encode.length+1) := by
  let U := recordBits src tmp backup S (encNat i.gate) (i.wires.flatMap encNat++tail)
  have hfields := recordFields_exec src tmp backup hst hsb htb i.wires U none tail
    (by simp [U,recordBits,hst,hsb])
  rw [recordBits_append src tmp backup hst hsb htb] at hfields
  have hlen : i.gate<(g2RecordBranches src tmp backup).length := by simpa using hi
  have hb : ((g2RecordBranches src tmp backup)[i.gate]'hlen).Exec (none,U)
      (none,recordBits src tmp backup S i.encode tail) (2*(i.wires.flatMap encNat).length+1) := by
    simpa only [g2RecordBranches,List.getElem_ofFn,hw,Main.RawEncoding.Instruction.encode] using hfields
  have hh := recordTag_exec src tmp backup hst hsb htb (g2RecordBranches src tmp backup)
    i.gate hlen S q (i.wires.flatMap encNat++tail)
    (by simpa [Main.RawEncoding.Instruction.encode,List.append_assoc] using hx) _ _ hb
  simpa [recordG2,Main.RawEncoding.Instruction.encode,List.length_append,Main.Encoding.encNat_length,
    Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

end QMAPerfectCompleteness.Uniformity.StructuredStack.Code


