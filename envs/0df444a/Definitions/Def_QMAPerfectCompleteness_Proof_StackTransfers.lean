-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_StackTransfers
-- name    : QMAPerfectCompleteness_Proof_StackTransfers
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:57:21.681521+00:00
-- url     : https://prove2.me/theorems/415d0e50-7ce5-465f-b2dc-c17eb4678531
-- title:
--   Finite stack transfer, copy and clearing
-- statement:
--   Defines shared-stack programs for moving, copying and clearing finite binary words. Execution bounds and framing identities describe reversal during transfer, restoration of copied sources and cleanup of temporary registers.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/StackTransfers.lean, retained declaration span lines 9–133.

/- Generated from Solutions.StackTransfers by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_StructuredStackCode
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Concrete shared-stack copying routines for unary circuit-generation registers. -/
open Turing StateTransition
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Uniformity.StructuredStack.Code
variable {K : Type} [DecidableEq K]

abbrev moveBody (src dst : K) : Code K := atomic
  (.pop src (fun _ b=>b) (.push dst (fun v=>v.getD false) .halt))
abbrev transfer (src dst : K) : Code K := whilePeek src Option.isSome (moveBody src dst)

lemma moveBody_exec (src dst : K) (h : src ≠ dst) (S : K → List Bool)
    (v : Option Bool) (b : Bool) (xs : List Bool) (hx : S src=b::xs) :
    (moveBody src dst).Exec (v,S)
      (some b,Function.update (Function.update S src xs) dst (b::S dst)) 1 := by
  have hh := atomic_exec (.pop src (fun _ b=>b) (.push dst (fun v=>v.getD false) .halt)) (v,S) rfl
  simpa [effect,TM2.stepAux,hx,h,Ne.symm h] using hh

/-- Move a complete stack onto another stack, reversing its order, and clear the scratch value. -/
theorem transfer_exec (src dst : K) (h : src ≠ dst) (xs : List Bool)
    (S : K → List Bool) (v : Option Bool) (hx : S src=xs) :
    (transfer src dst).Exec (v,S)
      (none,Function.update (Function.update S src []) dst (xs.reverse++S dst)) (2*xs.length+1) := by
  induction xs generalizing S v with
  | nil =>
    have hh := while_false src Option.isSome (moveBody src dst) (v,S) (by simp [hx])
    have hs : Function.update (Function.update S src []) dst (List.reverse [] ++ S dst)=S := by
      funext k
      by_cases hks : k=src <;> by_cases hkd : k=dst <;> simp_all
    rw [hs]
    simpa [hx] using hh
  | cons b xs ih =>
    let S' := Function.update (Function.update S src xs) dst (b::S dst)
    have hbody := moveBody_exec src dst h S (some b) b xs hx
    have htail := ih S' (some b) (by simp [S',h,Ne.symm h])
    have hh := while_true src Option.isSome (moveBody src dst)
      (d := (v,S)) (by simp [hx]) (by simpa [hx,S'] using hbody) htail
    have hs : Function.update (Function.update S' src []) dst (xs.reverse++S' dst) =
        Function.update (Function.update S src []) dst ((b::xs).reverse++S dst) := by
      funext k
      by_cases hks : k=src <;> by_cases hkd : k=dst <;>
        simp_all [S',List.reverse_cons,List.append_assoc]
    rw [hs] at hh
    simpa [List.length_cons,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

abbrev clearBody (src : K) : Code K := atomic (.pop src (fun _ b=>b) .halt)
abbrev clear (src : K) : Code K := whilePeek src Option.isSome (clearBody src)

theorem clear_exec (src : K) (xs : List Bool) (S : K → List Bool)
    (v : Option Bool) (hx : S src=xs) :
    (clear src).Exec (v,S) (none,Function.update S src []) (2*xs.length+1) := by
  induction xs generalizing S v with
  | nil =>
    have hh := while_false src Option.isSome (clearBody src) (v,S) (by simp [hx])
    have hs : Function.update S src [] = S := by
      funext k
      by_cases hk : k=src <;> simp_all
    rw [hs]
    simpa [hx] using hh
  | cons b xs ih =>
    let S' := Function.update S src xs
    have hbody : (clearBody src).Exec (some b,S) (some b,S') 1 := by
      simpa [effect,TM2.stepAux,hx,S'] using
        atomic_exec (.pop src (fun _ b=>b) .halt) (some b,S) rfl
    have htail := ih S' (some b) (by simp [S'])
    have hh := while_true src Option.isSome (clearBody src)
      (d := (v,S)) (by simp [hx]) (by simpa [hx] using hbody) htail
    simpa [S',Function.update_idem,List.length_cons,Nat.mul_add,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

abbrev copyBody (src dst tmp : K) : Code K := atomic
  (.pop src (fun _ b=>b) (.push dst (fun v=>v.getD false)
    (.push tmp (fun v=>v.getD false) .halt)))
abbrev copy (src dst tmp : K) : Code K :=
  seq (whilePeek src Option.isSome (copyBody src dst tmp)) (transfer tmp src)

lemma copyBody_exec (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (S : K → List Bool) (v : Option Bool) (b : Bool) (xs : List Bool) (hx : S src=b::xs) :
    (copyBody src dst tmp).Exec (v,S)
      (some b,Function.update (Function.update (Function.update S src xs)
        dst (b::S dst)) tmp (b::S tmp)) 1 := by
  have hh := atomic_exec (.pop src (fun _ b=>b) (.push dst (fun v=>v.getD false)
    (.push tmp (fun v=>v.getD false) .halt))) (v,S) rfl
  simpa [effect,TM2.stepAux,hx,hsd,hst,hdt,Ne.symm hsd,Ne.symm hst,Ne.symm hdt] using hh

lemma copy_loop_exec (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (xs : List Bool) (S : K → List Bool) (v : Option Bool) (hx : S src=xs) :
    (whilePeek src Option.isSome (copyBody src dst tmp)).Exec (v,S)
      (none,Function.update (Function.update (Function.update S src [])
        dst (xs.reverse++S dst)) tmp (xs.reverse++S tmp)) (2*xs.length+1) := by
  induction xs generalizing S v with
  | nil =>
    have hh := while_false src Option.isSome (copyBody src dst tmp) (v,S) (by simp [hx])
    have hs : Function.update (Function.update (Function.update S src [])
        dst (([] : List Bool).reverse++S dst)) tmp ([].reverse++S tmp)=S := by
      funext k
      by_cases hks : k=src <;> by_cases hkd : k=dst <;> by_cases hkt : k=tmp <;> simp_all
    rw [hs]
    simpa [hx] using hh
  | cons b xs ih =>
    let S' := Function.update (Function.update (Function.update S src xs) dst (b::S dst)) tmp (b::S tmp)
    have hbody := copyBody_exec src dst tmp hsd hst hdt S (some b) b xs hx
    have htail := ih S' (some b) (by simp [S',hsd,hst,Ne.symm hsd,Ne.symm hst])
    have hh := while_true src Option.isSome (copyBody src dst tmp)
      (d := (v,S)) (by simp [hx]) (by simpa [hx,S'] using hbody) htail
    have hs : Function.update (Function.update (Function.update S' src [])
        dst (xs.reverse++S' dst)) tmp (xs.reverse++S' tmp) =
        Function.update (Function.update (Function.update S src [])
          dst ((b::xs).reverse++S dst)) tmp ((b::xs).reverse++S tmp) := by
      funext k
      by_cases hks : k=src <;> by_cases hkd : k=dst <;> by_cases hkt : k=tmp <;>
        simp_all [S',List.reverse_cons,List.append_assoc]
    rw [hs] at hh
    simpa [List.length_cons,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- Copy a stack while restoring the original and clearing the temporary stack. -/
theorem copy_exec (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (xs : List Bool) (S : K → List Bool) (v : Option Bool) (hx : S src=xs) (ht : S tmp=[]) :
    (copy src dst tmp).Exec (v,S)
      (none,Function.update S dst (xs.reverse++S dst)) (4*xs.length+2) := by
  let S' := Function.update (Function.update (Function.update S src [])
    dst (xs.reverse++S dst)) tmp xs.reverse
  have h₁ := copy_loop_exec src dst tmp hsd hst hdt xs S v hx
  have h₂ := transfer_exec tmp src (Ne.symm hst) xs.reverse S' none (by simp [S'])
  have hh := seq_exec _ _ (by simpa [ht,S'] using h₁) h₂
  have hs : Function.update (Function.update S' tmp []) src (xs.reverse.reverse++S' src) =
      Function.update S dst (xs.reverse++S dst) := by
    funext k
    by_cases hks : k=src <;> by_cases hkd : k=dst <;> by_cases hkt : k=tmp <;>
      simp_all [S']
  rw [hs] at hh
  convert hh using 1 <;> simp only [List.length_reverse] <;> omega

end QMAPerfectCompleteness.Uniformity.StructuredStack.Code


