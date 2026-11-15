-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_UnaryMetadataArithmetic
-- name    : QMAPerfectCompleteness_Proof_UnaryMetadataArithmetic
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T15:00:53.793548+00:00
-- url     : https://prove2.me/theorems/2768743f-70a4-4f8c-86cc-537ebdd31263
-- title:
--   Unary multiplication and even rounding
-- statement:
--   Defines preserved-source multiplication-addition and even-rounding programs for the cyclic serializer metadata. Their execution bounds and arithmetic identities support computation of the index-register width without assuming a general function-composition theorem.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/UnaryMetadataArithmetic.lean, retained declaration span lines 11–114.

/- Generated from Solutions.UnaryMetadataArithmetic by authoritative Stage-2 skeleton subtraction.
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
import Definitions.Def_QMAPerfectCompleteness_Proof_UnaryStackOps
import Definitions.Def_QMAPerfectCompleteness_Proof_VerifierEncoding

/- Namespace registrations retained from original proof-only imports. -/
namespace QMAPerfectCompleteness.Main.DiagonalProof
end QMAPerfectCompleteness.Main.DiagonalProof
namespace QMAPerfectCompleteness.Uniformity.Expansion
end QMAPerfectCompleteness.Uniformity.Expansion



/-! Preserved-source unary multiplication and even rounding for cyclic compiler metadata. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Turing StateTransition
namespace QMAPerfectCompleteness.Uniformity.StructuredStack.Code
variable {K : Type} [DecidableEq K]

abbrev multiplyAdd (it src dst tmp : K) : Code K :=
  whilePeek it Option.isSome (seq (pop it) (copy src dst tmp))

/-- Consume the iterator, preserve the multiplicand, and add their product to the destination. -/
theorem multiplyAdd_exec (it src dst tmp : K)
    (his : it≠src) (hid : it≠dst) (hit : it≠tmp)
    (hsd : src≠dst) (hst : src≠tmp) (hdt : dst≠tmp)
    (a b : ℕ) (S : K→List Bool) (v : Option Bool)
    (hi : S it=unary a) (hs : S src=unary b) (ht : S tmp=[]) :
    (multiplyAdd it src dst tmp).Exec (v,S)
      (none,Function.update (Function.update S it []) dst (unary (a*b)++S dst))
      (a*(4*b+4)+1) := by
  induction a generalizing S v with
  | zero =>
    have hh := while_false it Option.isSome (seq (pop it) (copy src dst tmp)) (v,S) (by simp [hi,unary])
    have he : Function.update (Function.update S it []) dst (unary (0*b)++S dst)=S := by
      funext k
      by_cases hki : k=it <;> by_cases hkd : k=dst <;> simp_all [unary]
    rw [he]
    simpa [multiplyAdd,hi,unary] using hh
  | succ a ih =>
    let U := Function.update S it (unary a)
    let W := Function.update U dst (unary b++S dst)
    have hpop : (pop it).Exec (some true,S) (some true,U) 1 := by
      simpa [U,hi,unary,List.replicate_succ] using pop_exec it (some true,S)
    have hcopy : (copy src dst tmp).Exec (some true,U) (none,W) (4*b+2) := by
      have hh := copy_exec src dst tmp hsd hst hdt (unary b) U (some true)
        (by simp [U,Ne.symm his,hs]) (by simp [U,Ne.symm hit,ht])
      simpa [U,W,unary,List.reverse_replicate,hid,Ne.symm hid] using hh
    have hbody := seq_exec _ _ hpop hcopy
    have htail := ih W none (by simp [W,U,hid])
      (by simp [W,U,hsd,Ne.symm his,hs])
      (by simp [W,U,Ne.symm hdt,Ne.symm hit,ht])
    have hh := while_true it Option.isSome (seq (pop it) (copy src dst tmp))
      (d := (v,S)) (by simp [hi,unary,List.replicate_succ])
      (by simpa [hi,unary,List.replicate_succ] using hbody) htail
    have he : Function.update (Function.update W it []) dst (unary (a*b)++W dst) =
        Function.update (Function.update S it []) dst (unary ((a+1)*b)++S dst) := by
      funext k
      by_cases hki : k=it <;> by_cases hkd : k=dst <;>
        simp_all [W,U,unary,Nat.add_mul,List.replicate_add,List.append_assoc,-List.replicate_append_replicate]
    rw [he] at hh
    convert hh using 1 <;> ring

abbrev doubleMoveBody (src dst : K) : Code K := atomic
  (.pop src (fun _ b=>b) (.push dst (fun _=>true) (.push dst (fun _=>true) .halt)))
abbrev doubleMove (src dst : K) : Code K := whilePeek src Option.isSome (doubleMoveBody src dst)

theorem doubleMove_exec (src dst : K) (hsd : src≠dst) (n : ℕ)
    (S : K→List Bool) (v : Option Bool) (hs : S src=unary n) :
    (doubleMove src dst).Exec (v,S)
      (none,Function.update (Function.update S src []) dst (unary (2*n)++S dst)) (2*n+1) := by
  induction n generalizing S v with
  | zero =>
    have hh := while_false src Option.isSome (doubleMoveBody src dst) (v,S) (by simp [hs,unary])
    have he : Function.update (Function.update S src []) dst (unary (2*0)++S dst)=S := by
      funext k
      by_cases hks : k=src <;> by_cases hkd : k=dst <;> simp_all [unary]
    rw [he]
    simpa [doubleMove,hs,unary] using hh
  | succ n ih =>
    let U := Function.update (Function.update S src (unary n)) dst (true::true::S dst)
    have hbody : (doubleMoveBody src dst).Exec (some true,S) (some true,U) 1 := by
      have hh := atomic_exec (.pop src (fun _ b=>b) (.push dst (fun _=>true) (.push dst (fun _=>true) .halt)))
        (some true,S) rfl
      simpa [effect,TM2.stepAux,U,hs,unary,List.replicate_succ,hsd,Ne.symm hsd,Function.update_idem] using hh
    have htail := ih U (some true) (by simp [U,hsd])
    have hh := while_true src Option.isSome (doubleMoveBody src dst)
      (d := (v,S)) (by simp [hs,unary,List.replicate_succ])
      (by simpa [hs,unary,List.replicate_succ] using hbody) htail
    have he : Function.update (Function.update U src []) dst (unary (2*n)++U dst) =
        Function.update (Function.update S src []) dst (unary (2*(n+1))++S dst) := by
      funext k
      by_cases hks : k=src <;> by_cases hkd : k=dst <;>
        simp_all [U,unary,Nat.mul_add,List.replicate_add,List.append_assoc,-List.replicate_append_replicate]
    rw [he] at hh
    convert hh using 1 <;> omega

abbrev roundEven (src tmp : K) : Code K := seq (push src true) (seq (half src tmp) (doubleMove tmp src))

lemma roundEven_arithmetic (n : ℕ) : n+n%2=2*((n+1)/2) := by omega

/-- The least even integer at least n, with the temporary register restored. -/
theorem roundEven_exec (src tmp : K) (hst : src≠tmp) (n : ℕ)
    (S : K→List Bool) (v : Option Bool) (hs : S src=unary n) (ht : S tmp=[]) :
    (roundEven src tmp).Exec (v,S) (none,Function.update S src (unary (n+n%2))) (4*n+7) := by
  let U := Function.update S src (unary (n+1))
  let W := Function.update (Function.update S src []) tmp (unary ((n+1)/2))
  have h1 : (push src true).Exec (v,S) (v,U) 1 := by
    simpa [U,hs,unary,List.replicate_succ] using push_exec src true (v,S)
  have h2 : (half src tmp).Exec (v,U) (none,W) (2*(n+1)+1) := by
    have hh := half_exec src tmp hst (n+1) U v (by simp [U])
    simpa [U,W,Ne.symm hst,ht] using hh
  have h3 := doubleMove_exec tmp src (Ne.symm hst) ((n+1)/2) W none (by simp [W])
  have hh := seq_exec _ _ h1 (seq_exec _ _ h2 h3)
  have he : Function.update (Function.update W tmp []) src (unary (2*((n+1)/2))++W src) =
      Function.update S src (unary (n+n%2)) := by
    funext k
    by_cases hks : k=src <;> by_cases hkt : k=tmp <;>
      simp_all [W,roundEven_arithmetic]
  rw [he] at hh
  apply exec_mono _ hh
  have hd : (n+1)/2 ≤ n+1 := Nat.div_le_self _ _
  omega

end QMAPerfectCompleteness.Uniformity.StructuredStack.Code


