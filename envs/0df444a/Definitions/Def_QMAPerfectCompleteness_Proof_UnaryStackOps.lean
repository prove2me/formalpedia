-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_UnaryStackOps
-- name    : QMAPerfectCompleteness_Proof_UnaryStackOps
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:58:43.184198+00:00
-- url     : https://prove2.me/theorems/384c61fd-5358-423b-af1f-9fa1a124e1dd
-- title:
--   Primitive unary arithmetic on shared stacks
-- statement:
--   Defines finite shared-register programs for constants, truncated subtraction and halving. Their execution identities state the resulting unary values, cleared temporary operands and preservation of other stack contents.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/UnaryStackOps.lean, retained declaration span lines 8–131.

/- Generated from Solutions.UnaryStackOps by authoritative Stage-2 skeleton subtraction.
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



/-! Unary arithmetic performed by finite structured TM2 programs on shared registers. -/
open Turing StateTransition
set_option backward.isDefEq.respectTransparency false
namespace QMAPerfectCompleteness.Uniformity.StructuredStack.Code
variable {K : Type} [DecidableEq K]
abbrev unary (n : ℕ) : List Bool := List.replicate n true

abbrev constantStmt (dst : K) (n : ℕ) : TM2.Stmt (fun _ : K=>Bool) Unit (Option Bool) :=
  Nat.rec .halt (fun _ q=>.push dst (fun _=>true) q) n
abbrev constant (dst : K) (n : ℕ) : Code K := atomic (constantStmt dst n)

lemma constantStmt_effect (dst : K) (n : ℕ) (v : Option Bool) (S : K → List Bool) :
    TM2.stepAux (constantStmt dst n) v S =
      ⟨none,v,Function.update S dst (unary n++S dst)⟩ := by
  induction n generalizing S with
  | zero => simp [constantStmt,TM2.stepAux,Function.update_eq_self]
  | succ n ih =>
    simp only [constantStmt,TM2.stepAux]
    rw [ih]
    congr 1
    funext k
    by_cases hk : k=dst
    · subst k
      simp only [Function.update_self,unary,List.replicate_succ,List.cons_append]
      change List.replicate n true ++ ([true] ++ S dst) = _
      rw [← List.append_assoc,← List.replicate_succ',List.replicate_succ,List.cons_append]
    · simp [hk]

lemma constant_exec (dst : K) (n : ℕ) (v : Option Bool) (S : K → List Bool) :
    (constant dst n).Exec (v,S) (v,Function.update S dst (unary n++S dst)) 1 := by
  have hh := atomic_exec (constantStmt dst n) (v,S) (by rw [constantStmt_effect])
  simpa [effect,constantStmt_effect] using hh

abbrev subtractBody (src dst : K) : Code K := atomic
  (.pop src (fun _ b=>b) (.pop dst (fun _ b=>b) .halt))
abbrev subtract (src dst : K) : Code K := whilePeek src Option.isSome (subtractBody src dst)

lemma subtractBody_exec (src dst : K) (h : src ≠ dst) (S : K → List Bool)
    (v : Option Bool) (n m : ℕ) (hs : S src=unary (n+1)) (hd : S dst=unary m) :
    (subtractBody src dst).Exec (v,S)
      ((unary m).head?,Function.update (Function.update S src (unary n)) dst (unary (m-1))) 1 := by
  have hh := atomic_exec (.pop src (fun _ b=>b) (.pop dst (fun _ b=>b) .halt)) (v,S) rfl
  simpa [effect,TM2.stepAux,hs,hd,h,Ne.symm h,unary,List.replicate_succ] using hh

theorem subtract_exec (src dst : K) (h : src ≠ dst) (n m : ℕ)
    (S : K → List Bool) (v : Option Bool) (hs : S src=unary n) (hd : S dst=unary m) :
    (subtract src dst).Exec (v,S)
      (none,Function.update (Function.update S src []) dst (unary (m-n))) (2*n+1) := by
  induction n generalizing m S v with
  | zero =>
    have hh := while_false src Option.isSome (subtractBody src dst) (v,S) (by simp [hs])
    have he : Function.update (Function.update S src []) dst (unary (m-0))=S := by
      funext k
      by_cases hks : k=src <;> by_cases hkd : k=dst <;> simp_all
    rw [he]
    simpa [hs] using hh
  | succ n ih =>
    let S' := Function.update (Function.update S src (unary n)) dst (unary (m-1))
    have hb := subtractBody_exec src dst h S (some true) n m hs hd
    have ht := ih (m-1) S' (unary m).head? (by simp [S',h]) (by simp [S'])
    have hh := while_true src Option.isSome (subtractBody src dst)
      (d := (v,S)) (by simp [hs,unary,List.replicate_succ])
      (by simpa [S',hs,unary,List.replicate_succ] using hb) ht
    have he : Function.update (Function.update S' src []) dst (unary (m-1-n)) =
        Function.update (Function.update S src []) dst (unary (m-(n+1))) := by
      have ha : m-1-n=m-(n+1) := by omega
      funext k
      by_cases hks : k=src <;> by_cases hkd : k=dst <;> simp_all [S']
    rw [he] at hh
    convert hh using 1 <;> omega

abbrev halfBody (src dst : K) : Code K := atomic
  (.pop src (fun _ b=>b) (.pop src (fun _ b=>b)
    (.branch Option.isSome (.push dst (fun _=>true) .halt) .halt)))
abbrev half (src dst : K) : Code K := whilePeek src Option.isSome (halfBody src dst)

lemma halfBody_one (src dst : K) (S : K → List Bool) (v : Option Bool) (hs : S src=unary 1) :
    (halfBody src dst).Exec (v,S) (none,Function.update S src []) 1 := by
  have hh := atomic_exec (.pop src (fun _ b=>b) (.pop src (fun _ b=>b)
    (.branch Option.isSome (.push dst (fun _=>true) .halt) .halt))) (v,S) (by simp [TM2.stepAux,hs,unary])
  simpa [effect,TM2.stepAux,hs,unary] using hh

lemma halfBody_two (src dst : K) (h : src ≠ dst) (S : K → List Bool)
    (v : Option Bool) (n : ℕ) (hs : S src=unary (n+2)) :
    (halfBody src dst).Exec (v,S)
      (some true,Function.update (Function.update S src (unary n)) dst (true::S dst)) 1 := by
  have hh := atomic_exec (.pop src (fun _ b=>b) (.pop src (fun _ b=>b)
    (.branch Option.isSome (.push dst (fun _=>true) .halt) .halt))) (v,S) (by simp [TM2.stepAux,hs,unary,List.replicate_succ])
  simpa [effect,TM2.stepAux,hs,unary,List.replicate_succ,h,Ne.symm h] using hh

/-- Divide a unary register by two while accumulating its quotient on another stack. -/
theorem half_exec (src dst : K) (h : src ≠ dst) (n : ℕ)
    (S : K → List Bool) (v : Option Bool) (hs : S src=unary n) :
    (half src dst).Exec (v,S)
      (none,Function.update (Function.update S src []) dst (unary (n/2)++S dst)) (2*n+1) := by
  induction n using Nat.twoStepInduction generalizing S v with
  | zero =>
    have hh := while_false src Option.isSome (halfBody src dst) (v,S) (by simp [hs])
    have he : Function.update (Function.update S src []) dst (unary (0/2)++S dst)=S := by
      funext k
      by_cases hks : k=src <;> by_cases hkd : k=dst <;> simp_all
    rw [he]
    simpa [hs] using hh
  | one =>
    let S' := Function.update S src []
    have hb := halfBody_one src dst S (some true) hs
    have ht := while_false src Option.isSome (halfBody src dst) (none,S') (by simp [S'])
    have hh := while_true src Option.isSome (halfBody src dst) (d := (v,S))
      (by simp [hs,unary]) (by simpa [hs,S',unary] using hb) ht
    have he : Function.update (Function.update S src []) dst (unary (1/2)++S dst)=S' := by
      funext k
      by_cases hks : k=src <;> by_cases hkd : k=dst <;> simp_all [S']
    rw [he]
    simpa [S'] using hh
  | more n ih _ =>
    let S' := Function.update (Function.update S src (unary n)) dst (true::S dst)
    have hb := halfBody_two src dst h S (some true) n hs
    have ht := ih S' (some true) (by simp [S',h])
    have hh := while_true src Option.isSome (halfBody src dst) (d := (v,S))
      (by simp [hs,unary,List.replicate_succ])
      (by simpa [S',hs,unary,List.replicate_succ] using hb) ht
    have he : Function.update (Function.update S' src []) dst (unary (n/2)++S' dst) =
        Function.update (Function.update S src []) dst (unary ((n+2)/2)++S dst) := by
      have ha : (n+2)/2=n/2+1 := by omega
      funext k
      by_cases hks : k=src <;> by_cases hkd : k=dst <;>
        simp_all [S',unary,List.replicate_add,List.append_assoc]
    rw [he] at hh
    exact exec_mono _ hh (by omega)

end QMAPerfectCompleteness.Uniformity.StructuredStack.Code


