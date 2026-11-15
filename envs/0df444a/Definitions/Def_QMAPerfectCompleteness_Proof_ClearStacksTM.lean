-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_ClearStacksTM
-- name    : QMAPerfectCompleteness_Proof_ClearStacksTM
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:58:42.879518+00:00
-- url     : https://prove2.me/theorems/2b02b0b6-e884-41e2-bae5-6ecba0f76498
-- title:
--   Clearing a finite stack bank
-- statement:
--   Defines a structured stack program that clears a specified finite list of registers and preserves all others. The retained execution bound is the sum of the individual stack-clearing bounds.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/ClearStacksTM.lean, retained declaration span lines 7–35.

/- Generated from Solutions.ClearStacksTM by authoritative Stage-2 skeleton subtraction.
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


set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace QMAPerfectCompleteness.Uniformity.StructuredStack.Code
variable {K : Type} [DecidableEq K]

def erased (S : K→List Bool) (ks : List K) : K→List Bool := fun k=>if k∈ks then [] else S k
abbrev clearList : List K→ Code K
  | []=>load none
  | k::ks=>seq (clear k) (clearList ks)

def clearListTime (S : K→List Bool) (ks : List K) : ℕ :=
  2*(ks.map (fun k=>(S k).length)).sum+ks.length+1
lemma clearList_exec (ks : List K) (S : K→List Bool) (q : Option Bool) :
    (clearList ks).Exec (q,S) (none,erased S ks) (clearListTime S ks) := by
  induction ks generalizing S q with
  | nil=>
    have he : erased S []=S := by funext k; simp [erased]
    rw [he]
    exact load_exec none (q,S)
  | cons k ks ih=>
    have h1:=clear_exec k (S k) S q rfl
    have h2:=ih (Function.update S k []) none
    have hh:=seq_exec _ _ h1 h2
    have he : erased (Function.update S k []) ks=erased S (k::ks) := by
      funext l
      by_cases hl : l=k <;> by_cases hm : l∈ks <;> simp_all [erased]
    rw [he] at hh
    apply exec_mono _ hh
    have hs : (ks.map (fun l=>(Function.update S k [] l).length)).sum≤(ks.map (fun l=>(S l).length)).sum := by
      apply List.sum_le_sum
      intro l hl
      by_cases hk : l=k <;> simp [hk]
    simp only [clearListTime,List.map_cons,List.sum_cons,List.length_cons] at ⊢
    omega
end QMAPerfectCompleteness.Uniformity.StructuredStack.Code


