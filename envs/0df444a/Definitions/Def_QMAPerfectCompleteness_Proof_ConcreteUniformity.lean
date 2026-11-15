-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Proof_ConcreteUniformity
-- name    : QMAPerfectCompleteness_Proof_ConcreteUniformity
-- status  : Definition
-- author  : @Dorian Rudolph
-- created : 2026-11-14T14:45:31.162034+00:00
-- url     : https://prove2.me/theorems/b9b40c37-d63f-4a86-9821-15a7e69cb18d
-- title:
--   Literal finite stack-push statements
-- statement:
--   Defines a finite statement that pushes a specified list of symbols before a continuation. Its execution identity gives the resulting stack contents and is used when constructing concrete compiler machines.
-- source:
--   Formalization auxiliary for ~/research/qma1z/main.tex, the uniform circuit implementation supporting Section 3.3 and the proof of Theorem 1.1. Original Lean source: commit bbe19efbde567e5c8f7fe21655fd0c4da3573e4d, Solutions/ConcreteUniformity.lean, retained declaration span lines 13–24.

/- Generated from Solutions.ConcreteUniformity by authoritative Stage-2 skeleton subtraction.
Original explanatory text, declaration names and scoped commands are retained.
Only selected proof cuts, import rewrites and fact-indexed platform edits are applied. -/
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QMAPerfectCompleteness_Proof_PolyTimeComposition



/-! Specialized compiler closure: add a fixed code prefix directly to the source machine's
halting statements. This constructs the exact machine needed for this operation and does not
use a general polynomial-time composition theorem. -/
open Turing StateTransition

namespace QMAPerfectCompleteness.Uniformity

namespace Statement
variable {K Λ σ : Type} {Γ : K → Type}

def pushMany (k : K) : List (Γ k) → TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ σ
  | [], q => q
  | a :: s, q => pushMany k s (.push k (fun _ => a) q)

theorem stepAux_pushMany [DecidableEq K] (k : K) (s : List (Γ k))
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    TM2.stepAux (pushMany k s q) v S =
      TM2.stepAux q v (Function.update S k (s ++ S k)) := by
  induction s generalizing q with
  | nil => simp [pushMany]
  | cons a s ih =>
    simp [pushMany, ih, TM2.stepAux, Function.update_idem]

end Statement































end QMAPerfectCompleteness.Uniformity


