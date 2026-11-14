-- Prove2me | Definitions.Def_APFPaper1_Cont_prefix_countermodel_data
-- name    : APFPaper1_Cont_prefix_countermodel_data
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:06:57.080976+00:00
-- url     : https://prove2.me/theorems/2ffaa0e7-2f81-452a-a269-00a0a2af815f
-- title:
--   A two-letter word can meet whole budget while its prefix fails under supplied nonmonotone calibration
-- statement:
--   Word-length, execution and cost data for the reviewed counterexample to automatic prefix restriction. A two-fragment word has lower cost than its one-fragment prefix. The separate counterexample theorem proves the failure of prefix closure without a bill-monotonicity hypothesis. This definition bundle supplies the data only.
--
--   A two-letter word can meet whole budget while its prefix fails under supplied nonmonotone calibration. Premises: One-context Unit model; bills 2 at length1 and 0 otherwise; capacity1. Scope: Correct separation of definitions; not a physical calibration countermodel and not a refutation under prefix monotonicity.
--
--   **Representation and scope.** Correct separation of definitions; not a physical calibration countermodel and not a refutation under prefix monotonicity.
--
--   **Supplied data or hypotheses.** One-context Unit model; bills 2 at length1 and 0 otherwise; capacity1.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Reference/Ref_APFPaper1_Cont_prefix_countermodel.lean; Sib v15, SHA-256 45019c2b82de9baf9b53d839461b9516895ae70d54329ea28fd0ab93d1bf67c9. ['20-34: all model definitions', '36-53: three proofs', '10-11: physical-calibration disclaimer']

/-
REFERENCE ONLY. Not a Foundation Ledger node (standing rule 11: countermodels stay in reference missions).
DRAFT, not gated, not released.
name: APFPaper1.Continuation.Reference.prefix_restriction_not_automatic
purpose: shows that the bill-comparison hypothesis of C3 (Thm_APFPaper1_Cont_prefix_restriction) cannot be dropped.
model: one context; one fragment; every step allowed; the resource of a word is its length; the calibration
  charges 2 for a word of length one and 0 otherwise; capacity 1. The two-fragment word executes and has bill
  0, so it is in Cont. Its one-fragment initial segment has bill 2 > 1, so it is not. The same model shows the
  whole-word class and the hereditary class differ, and that Cont is inhabited.
what it does not show: nothing about physical resources. The calibration here is not monotone in any physical
  sense; the model only separates the two definitions.
-/
import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
namespace APFPaper1.Continuation.Reference
open APFPaper1.Continuation

/-- Number of fragments in a word. -/
def length {Context : Type} {Frag : Context → Context → Type} :
    {g h : Context} → Word Frag g h → Nat
  | _, _, Word.nil _ => 0
  | _, _, Word.cons _ w => length w + 1

abbrev F : Unit → Unit → Type := fun _ _ => Unit

def step : (g h : Unit) → F g h → Unit → Unit → Prop := fun _ _ _ _ _ => True
def resource : (g : Unit) → WordFrom F g → Nat := fun _ w => length w.2
noncomputable def calibration : Unit → Nat → NNReal := fun _ n => if n = 1 then 2 else 0
noncomputable def capacity : Unit → NNReal := fun _ => 1

def one : WordFrom F () := ⟨(), Word.single (g := ()) (h := ()) ()⟩
def two : WordFrom F () :=
  ⟨(), Word.cons (g := ()) (h := ()) (k := ()) () (Word.single (g := ()) (h := ()) ())⟩







end APFPaper1.Continuation.Reference


