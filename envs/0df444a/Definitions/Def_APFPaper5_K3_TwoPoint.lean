-- Prove2me | Definitions.Def_APFPaper5_K3_TwoPoint
-- name    : APFPaper5_K3_TwoPoint
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:11:22.745992+00:00
-- url     : https://prove2.me/theorems/31c367d7-d303-49a9-9b44-5f855a9f5895
-- title:
--   Candidate two-point transitivity and square-root-of-turn conditions
-- statement:
--   Defines TwoPoint and TurnsHaveHalves on supplied marks, scores and maps.
--
--   **Representation and scope.** Faithful to its exact supplied mathematical definitions under the stated exposure; original physical-object correspondence is not established.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_TwoPoint.lean; Sib v15, SHA-256 a210e9e221171ddbf621262ef0d0d016065ac9dc650780ffd917a551a828c2bf. P5:3037-3056

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_TwoPoint
title: Two candidate clauses about turns: turns carry any pair of marks to any pair with the same number, and every turn has a half
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: The test announced in NOTE_derivation_pass_5_2026-11-12: does "the exchange of two marks is a turn with
 halves" follow from what has been adopted.
standing: CANDIDATE clauses, defined so that the test can be stated. Neither is adopted. Neither is a declared
 input.
statement: TwoPoint Marks B Adm says that whenever two pairs of marks have the same score, some admissible turn
 carries the first pair to the second. TurnsHaveHalves Adm says every admissible turn is an admissible turn
 done twice.
-/
import Mathlib.Data.Real.Basic

set_option autoImplicit false
namespace APFPaper5.K3

universe u
variable {V : Type u}

/-- Admissible turns carry any pair of marks to any pair of marks with the same score. -/
def TwoPoint (Marks : Set V) (B : V → V → ℝ) (Adm : Set (V → V)) : Prop :=
  ∀ p q p' q' : V, p ∈ Marks → q ∈ Marks → p' ∈ Marks → q' ∈ Marks → B p q = B p' q' →
    ∃ T ∈ Adm, T p = p' ∧ T q = q'

/-- Every admissible turn is an admissible turn done twice. -/
def TurnsHaveHalves (Adm : Set (V → V)) : Prop :=
  ∀ T ∈ Adm, ∃ H ∈ Adm, ∀ v : V, H (H v) = T v

end APFPaper5.K3


