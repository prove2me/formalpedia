-- Prove2me | Definitions.Def_APFPaper5_K3_Preservation
-- name    : APFPaper5_K3_Preservation
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:10:29.162448+00:00
-- url     : https://prove2.me/theorems/60f9f242-c905-4729-abe3-4e28c6cb7117
-- title:
--   Conditional nonincrease of cost under admitted turns
-- statement:
--   Defines TurnsNeverRaiseCost for a supplied set of maps and real-valued cost.
--
--   **Representation and scope.** Faithful to its exact supplied mathematical definitions under the stated exposure; original physical-object correspondence is not established.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_Preservation.lean; Sib v15, SHA-256 85169c5723edf91f3d488d5f84a0588e2d9d9ca33f21ccf46393a8d42148dc7e. P5:1660-1679

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_Preservation
title: The cost clause of preservation: no admissible turn raises cost
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Author's ruling of 2026-11-12 ("Proceed as advised"), adding to PRESERVATION the clause "no admissible
 turn raises cost".
standing: a NAMED HYPOTHESIS of the K layer. Not a declared input; a derivation is owed.
statement: TurnsNeverRaiseCost Adm cost says that cost after an admissible turn is at most cost before.
-/
import Mathlib.Data.Real.Basic

set_option autoImplicit false
namespace APFPaper5.K3

universe u
variable {S : Type u}

/-- No admissible turn raises cost. -/
def TurnsNeverRaiseCost (Adm : Set (S → S)) (cost : S → ℝ) : Prop :=
  ∀ f ∈ Adm, ∀ s : S, cost (f s) ≤ cost s

end APFPaper5.K3


