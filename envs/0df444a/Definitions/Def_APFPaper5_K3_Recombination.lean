-- Prove2me | Definitions.Def_APFPaper5_K3_Recombination
-- name    : APFPaper5_K3_Recombination
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:10:35.888198+00:00
-- url     : https://prove2.me/theorems/bb67b7bd-71e7-485f-a870-9b9110bf89e2
-- title:
--   Cost of a weighted recombination in a supplied real module
-- statement:
--   Defines recombinationRecord cost a b x y as cost(a • x + b • y).
--
--   **Representation and scope.** Faithful to its exact supplied mathematical definitions under the stated exposure; original physical-object correspondence is not established.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_Recombination.lean; Sib v15, SHA-256 8897342e88f9fa24b9266c2776ada89de6821f4617017469b72cac6023459636. P5:1809-1832;293-350

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_Recombination
title: The recombination record of two held components: the cost of a weighted combination of them
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:1808-1832 (Global-phase kernel theorem; "relative orientation remains
 represented whenever it changes a later recombination record. Only the diagonal common action is
 record-null"). Author's direction of 2026-11-13: follow the Supplement's route.
standing: a DEFINITION on a supplied cost of combinations. It reads a record as the cost of recombining two
 components. That every record is of this kind is not claimed.
statement: recombinationRecord cost a b x y is cost (a • x + b • y).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Defs

set_option autoImplicit false
namespace APFPaper5.K3

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The cost of recombining two held components with real weights. -/
def recombinationRecord (cost : V → ℝ) (a b : ℝ) (x y : V) : ℝ := cost (a • x + b • y)

end APFPaper5.K3


