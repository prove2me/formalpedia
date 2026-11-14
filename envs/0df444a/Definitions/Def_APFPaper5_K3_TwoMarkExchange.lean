-- Prove2me | Definitions.Def_APFPaper5_K3_TwoMarkExchange
-- name    : APFPaper5_K3_TwoMarkExchange
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:13:17.609295+00:00
-- url     : https://prove2.me/theorems/3e2028c3-65a7-4f73-a0ff-2e03fe7b0b5a
-- title:
--   Mirror and slanted idempotent formulas in the real-array model
-- statement:
--   Defines mirror(u,v) and slantMark(t).
--
--   **Representation and scope.** Faithful to its exact supplied mathematical definitions under the stated exposure; original physical-object correspondence is not established.
--
--   **Claim boundaries.** K3-07
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_TwoMarkExchange.lean; Sib v15, SHA-256 6d23178780760fe006ca58b558b213289f673986db3a91bd92ee0fda9d48493c. P5:3037-3056;P1:6276-6280

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_TwoMarkExchange
title: Two more arrays in the two-mark model: the mirror that exchanges the marks, and a slanted mark
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_TwoMarkModel.
standing: part of the supplied MODEL. Not ledger data; no declared input produces it.
statement: mirror u v is the reflection across the line midway between the fixed mark and the mark along
 (u, v). slantMark t is a repeatable array that is never its own transpose
 (Thm_APFPaper5_K3_two_mark_range, slantMark_not_selfReverse).
-/
import Definitions.Def_APFPaper5_K3_TwoMarkModel

set_option autoImplicit false
namespace APFPaper5.K3

/-- The reflection that exchanges the fixed mark and the mark along `(u, v)`. -/
def mirror (u v : ℝ) : M2 := ⟨u, v, v, -u⟩

/-- A slanted repeatable mark. -/
def slantMark (t : ℝ) : M2 := ⟨t, 1, t * (1 - t), 1 - t⟩

end APFPaper5.K3


