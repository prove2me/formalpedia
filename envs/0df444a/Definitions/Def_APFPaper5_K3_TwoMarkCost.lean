-- Prove2me | Definitions.Def_APFPaper5_K3_TwoMarkCost
-- name    : APFPaper5_K3_TwoMarkCost
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:13:12.312834+00:00
-- url     : https://prove2.me/theorems/80efec35-68e0-4fd3-82a3-c225d4d73762
-- title:
--   Frobenius quadratic cost and cross term on two-by-two real arrays
-- statement:
--   Defines array addition, sum-of-squares cost and entrywise bilinear cross term.
--
--   **Representation and scope.** Faithful to its exact supplied mathematical definitions under the stated exposure; original physical-object correspondence is not established.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_TwoMarkCost.lean; Sib v15, SHA-256 59b9b3284acdf5f98c63a2885f4e740dff36bdcfa7232dc23bba2fb06f2561cf. P5:271-350

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_TwoMarkCost
title: A cost on the arrays of the two-mark model: the sum of squares, with its cross term
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_TwoMarkModel; Paper 5 Supplement v7.33:271-350 (quadratic ledger, polarization).
standing: part of the supplied MODEL. Not ledger data; no declared input produces it.
statement: add is the entrywise sum of two arrays. sqCost is the sum of the squares of the entries. crossTerm
 is the entrywise product summed.
-/
import Definitions.Def_APFPaper5_K3_TwoMarkModel

set_option autoImplicit false
namespace APFPaper5.K3

/-- Two arrays put together. -/
def add (x y : M2) : M2 := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩

/-- The sum-of-squares cost of an array. -/
def sqCost (x : M2) : ℝ := x.a * x.a + x.b * x.b + x.c * x.c + x.d * x.d

/-- The cross term of that cost. -/
def crossTerm (x y : M2) : ℝ := x.a * y.a + x.b * y.b + x.c * y.c + x.d * y.d

end APFPaper5.K3


