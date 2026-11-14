-- Prove2me | Definitions.Def_APFPaper5_K3_TwoComponents
-- name    : APFPaper5_K3_TwoComponents
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:11:11.340809+00:00
-- url     : https://prove2.me/theorems/59950752-99db-4810-97ae-f2b0a6dd543c
-- title:
--   Supplied two-component real model with quadratic records and turns
-- statement:
--   Defines Held2, common and relative turn formulas, four records, two cross terms and total negation.
--
--   **Representation and scope.** Faithful to its exact supplied mathematical definitions under the stated exposure; original physical-object correspondence is not established.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_TwoComponents.lean; Sib v15, SHA-256 aa94b846ccb21c5a8ddd6191c8b3c1f2549fe1b2318694a2257241bbb1af8f2d. P5:1621-1649;1809-1832;293-350

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_TwoComponents
title: Two held components, each with a value and a rate; the common turn, the turn of one component, and the records
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:1621-1647 (the carrier of one held component has two coordinates, value and
 rate) and 1824-1832 (for a composite, the two circles split into a common one and a relative one).
standing: a MODEL of the Supplement's composite of two held components. Not ledger data. The structure has
 data fields only.
statement: Held2 holds the value and rate of component A (a1, a2) and of component B (b1, b2). commonTurn c s
 turns both by the pair (c, s). relativeTurn c s turns B alone. recA and recB are the costs of the components.
 recSum is the cost of A and B recombined. recQuarter is the cost of A recombined with B after a quarter turn.
 crossRe and crossIm are the two cross terms. neg2 reverses every entry.
-/
import Mathlib.Data.Real.Basic

set_option autoImplicit false
namespace APFPaper5.K3

/-- Two held components: value and rate of A, value and rate of B. -/
@[ext] structure Held2 where
  a1 : ℝ
  a2 : ℝ
  b1 : ℝ
  b2 : ℝ

/-- The same turn applied to both components. -/
def commonTurn (c s : ℝ) (h : Held2) : Held2 :=
  ⟨c * h.a1 - s * h.a2, s * h.a1 + c * h.a2, c * h.b1 - s * h.b2, s * h.b1 + c * h.b2⟩

/-- A turn applied to component B alone. -/
def relativeTurn (c s : ℝ) (h : Held2) : Held2 :=
  ⟨h.a1, h.a2, c * h.b1 - s * h.b2, s * h.b1 + c * h.b2⟩

/-- The cost of component A. -/
def recA (h : Held2) : ℝ := h.a1 * h.a1 + h.a2 * h.a2

/-- The cost of component B. -/
def recB (h : Held2) : ℝ := h.b1 * h.b1 + h.b2 * h.b2

/-- The cost of A and B recombined. -/
def recSum (h : Held2) : ℝ := (h.a1 + h.b1) * (h.a1 + h.b1) + (h.a2 + h.b2) * (h.a2 + h.b2)

/-- The cost of A recombined with B after a quarter turn of B. -/
def recQuarter (h : Held2) : ℝ := (h.a1 - h.b2) * (h.a1 - h.b2) + (h.a2 + h.b1) * (h.a2 + h.b1)

/-- The first cross term of A and B. -/
def crossRe (h : Held2) : ℝ := h.a1 * h.b1 + h.a2 * h.b2

/-- The second cross term of A and B. -/
def crossIm (h : Held2) : ℝ := h.a2 * h.b1 - h.a1 * h.b2

/-- Every entry reversed. -/
def neg2 (h : Held2) : Held2 := ⟨-h.a1, -h.a2, -h.b1, -h.b2⟩

end APFPaper5.K3


