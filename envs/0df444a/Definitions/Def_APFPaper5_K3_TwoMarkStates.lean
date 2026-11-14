-- Prove2me | Definitions.Def_APFPaper5_K3_TwoMarkStates
-- name    : APFPaper5_K3_TwoMarkStates
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:13:22.88431+00:00
-- url     : https://prove2.me/theorems/536aae03-3cd4-48bb-9d1a-8bbe750e85e2
-- title:
--   Unit-pair state model and its designated rotation maps
-- statement:
--   Defines UnitPair, squared first-coordinate relation number, markOf, actTurn, reverseTurn and admTurns.
--
--   **Representation and scope.** Faithful to its exact supplied mathematical definitions under the stated exposure; original physical-object correspondence is not established.
--
--   **Claim boundaries.** K3-03
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K3_TwoMarkStates.lean; Sib v15, SHA-256 001d07bed42a960054d31cc877d295ee8f0cbadbc2e0c8c0c99bcc05fc6f39ff. P5:1686-1717;3049-3056

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_TwoMarkStates
title: The held relations of the two-mark model, their number, and the turns acting on them
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_TwoMarkModel.
standing: part of the supplied MODEL. Not ledger data; no declared input produces it.
statement: UnitPair is a pair of reals of unit length. relNumber is the square of its first entry. markOf is
 its turned mark. actTurn a is the turn by a acting on unit pairs. reverseTurn a is the reverse turn. admTurns
 is the set of all such turns.
-/
import Definitions.Def_APFPaper5_K3_TwoMarkModel
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K3

/-- A held relation of the two marks: a pair of unit length. -/
def UnitPair : Type := {w : ℝ × ℝ // w.1 * w.1 + w.2 * w.2 = 1}

/-- The number in the relation. -/
def relNumber (w : UnitPair) : ℝ := w.1.1 * w.1.1

/-- The turned mark of a held relation. -/
def markOf (w : UnitPair) : M2 := markQ w.1.1 w.1.2

/-- The turn by `a`, acting on held relations. -/
def actTurn (a w : UnitPair) : UnitPair :=
  ⟨(a.1.1 * w.1.1 - a.1.2 * w.1.2, a.1.2 * w.1.1 + a.1.1 * w.1.2), by
    have ha : a.1.1 * a.1.1 + a.1.2 * a.1.2 = 1 := a.2
    have hw : w.1.1 * w.1.1 + w.1.2 * w.1.2 = 1 := w.2
    have e : (a.1.1 * w.1.1 - a.1.2 * w.1.2) * (a.1.1 * w.1.1 - a.1.2 * w.1.2)
          + (a.1.2 * w.1.1 + a.1.1 * w.1.2) * (a.1.2 * w.1.1 + a.1.1 * w.1.2)
        = (a.1.1 * a.1.1 + a.1.2 * a.1.2) * (w.1.1 * w.1.1 + w.1.2 * w.1.2) := by ring
    show (a.1.1 * w.1.1 - a.1.2 * w.1.2) * (a.1.1 * w.1.1 - a.1.2 * w.1.2)
          + (a.1.2 * w.1.1 + a.1.1 * w.1.2) * (a.1.2 * w.1.1 + a.1.1 * w.1.2) = 1
    rw [e, ha, hw, mul_one]⟩

/-- The reverse of the turn by `a`. -/
def reverseTurn (a : UnitPair) : UnitPair :=
  ⟨(a.1.1, -a.1.2), by
    have ha : a.1.1 * a.1.1 + a.1.2 * a.1.2 = 1 := a.2
    show a.1.1 * a.1.1 + (-a.1.2) * (-a.1.2) = 1
    rw [neg_mul_neg]
    exact ha⟩

/-- The admissible moves of the model: the turns. -/
def admTurns : Set (UnitPair → UnitPair) := {f | ∃ a : UnitPair, f = actTurn a}

end APFPaper5.K3


