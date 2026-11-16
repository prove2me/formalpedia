-- Prove2me | Definitions.Def_APFPaper5_K1_LedgerScore
-- name    : APFPaper5_K1_LedgerScore
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T19:47:13.951782+00:00
-- url     : https://prove2.me/theorems/6ff6c092-b8f6-4040-9f72-50cf6735f80d
-- title:
--   Ledger score, counted families and an explicit availability predicate
-- statement:
--   Defines ledgerScore as shared family cost; LedgerCounted includes finite-family admissibility, testing and support novelty over the other indexed members; LedgerAvailable asserts exact-service protocol existence for each admissible family. These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. A definition of a predicate does not establish its truth. Availability and representation over RecordLedger are not installed Foundation inputs; calling a family counted retains every conjunct as an obligation.
--
--   **Supplied data and hypotheses**
--
--   - These are finite table-form claims with identity role exchange. They do not construct the physical ordered score, its alternating part, a general boundary-role isomorphism, K3 profile binding, K2-K6, or Born. A definition of a predicate does not establish its truth. Availability and representation over RecordLedger are not installed Foundation inputs; calling a family counted retains every conjunct as an obligation.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions.Def_APFPaper5_K1_LedgerScore; Sib v66 / pullbacks v22, SHA-256 5533dc882afa3825b6ec29babd4e09f3c2e89cf67c39ba4af145d322a2d0febc. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Definitions\Def_APFPaper5_K1_LedgerScore.lean

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-14; not
 gated, not reviewed, not released, not built in the ledger repo)
name: APFPaper5_K1_LedgerScore
title: On a record ledger: the ledger form of the score of two families is their shared cost; a counted family is a finite family within capacity, tested, each member support-novel over the others; and the availability sentence
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: RULING_K1_tie_in_calls_1_to_4_2026-11-14 (the author, 19:57 HST): call 1 (the shared cost is the
 ledger form, the symmetric part, of the K layer's score off the record-book side), call 2 (what "counted"
 means), call 4 (availability is to be an input line). Def_APFPaper1_RecordLedger (this seat).
 Def_APFPaper5_K1_SharedCost (builder seat).
standing:
 - ledgerScore: a DEFINITION, adopted by the author as call 1. A choice of a score from ledger objects,
   not a consequence of any input. Orientation (the alternating part of an ordered score) is not ruled.
 - LedgerCounted: a DEFINITION, adopted by the author as call 2. Said of the family in hand.
 - LedgerAvailable: NOT A DEFINITION OF ANYTHING THAT HOLDS BY CONSTRUCTION. It is the availability
   sentence written out so that theorems can name it: every family within capacity has a protocol keeping
   exactly what it needs. It claims that protocols exist. By the author's ruling on call 4 it is to be an
   input line, the author's to install. Until then every theorem that uses it takes it as a hypothesis.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Definitions.Def_APFPaper1_RecordLedger
import Definitions.Def_APFPaper5_K1_SharedCost
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false

open APFPaper1 APFPaper1.Source

namespace APFPaper5.K1

variable {D P Record : Type*}

/-- The ledger form of the score of two families: their shared cost. -/
noncomputable def ledgerScore [DecidableEq D] (L : RecordLedger D P Record) (S T : Finset D) : ℝ :=
  sharedCost L.familyCost S T

/-- The availability sentence: every family within capacity has a protocol that keeps exactly the records
the family needs and serves the family. -/
def LedgerAvailable [DecidableEq Record] (L : RecordLedger D P Record) (C : ℝ) : Prop :=
  ∀ S : Finset D,
    familyAdmissible L.wholeResource L.calibration L.maintained L.sufficient L.usesToRealize C S →
    ∃ p : P, L.kept p = S.biUnion L.needsFin ∧ ∀ d ∈ S, ∃ sigma : Set Record,
      sigma ⊆ L.maintained p ∧ L.sufficient p sigma d ∧ L.usesToRealize p d sigma

/-- A counted family: finite, within capacity, each member tested and support-novel over the others. -/
def LedgerCounted {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq D]
    (L : RecordLedger D P Record) (tested : D → Prop) (C : ℝ) (dist : ι → D) : Prop :=
  familyAdmissible L.wholeResource L.calibration L.maintained L.sufficient L.usesToRealize C
      (Finset.univ.image dist) ∧
    (∀ i, tested (dist i)) ∧
    ∀ i, supportNovel L.wholeResource L.calibration L.maintained L.sufficient L.usesToRealize
      ((Finset.univ.erase i).image dist) (dist i)

end APFPaper5.K1


