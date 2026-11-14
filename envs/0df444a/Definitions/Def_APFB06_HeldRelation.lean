-- Prove2me | Definitions.Def_APFB06_HeldRelation
-- name    : APFB06_HeldRelation
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:06:29.861056+00:00
-- url     : https://prove2.me/theorems/bb02dc21-b518-46c9-8a16-224672ee9560
-- title:
--   Proposed NeedsNewRecord and HeldRelationExists predicates on supplied shared FamilyCost data
-- statement:
--   Proposed NeedsNewRecord and HeldRelationExists predicates on supplied shared FamilyCost data; no B06 entailment. Premises: No law assumed by definition; HeldRelationExists itself would be an extra existence hypothesis. Scope: NeedsNewRecord preserves testedness, both admissibility guards and near-optimal novelty; existence is not tied to actualJoint, original carried family or B01 quotient.
--
--   **Representation and scope.** NeedsNewRecord preserves testedness, both admissibility guards and near-optimal novelty; existence is not tied to actualJoint, original carried family or B01 quotient.
--
--   **Supplied data or hypotheses.** No law assumed by definition; HeldRelationExists itself would be an extra existence hypothesis.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFB06_HeldRelation.lean; Sib v15, SHA-256 f917457bb509c86b4ff0742e1e05961373e3366a3744a37bf3b43fcb8ac4a4a4. ['25-32: NeedsNewRecord', '35-45: HeldRelationExists', '9-11: proposal and Batch4 bridge explicitly owed', 'RULING_eight_decisions item1']

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFB06_HeldRelation
title: PROPOSED Lean form of "irreducibly joint" in B06: a held family with a relation task that needs a new record
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Author ruling of 2026-11-12 (RULING_eight_decisions_2026-11-12, item 1). FOUNDATION_INPUTS B06 current
 wording. Paper 0 v6.3.2 sec:chained_boats, "What is paid for".
standing: PROPOSAL. This module does not change the declared input. It is stated on the shared FamilyCost
 vocabulary, not on B06's own joint-class vocabulary; the correspondence between the two (the Batch 4 bridge) is
 owed. A disturbance that defeats the pair is deliberately not part of it.
statement: NeedsNewRecord says r is tested, S and insert r S are ledger-admissible, and r is support-novel over
 S. HeldRelationExists says some context has a nonempty family S and a task r outside S with NeedsNewRecord.
-/
import Definitions.Def_APFPaper1_FamilyCost
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Finset.Insert

set_option autoImplicit false
namespace APFB06

open APFPaper1.Source

/-- `r` is tested, admitted alongside the held family `S`, and needs a new record over it. -/
def NeedsNewRecord {D P R Record : Type*} [DecidableEq D]
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (tested : D → Prop) (C : ℝ) (S : Finset D) (r : D) : Prop :=
  tested r ∧
    familyAdmissible wholeResource calibration maintained sufficient usesToRealize C S ∧
    familyAdmissible wholeResource calibration maintained sufficient usesToRealize C (insert r S) ∧
    supportNovel wholeResource calibration maintained sufficient usesToRealize S r

/-- Some context holds a nonempty family together with a relation task that needs a new record. -/
def HeldRelationExists {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (tested : (g : Context) → D g → Prop)
    (C : Context → ℝ) : Prop :=
  ∃ (g : Context) (S : Finset (D g)) (r : D g), S.Nonempty ∧ r ∉ S ∧
    NeedsNewRecord (wholeResource g) (calibration g) (maintained g) (sufficient g)
      (usesToRealize g) (tested g) (C g) S r

end APFB06


