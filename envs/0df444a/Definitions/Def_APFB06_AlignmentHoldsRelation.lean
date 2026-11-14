-- Prove2me | Definitions.Def_APFB06_AlignmentHoldsRelation
-- name    : APFB06_AlignmentHoldsRelation
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:51:03.006079+00:00
-- url     : https://prove2.me/theorems/85bcad0d-d6b7-46ea-84c8-649a5b4e677b
-- title:
--   An alignment contains a tested support-novel relation task over a nonempty carried subfamily
-- statement:
--   An alignment contains a tested support-novel relation task over a nonempty carried subfamily. The predicate requires nonempty S, r outside S, insert r S inside the carried family, tested r and positive-window support novelty; it does not itself assert either admissibility guard. Boundaries: The Nov13 held-relation ruling reports an author reading, but the frozen declared B06 does not entail this predicate. hrel/hread must remain visible in consumers. Relation means tested support novelty here; no typed binary relation between members or defeating disturbance is constructed.
--
--   **Supplied data and hypotheses**
--
--   - hresp: all raw distinctions descend; supplied tested, maintained, sufficient, usesToRealize, wholeResource/calibration; no existence asserted by this definition
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFB06_AlignmentHoldsRelation.lean; Sib v44 / pullbacks v1, SHA-256 844bfa9505406f63eb29a06aa154dea5024cdbe712925bc95fe0a84980a5281f. Paper 1 Supplement v9.28:1313-1322,1761-1766,1774-1885,2624-2625,2777-2782,7101; Paper 5 Supplement v7.33:3034-3075 (remaining K1-K6 physical obligations); Frozen pullbacks/MANIFEST.txt and Notes passes1-6, hypothesis ledger, joint-class and held-relation ruling records; Actual codebank delta_calculus.py:165-188,236-300; continuation_calculus.py:76-140; quantum_frontend_closure.py:494-565,864-921

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-13; not
 gated, not reviewed, not released, not built on the build box)
name: APFB06_AlignmentHoldsRelation
title: The reading of "irreducibly joint" of 2026-11-12, tied to an alignment: its held family contains a tested task that needs a new record over a nonempty rest
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Author ruling of 2026-11-12 (RULING_eight_decisions_2026-11-12, item 1, as recorded in
 DRAFT_FOUNDATION_INPUTS_B06_irreducibly_joint_line_2026-11-12: an irreducibly joint alignment is one whose
 carried family is actually held and whose relation is itself a tested task that needs a new record).
 Def_APFB06_HeldRelation (NeedsNewRecord, HeldRelationExists: stated on the FamilyCost vocabulary, with no
 mention of any alignment). Def_APFB06_PhysicalDomain (heldDistinctions).
standing: PROPOSAL. It does not change the declared input or Def_APFB06_HeldRelation. It says of ONE
 alignment what HeldRelationExists says of no alignment in particular.
statement: AlignmentHoldsRelation says the alignment's held family, written as raw distinctions, contains a
 task r and a nonempty family S not containing r, with r tested and support-novel over S.
not_claimed: that r is "the relation between" the members of S in any further sense (the ledger has no
 typed notion of that); the two admissibility clauses of NeedsNewRecord (under B06 they follow, see
 Thm_APFB06_held_relation_of_occupancy); any disturbance that defeats the pair.
-/
import Definitions.Def_APFB06_PhysicalDomain
import Definitions.Def_APFPaper1_FamilyCost

set_option autoImplicit false
namespace APFB06

open APFPaper1.Source

/-- The alignment holds a relation: a tested member of its held family is support-novel over a nonempty
family of other members. -/
def AlignmentHoldsRelation {X Q P R Record : Type*} (Cont : X → Q → Prop)
    (Delta : (X → Bool) → Prop) [DecidableEq {d : X → Bool // Delta d}]
    (hresp : ∀ (d : {d : X → Bool // Delta d}) (x y : X), Cont x = Cont y → d.val x = d.val y)
    (wholeResource : P → R) (calibration : R → NNReal) (maintained : P → Set Record)
    (sufficient : P → Set Record → {d : X → Bool // Delta d} → Prop)
    (usesToRealize : P → {d : X → Bool // Delta d} → Set Record → Prop)
    (tested : {d : X → Bool // Delta d} → Prop)
    (a : OriginalAlignment Cont (physicalDomain Cont Delta hresp)) : Prop :=
  ∃ (S : Finset {d : X → Bool // Delta d}) (r : {d : X → Bool // Delta d}),
    S.Nonempty ∧ r ∉ S ∧ insert r S ⊆ heldDistinctions Cont Delta hresp a ∧ tested r ∧
    supportNovel wholeResource calibration maintained sufficient usesToRealize S r

end APFB06


