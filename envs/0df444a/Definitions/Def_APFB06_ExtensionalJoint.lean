-- Prove2me | Definitions.Def_APFB06_ExtensionalJoint
-- name    : APFB06_ExtensionalJoint
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:36:09.952311+00:00
-- url     : https://prove2.me/theorems/da89bb2a-d57b-4b9e-b53d-a04938ad62c3
-- title:
--   Joint service and its class defined by maintained sufficient records
-- statement:
--   Joint service and its class defined by maintained sufficient records. Serves reproduces the shared familyCost serving predicate exactly; extensionalJoint and servingBills introduce names for its set and NNReal bills, with no new Prop-valued structure fields. Boundaries: Definition is ordinary shared vocabulary. Physical identification of B06 J with this class relies on the reported Nov13 joint-class reading and exact original parameter binding. Service does not imply any endpoint reading or execution.
--
--   **Representation and scope.** Serves reproduces the shared familyCost serving predicate exactly; extensionalJoint and servingBills introduce names for its set and NNReal bills, with no new Prop-valued structure fields.
--
--   **Supplied data or hypotheses.** Arbitrary supplied record relations; no law or physical existence hypothesis
-- source:
--   Definitions/Def_APFB06_ExtensionalJoint.lean; Sib v44 / pullbacks v1, SHA-256 d0c5d8bb9a6267527f8df7b9a39c1f8dca729b40072a5adc165d1ec5387d03f5. ['Paper 1 Supplement v9.28:1313-1322,1761-1766,1774-1885,2624-2625,2777-2782,7101', 'Paper 5 Supplement v7.33:3034-3075 (remaining K1-K6 physical obligations)', 'Frozen pullbacks/MANIFEST.txt and Notes passes1-6, hypothesis ledger, joint-class and held-relation ruling records', 'Actual codebank delta_calculus.py:165-188,236-300; continuation_calculus.py:76-140; quantum_frontend_closure.py:494-565,864-921']

/-
APF Foundation Ledger — definition node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-13; not
 gated, not reviewed, not released, not built on the build box)
name: APFB06_ExtensionalJoint
title: PROPOSED value of B06's joint class: the protocols that serve every member of a family from their own maintained sufficient support
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:7101 (the joint class "is at present carried in the formal arm as data";
 read extensionally it is "the set of protocols that realize every member of S from their own maintained
 support"; "the formal arm is expected to adopt it"), 2777-2782 (the monotonicity proof reads the class this
 way), 2624 (support assignment of a joint protocol), 1787-1790 (ledger valuation convention). The membership
 condition is the one already inside APFPaper1.Source.familyCost and familyFeasible, word for word.
standing: PROPOSAL for the author's ruling. This module does not change the declared input B06. In
 AmendedB06_20260914 the joint class J stays a supplied argument; this names one value for it. That the
 source's joint class IS this value is a correspondence only the author can affirm.
statement: Serves p S says p has, for each d in S, a set of its own maintained records that is sufficient
 for d and that p uses to realize d. extensionalJoint S is the set of such p. servingBills S is the set of
 their calibrated whole-resource bills.
not_claimed: any law on maintained, sufficient or usesToRealize; that a serving protocol ends where the
 members of S read true (that is a further clause, see Thm_APFB06_extensional_joint_class).
-/
import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFPaper1_FamilyCost

set_option autoImplicit false
namespace APFB06

/-- `p` serves every member of `S` from its own maintained sufficient support. -/
def Serves {D P Record : Type*} (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (p : P) (S : Finset D) : Prop :=
  ∀ d ∈ S, ∃ sigma : Set Record,
    sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma

/-- The extensional joint class of `S`: the protocols that serve `S`. -/
def extensionalJoint {D P Record : Type*} (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (S : Finset D) : Set P :=
  {p | Serves maintained sufficient usesToRealize p S}

/-- The calibrated whole-resource bills of the protocols that serve `S`. -/
def servingBills {D P R Record : Type*} (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (S : Finset D) : Set NNReal :=
  {t | ∃ p : P, Serves maintained sufficient usesToRealize p S ∧ calibration (wholeResource p) = t}

end APFB06


