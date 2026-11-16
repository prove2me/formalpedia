-- Prove2me | Definitions.Def_APFB02_DomainComplete
-- name    : APFB02_DomainComplete
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-15T19:41:37.739082+00:00
-- url     : https://prove2.me/theorems/05daf2f1-b316-494b-9f78-925e0833e4f2
-- title:
--   A completeness predicate for a family of Boolean readings
-- statement:
--   Defines admission readings, settlement by a reading family, and settlement of every Boolean reading that respects continuation profiles. DomainComplete is an additional predicate. An admission reading is not thereby an enforceable distinction. Current B02 does not supply completeness or a domain containing all such readings.
--
--   **Supplied data and hypotheses**
--
--   - DomainComplete is an additional predicate. An admission reading is not thereby an enforceable distinction. Current B02 does not supply completeness or a domain containing all such readings.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions.Def_APFB02_DomainComplete; Sib v66 / pullbacks v22, SHA-256 6c9d99a3c1657d57fd2d5cb08bc3bb82fa858edeefe4cb7bbc30a815be805185. rv2_v66_v22_PRIOR_WORK_CHECK.json; rv2_v66_v22_SOURCE_READ_SUPPLEMENT.json; C:\Users\brook\My Drive\__APF Library\Artifacts_2026-11-15_session\astra\sib_v66_publication\source\Definitions\Def_APFB02_DomainComplete.lean

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-14; not gated, not reviewed)
name: APFB02_DomainComplete
title: The reading "the state can go on to do this", what it is for the listed distinctions to settle a reading, and what it is for the list to be complete
inputs_revision: 2026-11-14.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-14 17:35 HST: "Told apart is in the def of continuation profile"
 (RULING_told_apart_in_the_definition_2026-11-14). Paper 1 Supplement v9.28: 1224-1235 (the class of finite
 admissible continuations available from a raw possibility; "Membership ... is certified in finite
 experiments by executing the continuation"), 1247-1257 (continuation identity is equality of that class),
 1745-1750 (a physical distinction is a quotient-descending separator with a finite admissible enforcement
 protocol). FOUNDATION_INPUTS.json revision 2026-11-14.1, B01 and B02 (first sentence), and the scope in
 B02's amendment block (each distinction counted once; a reading made from distinctions is not claimed to
 be a member of the domain).
standing: three predicates, typed by this seat to state the author's remark exactly. They state no input.
 DomainComplete is not an adopted reading; whether a context's list of distinctions is complete by
 definition is the author's to say.
statement: admits Cont q is the two-valued reading that is true exactly at the states whose continuation
 profile holds q. Settles reads r says states that the listed distinctions read alike are read alike by r.
 DomainComplete Cont reads says every two-valued reading that separates only continuation profiles is
 settled by the listed distinctions.
-/
import Definitions.Def_APFB02_ToldApart

set_option autoImplicit false
namespace APFB02

/-- The reading "the state can go on to do `q`". -/
noncomputable def admits {X Q : Type*} (Cont : X → Q → Prop) : Q → X → Bool :=
  fun q x => @decide (Cont x q) (Classical.propDecidable _)

/-- The listed distinctions settle a reading: states they read alike are read alike by it. -/
def Settles {X D : Type*} (reads : D → X → Bool) (r : X → Bool) : Prop :=
  ∀ x y : X, (∀ d : D, reads d x = reads d y) → r x = r y

/-- The list of distinctions is complete: every two-valued reading that separates only continuation
profiles is settled by the listed distinctions. -/
def DomainComplete {X Q D : Type*} (Cont : X → Q → Prop) (reads : D → X → Bool) : Prop :=
  ∀ r : X → Bool, (∀ x y : X, Cont x = Cont y → r x = r y) → Settles reads r

end APFB02


