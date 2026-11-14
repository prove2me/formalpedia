-- Prove2me | Definitions.Def_APFB07a_OccupantBinding
-- name    : APFB07a_OccupantBinding
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:52:00.041773+00:00
-- url     : https://prove2.me/theorems/a1f3767c-3a0a-40e4-a156-587962d79235
-- title:
--   A2 candidates admitted at a supplied occupant
-- statement:
--   Defines candidates by admission at a supplied raw representative, service of the alignment’s entire family, and a calibrated whole bill within capacity. Admission at the occupant is an added candidate-domain restriction. No identification of this domain with the original A2 domain is proved.
--
--   **Meaning and scope.** Defines candidates by admission at a supplied raw representative, service of the alignment’s entire family, and a calibrated whole bill within capacity. Fidelity exposure: Admission at the occupant is an added candidate-domain restriction. No identification of this domain with the original A2 domain is proved.
--
--   **Supplied data and hypotheses**
--
--   - All explicit/implicit parameters and hypotheses in the exact declaration inventory below, together with the recorded module variable and typeclass context. Admission at the occupant is an added candidate-domain restriction. No identification of this domain with the original A2 domain is proved.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFB07a_OccupantBinding.lean; Sib v44 / pullbacks v1, SHA-256 c7058f8c3151ffa33b141dc2f9238b8a08fc3a8130d18fa6277f1010e191ecd8. {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'lines_or_section': '1224-1241,1774-1887,2197-2223,2624-2626,3188-3230,7090-7110'}; {'path': 'Papers/Paper 00 - What Physics Permits/Paper_0_What_Physics_Permits_v6.3.2.tex', 'lines_or_section': '3226-3242, sec:argmin_scope'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB07a_OccupantBinding
title: The protocol binding of A2 taken at an occupant: the admissible protocols are those in the occupant's continuation class that serve its whole family at a bill no greater than the capacity
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author's rulings of 2026-11-13: 16:14 HST (the protocol binding affirmed; the realization is the
 occupant's alignment as determined by the protocol), 16:23 HST ("Protocols can only be instantiated or held
 by the occupant"), 16:27 and 16:29 HST (a step is taken when the budget allows and A2 selects it; this is
 what a continuation profile is). Def_APFB07a_ProtocolBinding. FOUNDATION_INPUTS B06, B07a in declared form.
standing: a refinement of the affirmed protocol binding, put to the author. It adds one clause to the
 admissible domain: the protocol is in the continuation class of the occupant's raw state.
statement: occupantAdmissible o x p says that p is admitted at the raw state x, serves every member of the
 family the alignment o carries, and bills at most the capacity. An interface is an alignment together with
 a raw state of its carrier.
-/
import Definitions.Def_APF_B06_DeclaredInput
import Definitions.Def_APFB07a_ProtocolBinding

set_option autoImplicit false
namespace APFB07a

/-- Admitted at the occupant's raw state, serving its whole family, at a bill no greater than capacity. -/
def occupantAdmissible {Raw FullProcess Resource Record : Type*} (Cont : Raw → FullProcess → Prop)
    (Dset : Set (APFB01.PhysicalState Cont → Bool)) (protocols : Set FullProcess)
    (wholeResource : {p // p ∈ protocols} → Resource) (calibration : Resource → NNReal)
    (maintained : {p // p ∈ protocols} → Set Record)
    (sufficient : {p // p ∈ protocols} → Set Record → APFB06.Task Cont Dset → Prop)
    (usesToRealize : {p // p ∈ protocols} → APFB06.Task Cont Dset → Set Record → Prop)
    (C : ℝ) (o : APFB06.OriginalAlignment Cont Dset) (x : Raw) (p : {p // p ∈ protocols}) : Prop :=
  Cont x p.val ∧ Serves maintained sufficient usesToRealize o.carried p ∧
    protocolBill wholeResource calibration p ≤ C

end APFB07a


