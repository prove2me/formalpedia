-- Prove2me | Definitions.Def_APFB07a_ProtocolBinding
-- name    : APFB07a_ProtocolBinding
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:51:13.255516+00:00
-- url     : https://prove2.me/theorems/40e1bf6c-d14a-4d32-a182-c40803905f42
-- title:
--   Protocol service, whole bill, and budgeted candidates
-- statement:
--   Serves requires sufficient support within a protocol’s maintained records, with actual use, for every task in a finite family. Candidates serve the family and have calibrated whole bill at most C. The protocol-domain correspondence ruling is recorded, but this review does not adopt a physical domain, realization, or source certification. Serves repeats the extensional service condition and needs a shared-symbol binding for Foundation placement.
--
--   **Meaning and scope.** Serves requires sufficient support within a protocol’s maintained records, with actual use, for every task in a finite family. Candidates serve the family and have calibrated whole bill at most C. Fidelity exposure: The protocol-domain correspondence ruling is recorded, but this review does not adopt a physical domain, realization, or source certification. Serves repeats the extensional service condition and needs a shared-symbol binding for Foundation placement.
--
--   **Supplied data and hypotheses**
--
--   - All explicit/implicit parameters and hypotheses in the exact declaration inventory below, together with the recorded module variable and typeclass context. The protocol-domain correspondence ruling is recorded, but this review does not adopt a physical domain, realization, or source certification. Serves repeats the extensional service condition and needs a shared-symbol binding for Foundation placement.
--
--   **Limits**
--
--
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1, K3 or K4 closure.
-- source:
--   Definitions/Def_APFB07a_ProtocolBinding.lean; Sib v44 / pullbacks v1, SHA-256 85c6cff29537dd8747024cf05e0e5404865bc83336e5fe2ccc0c11cf975d6acf. {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'lines_or_section': '1224-1241,1774-1887,2197-2223,2624-2626,3188-3230,7090-7110'}; {'path': 'Papers/Paper 00 - What Physics Permits/Paper_0_What_Physics_Permits_v6.3.2.tex', 'lines_or_section': '3226-3242, sec:argmin_scope'}

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFB07a_ProtocolBinding
title: A candidate binding of A2's domain and price to the ledger: the protocols that serve a fixed task family at a bill no greater than the capacity, priced by their calibrated whole-resource bill
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: FOUNDATION_INPUTS B07a (scope: "Preserve the original interface-local admissible configurations and
 total admissibility cost"; formal_reference: "its supplied domain/price/actual parameters still require
 source-fidelity accounting"). Paper 0, sec:argmin_scope: "The minimum ranges over the original
 interface-local admissible configurations at the stated resolution and context. The comparison cannot
 silently change the task, support, perturbations, duration, calibration or whole-resource account." (read
 in the local copy v6.3.2; the pinned source is v6.2.56:3491-3515, not reopened). Def_APFPaper1_FamilyCost.
standing: a CANDIDATE binding put to the author. Whether the source's admissible domain and price are these
 is a correspondence only the author can affirm. The actual realization is still a supplied argument.
statement: Serves S p says protocol p serves every member of the task family S from its own maintained
 sufficient support (the membership condition inside familyCost). protocolAdmissible C S p says p serves S
 and its calibrated bill is at most the capacity C. protocolBill p is the calibrated whole-resource bill.
note: the context (with its resolution, perturbations and duration) is fixed, as in the shared FamilyCost
 vocabulary. A sibling draft (Def_APFB06_ExtensionalJoint) names the same serving condition; the owning seat
 should keep one.
-/
import Definitions.Def_APF_B07a_DeclaredInput
import Definitions.Def_APF_B07b_DeclaredInput
import Definitions.Def_APFPaper1_FamilyCost

set_option autoImplicit false
namespace APFB07a

/-- p serves every member of S from its own maintained sufficient support. -/
def Serves {D P Record : Type*} (maintained : P → Set Record)
    (sufficient : P → Set Record → D → Prop) (usesToRealize : P → D → Set Record → Prop)
    (S : Finset D) (p : P) : Prop :=
  ∀ d ∈ S, ∃ sigma : Set Record,
    sigma ⊆ maintained p ∧ sufficient p sigma d ∧ usesToRealize p d sigma

/-- The calibrated whole-resource bill of a protocol. -/
def protocolBill {P R : Type*} (wholeResource : P → R) (calibration : R → NNReal) (p : P) : ℝ :=
  (calibration (wholeResource p) : ℝ)

/-- p serves S and its bill is at most the capacity. -/
def protocolAdmissible {D P R Record : Type*} (wholeResource : P → R) (calibration : R → NNReal)
    (maintained : P → Set Record) (sufficient : P → Set Record → D → Prop)
    (usesToRealize : P → D → Set Record → Prop) (C : ℝ) (S : Finset D) (p : P) : Prop :=
  Serves maintained sufficient usesToRealize S p ∧ protocolBill wholeResource calibration p ≤ C

end APFB07a


