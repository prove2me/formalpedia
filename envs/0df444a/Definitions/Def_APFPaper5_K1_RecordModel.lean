-- Prove2me | Definitions.Def_APFPaper5_K1_RecordModel
-- name    : APFPaper5_K1_RecordModel
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:08:39.478343+00:00
-- url     : https://prove2.me/theorems/4733ed34-a9c3-435e-af97-54fc38cbed82
-- title:
--   Family cost in a supplied weighted finite-record model
-- statement:
--   Instantiates familyCost with finite record sets as protocols, nonnegative record weights as bills, and service defined by containing each distinction’s required records. This is a conditional mathematical model of RECORDS.
--
--   **Representation and scope.** A faithful explicit special model of support-local accounting, not an encoding of all the Supplement support-independence clauses or a physical RECORDS theorem.
--
--   **Supplied data or hypotheses.** Record weights in NNReal; a finite required-record set for each distinction. All finite record sets are protocols; usesToRealize is True; service is support inclusion.
--
--   **Claim boundaries.** No predicate here proves an original interface is this record model. The infimum is over these supplied protocols; no physical capacity or execution test is built in.
--
--   This is conditional reference mathematics. The supplied model and its hypotheses are not adopted Foundation inputs, and this node does not establish K1 or K3 closure.
-- source:
--   Definitions/Def_APFPaper5_K1_RecordModel.lean; Sib v15, SHA-256 eae41414ddade1d539d450281f3bcc9dd828d31220e39d662170e345a413ad9d. [{'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'lines_or_section': '1772-1792;2502-2530'}, {'path': 'Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_records_clause_2026-11-12.md', 'lines_or_section': '1'}]

/-
APF Foundation Ledger — definition node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_RecordModel
title: The weighted record model of the ledger's family cost
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 1 Supplement v9.28:1763-1792 (ledger cost of a family; the interface term; "under protocol and
 bill factorization this valuation reduces to a sum") and 2502-2530 (support-independent resolution: exact
 witness supports, orthogonality, support-local additive accounting, charged carriage).
standing: a MODEL of the source vocabulary, not ledger data. A protocol is the finite set of records it
 maintains. Its bill is the sum of the costs of those records. A distinction is served when its own records
 are maintained. The Supplement lists additive accounting as a condition on an interface; it is not one of the
 declared inputs.
statement: recordModelCost w fam is the ledger's familyCost on that data.
-/
import Definitions.Def_APFPaper1_FamilyCost
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
namespace APFPaper5.K1

open APFPaper1.Source

universe u v
variable {ι : Type u} {Rec : Type v}

/-- The family cost of the weighted record model. -/
noncomputable def recordModelCost (w : Rec → NNReal) (fam : ι → Finset Rec) : Finset ι → ℝ :=
  familyCost (D := ι) (P := Finset Rec) (R := Finset Rec) (Record := Rec)
    (fun p => p) (fun r => ∑ a ∈ r, w a) (fun p => (↑p : Set Rec))
    (fun _ sigma d => (↑(fam d) : Set Rec) ⊆ sigma) (fun _ _ _ => True)

end APFPaper5.K1


