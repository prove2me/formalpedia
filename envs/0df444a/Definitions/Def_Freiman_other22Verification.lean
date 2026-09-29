-- Prove2me | Definitions.Def_Freiman_other22Verification
-- name    : Freiman_other22Verification
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:10:41.053986+00:00
-- url     : https://prove2.me/theorems/5dc1fb59-005e-4bba-b7a9-43eb3886e262
-- title:
--   other22Verification
-- statement:
--   Literal original other22 source data or precise source-binding/endpoint-adapter definitions. No assertion of validity is hidden in the data.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Data
import Definitions.Def_Freiman_lowerOther22

namespace Freiman
def other22Context (k : Fin 6) : LowerHistoryContext :=
  ⟨((other22Paths k).context,[3,1]),(false,false)⟩
def other22Ancestor (k : Fin 6) : LowerPair :=
  if ([3,1] : List ℕ+).IsSuffix (other22Paths k).context then ([],[]) else ([3],[2])
def other22AncestorUpper (k : Fin 6) : Bool :=
  decide (¬ ([3,1] : List ℕ+).IsSuffix (other22Paths k).context)
def other22ResidualWords : LowerPair := ([2,2,1],[3,1,2])
def other22RecordBinding (r : Other22Record) : Prop :=
  0 < r.witness ∧ r.witness ≤ 92 ∧
  (other22RecordPremise r).toFinset =
    (lowerHistoryResidual (other22Paths r.caseId) r.alternative (r.branch : ℤ)).toFinset ∧
  (other22Witness r.witness).lowerBound ∈ other22RecordPremise r ∧
  (other22Witness r.witness).upperBound ∈ other22RecordPremise r ∧
  (other22Witness r.witness).rectangle = (other22Paths r.caseId).rectangle
def other22CaseBinding (k : Fin 6) : Prop :=
  (∀ r ∈ other22Records, r.caseId = k → other22RecordBinding r) ∧
  (∀ ai : ℕ, ai < (lowerHistorySourcePremises (other22Paths k)).length →
    ∀ bi : ℕ, ∀ cs g,
      (lowerHistoryEndpointComparisons (other22Paths k))[bi]? = some (cs,g) →
      ∃ r ∈ other22Records, r.caseId = k ∧ r.alternative = ai ∧ r.branch = bi)
def other22AllBindings : Prop := ∀ k : Fin 6, other22CaseBinding k
def other22WitnessBatch (lo hi : ℕ) : Prop :=
  ∀ i : ℕ, lo ≤ i → i < hi → certWitnessValid (other22Witness (i+1))
def other22AllWitnesses : Prop :=
  ∀ i : ℕ, 0 < i → i ≤ 92 → certWitnessValid (other22Witness i)
noncomputable def other22AnchorValue (Z : LowerPair) : ℝ := by
  classical
  exact if lowerEnds Z.1 [3,1] then lowerBaseLower Z else lowerChildUpper Z ([3],[2])
def other22EndpointRepresented (base : LowerPair) (C : LowerHistoryContext)
    (words : LowerPair) (upper : Bool) (value : ℝ) : Prop :=
  ∃ z cs, (z,cs) ∈ lowerHistoryEndpointCases C words upper ∧
    lowerHistoryAtBase base cs ∧ value = lowerHistoryValue base C z ∧
    0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2
end Freiman


