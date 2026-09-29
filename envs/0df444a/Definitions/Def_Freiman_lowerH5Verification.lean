-- Prove2me | Definitions.Def_Freiman_lowerH5Verification
-- name    : Freiman_lowerH5Verification
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:40:19.413768+00:00
-- url     : https://prove2.me/theorems/c638e229-98da-48b1-90d8-2b88293ac6d6
-- title:
--   Freiman p97 predecessor certificates: lowerH5Verification
-- statement:
--   Actual source predecessor cases, exact Q(sqrt3,sqrt7) bound-pair witnesses, reconstructed endpoint residuals and earlier-depth priority events.
-- source:
--   Freiman report, 'The carried target in the shortened-left case of Section 14', sec:h5-source-target, Lemma lem:h5-original-two (source printed p. 97), report/source/staging/parts/h5_target.tex; global_selection.tex priority rule; certificates/target_selection/h5_cases.json and h5_original_appendix_printed.json; verification/families/target_selection/verify_h5_original_independent.py.

import Definitions.Def_Freiman_lowerH5WitnessData
namespace Freiman
structure LowerH5RecordBinding (c : LowerH5Case) (r : LowerH5Record) : Prop where
  caseId : r.caseId = c.id
  witnessRange : 0 < r.witness ∧ r.witness ≤ lowerH5Witnesses.length
  boundRanges : ∀ i ∈ r.bounds, 0 < i ∧ i ≤ lowerH5Bounds.length
  premise : (lowerH5RecordBounds r).toFinset = (lowerH5Residual c r.branch).toFinset
  lowerMember : (lowerH5Witness r.witness).lowerBound ∈ lowerH5RecordBounds r
  upperMember : (lowerH5Witness r.witness).upperBound ∈ lowerH5RecordBounds r
  rectangle : (lowerH5Witness r.witness).rectangle = c.rectangle
def lowerH5CaseBinding (c : LowerH5Case) : Prop :=
  lowerH5CaseShape c ∧
  (∀ r ∈ lowerH5RecordsFor c, LowerH5RecordBinding c r) ∧
  (∀ bi : ℕ, ∀ cs g, (lowerH5Comparisons c)[bi]? = some (cs,g) → g ≠ .automatic →
    (∃ r ∈ lowerH5RecordsFor c, r.branch = bi) ∨ (lowerH5Exceptional c ∧ bi=5)) ∧
  ((lowerH5Comparisons c).filter (fun z => match z.2 with | .automatic => true | _ => false)).length = c.automatic
def lowerH5CatalogValid : Prop :=
  (lowerH5Cases.map fun c => (c.kind,c.context.words)) = lowerH5ExpectedKeys ∧
  lowerH5Cases.length = 23 ∧ lowerH5Records.length = 89 ∧ lowerH5Witnesses.length = 71 ∧
  lowerH5Bounds.length = 43 ∧ (lowerH5Cases.map (fun c => c.automatic)).sum = 92 ∧
  ((lowerH5Cases.filter fun c => decide (c.kind = .b2h9not ∧ c.context.words.1 ∈ [[1],[2],[3]])).map (fun c => c.name)) =
    ["B2-1-H9-notH16","B2-2-H9-notH16","B2-3-H9-notH16"]
def lowerH5AllBindings : Prop := ∀ c ∈ lowerH5Cases, lowerH5CaseBinding c
def lowerH5AllWitnesses : Prop := ∀ i : ℕ, 0 < i → i ≤ lowerH5Witnesses.length → certWitnessValid (lowerH5Witness i)
def lowerH5Numeric (c : LowerH5Case) : Prop :=
  ∀ r s q : ℝ, certRectangleMem c.rectangle r s → lowerHistoryConditions (lowerH5Premises c) r s q →
    ∀ bi : ℕ, ∀ cs g, (lowerH5Comparisons c)[bi]? = some (cs,g) → lowerHistoryConditions cs r s q →
      lowerHistoryComparisonHolds g r s q ∨ (lowerH5Exceptional c ∧ bi=5)
end Freiman


