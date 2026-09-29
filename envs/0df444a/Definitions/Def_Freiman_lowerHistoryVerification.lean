-- Prove2me | Definitions.Def_Freiman_lowerHistoryVerification
-- name    : Freiman_lowerHistoryVerification
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T12:06:06.207591+00:00
-- url     : https://prove2.me/theorems/78aa40a0-96f4-41d9-9ed8-d3e61445921d
-- title:
--   Freiman.lowerHistoryVerification
-- statement:
--   Exact record binding and finite validator predicates, actual-source events and real-valued semantic bridge interfaces. Source: Freiman's Hall ray: Proof report and corrected English text (8 September 2026); history_certificates.tex app:all-suffix-histories, global_selection.tex lem:global-suffix-targets; initial_bridges.tex lem:H-entry-bridges; certificates/target_selection/all_suffix_histories_printed.json.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Appendix app:all-suffix-histories and its exact arithmetic/certificate guide.

import Definitions.Def_Freiman_lowerHistoryData
import Definitions.Def_Freiman_lowerHistorySource

namespace Freiman

set_option synthInstance.maxSize 1024 in
instance : DecidableEq LowerHistoryKey := by
  unfold LowerHistoryKey
  infer_instance

def lowerHistoryConditions (bs : List CertBound) (r s q : ℝ) : Prop :=
  ∀ b ∈ bs, certBoundHolds b r s q
def lowerHistoryAtBase (base : LowerPair) (bs : List CertBound) : Prop :=
  lowerHistoryConditions bs (lowerRatio base.1) (lowerRatio base.2) (lowerScale base)
def lowerHistoryComparisonHolds (g : LowerHistoryComparison) (r s q : ℝ) : Prop :=
  match g with
  | .automatic => True
  | .impossible => False
  | .bound b => certBoundHolds b r s q
def lowerHistoryComparisonsHold (p : LowerHistoryPath) (r s q : ℝ) : Prop :=
  ∀ cg ∈ lowerHistoryEndpointComparisons p,
    lowerHistoryConditions cg.1 r s q → lowerHistoryComparisonHolds cg.2 r s q
def lowerHistoryRecordFor (p : LowerHistoryPath) (record : LowerHistoryRecord) : Prop :=
  record.catalog = p.catalog ∧ record.pathId = p.id
def lowerHistoryRecordsFor (p : LowerHistoryPath) : List LowerHistoryRecord :=
  lowerHistoryRecords.toList.filter fun record => decide
    (record.catalog = p.catalog ∧ record.pathId = p.id)
def lowerHistorySurvivor (p : LowerHistoryPath) : Prop :=
  p.catalog = .initial ∧ (p.id = 182 ∨ p.id = 374) ∧ p.row = 2 ∧
  p.context ∈ [[2],[3]] ∧ p.entry = ([1],[]) ∧ p.initialWider = true ∧
  p.steps = [(([1],[]),true)] ∧ p.finalWider = false
def lowerHistoryRecordBinding (p : LowerHistoryPath) (record : LowerHistoryRecord) : Prop :=
  if record.survivor then lowerHistorySurvivor p ∧ record.alternative = 0 else
  0 < record.premiseId ∧ record.premiseId ≤ lowerHistoryPremises.size ∧
  0 < record.witnessId ∧ record.witnessId ≤ lowerHistoryWitnesses.size ∧
  (lowerHistoryPremise record.premiseId).toFinset =
    (lowerHistoryResidual p record.alternative record.endpointBranch).toFinset ∧
  (lowerHistoryWitness record.witnessId).lowerBound ∈ lowerHistoryPremise record.premiseId ∧
  (lowerHistoryWitness record.witnessId).upperBound ∈ lowerHistoryPremise record.premiseId ∧
  (lowerHistoryWitness record.witnessId).rectangle = p.rectangle
def lowerHistoryRecordCoverage (p : LowerHistoryPath) : Prop :=
  ∀ ai : ℕ, ai < (lowerHistorySourcePremises p).length →
    (∃ record ∈ lowerHistoryRecordsFor p,
      record.alternative = ai ∧ record.endpointBranch < 0) ∨
    (p.catalog ≠ .initial ∧ p.row ≠ 4 ∧
      ∀ bi : ℕ, ∀ cs g,
        (lowerHistoryEndpointComparisons p)[bi]? = some (cs,g) → g ≠ .automatic →
        ∃ record ∈ lowerHistoryRecordsFor p, record.alternative = ai ∧
          record.endpointBranch = (bi : ℤ) ∧ record.survivor = false)
def lowerHistoryPathBinding (p : LowerHistoryPath) : Prop :=
  p.alternatives = (lowerHistorySourcePremises p).length ∧
  (∀ record ∈ lowerHistoryRecordsFor p, lowerHistoryRecordBinding p record) ∧
  lowerHistoryRecordCoverage p
def lowerHistoryWitnessBatch (lo hi : ℕ) : Prop :=
  ∀ i : ℕ, lo ≤ i → i < hi → certWitnessValid (lowerHistoryWitness (i+1))
def lowerHistoryBindingBatch (lo hi : ℕ) : Prop :=
  ∀ i : ℕ, lo ≤ i → i < hi → ∀ p, lowerHistoryPaths[i]? = some p → lowerHistoryPathBinding p
def lowerHistoryCatalogKeys (cat : LowerHistoryCatalog) : List LowerHistoryKey :=
  (lowerHistoryPaths.toList.filter (fun p => decide (p.catalog = cat))).map lowerHistoryPathKey
def lowerHistoryAllWitnesses : Prop :=
  ∀ i : ℕ, 0 < i → i ≤ lowerHistoryWitnesses.size → certWitnessValid (lowerHistoryWitness i)
def lowerHistoryAllBindings : Prop :=
  ∀ p ∈ lowerHistoryPaths.toList, lowerHistoryPathBinding p

def lowerHistoryStateAt (p : LowerHistoryPath) (j : ℕ) : LowerHistoryState :=
  (p.steps.take j).foldl (fun s step => lowerHistoryAdvance s step.1 step.2) (lowerHistoryInitialState p)
def lowerHistoryWordsAt (p : LowerHistoryPath) (j : ℕ) : LowerPair :=
  (lowerHistoryReplay ([],[]) p j).1
def lowerHistoryBasePremises (p : LowerHistoryPath) : Option (List CertBound) :=
  if p.catalog = .initial then some [lowerHistoryZero,lowerHistoryHN,
    lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true]
  else (lowerHistoryRelaxedGoodness ⟨(p.context,[3,1]),(false,false)⟩).map fun good =>
    [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] ++ good
def lowerHistoryBaseEvent (base : LowerPair) (p : LowerHistoryPath) : Prop :=
  ∃ bs, lowerHistoryBasePremises p = some bs ∧ lowerHistoryAtBase base bs
def lowerHistoryGoodEvents (base : LowerPair) (p : LowerHistoryPath) : Prop :=
  ∀ j : ℕ, j ≤ p.steps.length → ∃ bs,
    lowerHistoryNecessary (lowerHistoryStateAt p j) (lowerHistoryWordsAt p j) = some bs ∧
    lowerHistoryAtBase base bs
def lowerHistoryChoiceEvents (base : LowerPair) (p : LowerHistoryPath) : Prop :=
  ∀ j : ℕ, ∀ l r, p.steps[j]? = some (l,r) →
    ∃ bs ∈ lowerHistorySourceChoices (lowerHistoryStateAt p j) l,
      lowerHistoryAtBase base (bs.map fun b =>
        lowerHistoryPull b (lowerHistoryWordsAt p j) (lowerHistoryStateAt p j).wider)
def lowerHistoryNormalizationEvents (base : LowerPair) (p : LowerHistoryPath) : Prop :=
  ∀ j : ℕ, j ≤ p.steps.length →
    let strict := if j = 0 then false else decide
      (((p.steps[j-1]?.getD (([],[]),false)).1) ∈
        [(([2],[]) : LowerLabel),([3],[]),([],[1])])
    lowerHistoryAtBase base [lowerHistoryNormalization
      (lowerHistoryWordsAt p j) (lowerHistoryStateAt p j).wider strict]
def lowerHistoryFinalEvent (base : LowerPair) (p : LowerHistoryPath) : Prop :=
  lowerHistoryAtBase base ((lowerHistoryFinalCuts p.row).map fun b =>
    lowerHistoryPull b (lowerHistoryWordsAt p p.steps.length) p.finalWider)
structure LowerHistorySourceEvents (base : LowerPair) (p : LowerHistoryPath) : Prop where
  baseEvent : lowerHistoryBaseEvent base p
  goodEvents : lowerHistoryGoodEvents base p
  choiceEvents : lowerHistoryChoiceEvents base p
  normalizationEvents : lowerHistoryNormalizationEvents base p
  finalEvent : lowerHistoryFinalEvent base p

def lowerHistoryContextFits (base : LowerPair) (C : LowerHistoryContext) : Prop :=
  lowerHistorySuffixContext base.1 C.words.1 ∧ lowerHistorySuffixContext base.2 C.words.2 ∧
  (decide (base.1.length % 2 = 1)).xor C.parity.1 =
    (decide (base.2.length % 2 = 1)).xor C.parity.2
def lowerHistoryCommonOdd (base : LowerPair) (C : LowerHistoryContext) : Bool :=
  (decide (base.1.length % 2 = 1)).xor C.parity.1
def lowerHistoryAppend (base words : LowerPair) : LowerPair := (base.1++words.1,base.2++words.2)
noncomputable def lowerHistoryValue (base : LowerPair) (C : LowerHistoryContext)
    (z : CertField × CertField) : ℝ :=
  (if lowerHistoryCommonOdd base C then -1 else 1) *
    (4 + prefixEval base.1 (certFieldVal z.1) + prefixEval base.2 (certFieldVal z.2))
noncomputable def lowerHistoryEndpointReal (base : LowerPair) (C : LowerHistoryContext)
    (words : LowerPair) (upper : Bool) : ℝ :=
  (if lowerHistoryCommonOdd base C then -1 else 1) *
    lowerEndpoint (lowerHistoryAppend base words) (upper.xor (lowerHistoryCommonOdd base C))
noncomputable def lowerHistoryEarlierAnchor (base : LowerPair) (p : LowerHistoryPath) (t : ℝ) : Prop :=
  let older : LowerPair := if ([3,1] : List ℕ+).IsSuffix p.context then ([],[]) else ([3],[2])
  let upper := decide (¬ ([3,1] : List ℕ+).IsSuffix p.context)
  lowerHistoryEndpointReal base ⟨(p.context,[3,1]),(false,false)⟩ older upper ≤
    (if base.1.length % 2 = 0 then t else -t)

def LowerHistoryEndpointLaw : Prop :=
  ∀ (base : LowerPair) (C : LowerHistoryContext), lowerHistoryContextFits base C →
    ∀ (words : LowerPair) (upper : Bool), ∃ z cs,
      (z,cs) ∈ lowerHistoryEndpointCases C words upper ∧ lowerHistoryAtBase base cs ∧
      lowerHistoryEndpointReal base C words upper = lowerHistoryValue base C z
def LowerHistoryGoodnessLaw : Prop :=
  ∀ (base : LowerPair) (C : LowerHistoryContext), lowerHistoryContextFits base C →
    lowerNormalize base = base → lowerGood base →
    ∃ bs, lowerHistoryRelaxedGoodness C = some bs ∧ lowerHistoryAtBase base bs
def LowerHistoryPullLaw : Prop :=
  ∀ (base words : LowerPair) (b : CertBound) (flip : Bool),
    0 < certFieldVal b.threshold.c →
    0 ≤ certFieldVal b.threshold.x0 → 0 ≤ certFieldVal b.threshold.x1 →
    0 ≤ certFieldVal b.threshold.y0 → 0 ≤ certFieldVal b.threshold.y1 →
    (lowerHistoryAtBase (lowerHistoryOrient (lowerHistoryAppend base words) flip) [b] ↔
      lowerHistoryAtBase base [lowerHistoryPull b words flip])
def LowerHistoryChoiceLaw : Prop :=
  ∀ (base : LowerPair) (s : LowerHistoryState) (l : LowerLabel),
    lowerHistoryContextFits base s.context →
    lowerNormalize base = lowerHistoryOrient base s.wider →
    l ∈ lowerHistoryLabels → lowerOffered base l →
    ∃ bs ∈ lowerHistorySourceChoices s l,
      lowerHistoryAtBase (lowerHistoryOrient base s.wider) bs

def LowerHistoryGreaterLaw : Prop :=
  ∀ (base : LowerPair) (C : LowerHistoryContext), lowerHistoryContextFits base C →
    ∀ x y : CertField × CertField,
      (0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2) →
      (0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2) →
      (lowerHistoryComparisonHolds (lowerHistoryGreater C x y)
        (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
        lowerHistoryValue base C y ≤ lowerHistoryValue base C x)
def LowerHistoryWidthLaw : Prop :=
  ∀ base words : LowerPair,
    (lowerWidth (base.2++words.2) ≤ lowerWidth (base.1++words.1) ↔
      lowerHistoryAtBase base [⟨false,false,lowerHistoryWH words⟩]) ∧
    (lowerWidth (base.2++words.2) < lowerWidth (base.1++words.1) ↔
      lowerHistoryAtBase base [⟨false,true,lowerHistoryWH words⟩])

end Freiman


