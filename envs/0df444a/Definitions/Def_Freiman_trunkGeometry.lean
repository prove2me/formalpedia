-- Prove2me | Definitions.Def_Freiman_trunkGeometry
-- name    : Freiman_trunkGeometry
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T14:26:25.108848+00:00
-- url     : https://prove2.me/theorems/dee2c21e-2e48-42db-8d7b-0eddeff20ddc
-- title:
--   trunkGeometry
-- statement:
--   Original pp120–126 trunk finite catalog and pure exact-rational endpoint/checker semantics. Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkData

namespace Freiman

noncomputable def trunkLocalUpper (p : LowerPair) (l : LowerLabel) : ℝ :=
  if (lowerNormalize p).1.length % 2 = 0 then lowerEndpoint (lowerChild p l) true
  else -lowerEndpoint (lowerChild p l) false
noncomputable def trunkParentEndpoint (p : LowerPair) (upper : Bool) : ℝ :=
  if (lowerNormalize p).1.length % 2 = 0 then lowerEndpoint p upper
  else -lowerEndpoint p (!upper)
structure TrunkGeometry (p : LowerPair) (plan : TrunkPlan) : Prop where
  nonempty : ∀ l ∈ plan.labels, (lowerCover (lowerChild p l)).Nonempty
  strictGood : ∀ l ∈ plan.labels, lowerStrictGood (lowerChild p l)
  contacts : ∀ lm ∈ plan.labels.zip plan.labels.tail, lm ∉ plan.holes →
    (lowerCover (lowerChild p lm.1) ∩ lowerCover (lowerChild p lm.2)).Nonempty
  upper : ∀ l, plan.labels.head? = some l → trunkParentEndpoint p true ≤ trunkLocalUpper p l
  lower : ∀ l, plan.labels.getLast? = some l → lowerLocalLower p l ≤ trunkParentEndpoint p false

def TrunkMode (p : LowerPair) (k : Fin 16) (pi par : ℕ) : Prop :=
  let S := trunkCatalog.states k
  let Z := lowerNormalize p
  lowerHistoryContextFits Z S.context ∧
  certRectangleMem S.rectangle (lowerRatio Z.1) (lowerRatio Z.2) ∧
  pi < (trunkSourcePlans S.context).length ∧ par < (trunkParents S.context).length ∧
  trunkHolds (trunkBaseConditions S pi par) (lowerRatio Z.1) (lowerRatio Z.2) (lowerScale Z)
def TrunkGeometryLaw : Prop :=
  ∀ (p : LowerPair) (k : Fin 16) (pi par : ℕ), TrunkMode p k pi par →
    TrunkGeometry p (trunkPlanAt (trunkCatalog.states k) pi)
def TrunkSourceGeometry (p : LowerPair) : Prop :=
  ∀ (k : Fin 16) (pi par : ℕ), TrunkMode p k pi par →
    TrunkGeometry p (trunkPlanAt (trunkCatalog.states k) pi)
def trunkWitnessBatch (lo hi : ℕ) : Prop :=
  ∀ i : ℕ, lo ≤ i → i < hi → trunkWitnessValid trunkCatalog (trunkWitness trunkCatalog (i+1))
def trunkBindingBatch (k : Fin 16) (lo hi : ℕ) : Prop :=
  ∀ i : ℕ, lo ≤ i → i < hi → ∀ g, (trunkCatalog.states k).groups[i]? = some g →
    trunkGroupValid trunkCatalog k g
def TrunkWitnessExclusion (C : TrunkCatalog) (w : TrunkWitness) : Prop :=
  ∀ (l u : CertBound), trunkUseBounds C w l u →
  ∀ r s q : ℝ, certRectangleMem w.rectangle r s →
    (w.diagonal = 0 ∨ 0 ≤ (w.diagonal : ℝ)*(r-s)) →
    ¬ (certBoundHolds l r s q ∧ certBoundHolds u r s q)
def TrunkTreeSound (C : TrunkCatalog) : Prop :=
  ∀ (R : CertRectangle) (bs : List CertBound) (tree : TrunkTree),
    certRectangleValid R → trunkTreeBound C R bs tree →
    ∀ r s q : ℝ, certRectangleMem R r s → ¬ trunkHolds bs r s q

noncomputable def trunkLocalEndpoint (p : LowerPair) (words : LowerPair) (upper : Bool) : ℝ :=
  let Z := lowerNormalize p
  if Z.1.length % 2 = 0 then lowerEndpoint (Z.1++words.1,Z.2++words.2) upper
  else -lowerEndpoint (Z.1++words.1,Z.2++words.2) (!upper)
noncomputable def trunkFramedEndpoint (base : LowerPair) (C : LowerHistoryContext)
    (words : LowerPair) (upper incoming : Bool) : ℝ :=
  (if lowerHistoryCommonOdd base C then -1 else 1) *
    lowerEndpoint (lowerHistoryOrient (lowerHistoryAppend base words) incoming)
      (upper.xor (lowerHistoryCommonOdd base C))
noncomputable def trunkSpecLocalEndpoint (p : LowerPair) (words : LowerPair) (upper incoming : Bool) : ℝ :=
  let Z := lowerNormalize p
  let physical := lowerHistoryOrient (lowerHistoryAppend Z words) incoming
  if Z.1.length % 2 = 0 then lowerEndpoint physical upper else -lowerEndpoint physical (!upper)
noncomputable def trunkSpecHolds (p : LowerPair) (s : Section14Spec) : Prop :=
  let Z := lowerNormalize p
  trunkHolds s.extra (lowerRatio Z.1) (lowerRatio Z.2) (lowerScale Z) →
    if s.strict then
      trunkSpecLocalEndpoint p s.second s.secondUpper (trunkSpecIncoming s) <
        trunkSpecLocalEndpoint p s.first s.firstUpper (trunkSpecIncoming s)
    else trunkSpecLocalEndpoint p s.second s.secondUpper (trunkSpecIncoming s) ≤
      trunkSpecLocalEndpoint p s.first s.firstUpper (trunkSpecIncoming s)
def TrunkEndpointLaw : Prop :=
  ∀ (base : LowerPair) (C : LowerHistoryContext), lowerHistoryContextFits base C →
  ∀ (words : LowerPair) (upper incoming : Bool), ∃ z cs,
    (z,cs) ∈ trunkEndpointCases C words upper incoming ∧ lowerHistoryAtBase base cs ∧
    trunkFramedEndpoint base C words upper incoming = lowerHistoryValue base C z ∧
    0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2
def TrunkGreaterLaw : Prop :=
  ∀ (base : LowerPair) (C : LowerHistoryContext), lowerHistoryContextFits base C →
  ∀ (x y : CertField × CertField),
    (0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2) →
    (0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2) → ∀ strict : Bool,
    (lowerHistoryComparisonHolds (trunkGreater C x y strict)
      (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
      if strict then lowerHistoryValue base C y < lowerHistoryValue base C x
      else lowerHistoryValue base C y ≤ lowerHistoryValue base C x)

noncomputable def TrunkActiveGeometry (p : LowerPair) : Prop :=
  ∃ k : Fin 16,
    lowerHistoryContextFits (lowerNormalize p) (trunkCatalog.states k).context ∧
    certRectangleMem (trunkCatalog.states k).rectangle
      (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2) ∧
    ∀ pi : ℕ, pi < (trunkSourcePlans (trunkCatalog.states k).context).length →
      trunkHolds (trunkPlanAt (trunkCatalog.states k) pi).cuts
        (lowerRatio (lowerNormalize p).1) (lowerRatio (lowerNormalize p).2)
        (lowerScale (lowerNormalize p)) →
      TrunkGeometry p (trunkPlanAt (trunkCatalog.states k) pi)

end Freiman


