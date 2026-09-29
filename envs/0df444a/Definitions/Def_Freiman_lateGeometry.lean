-- Prove2me | Definitions.Def_Freiman_lateGeometry
-- name    : Freiman_lateGeometry
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:33:31.510448+00:00
-- url     : https://prove2.me/theorems/a8cb67e6-bd1a-4927-ad53-c898db20894c
-- title:
--   Freiman late: lateGeometry
-- statement:
--   Exact source late decision catalogue, shared-kernel finite validator or actual-cover interface; no theorem/axiom declarations.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateData
import Definitions.Def_Freiman_lowerHistoryVerification

namespace Freiman

noncomputable def lateR (p : LowerPair) : ℝ := lowerRatio (lowerNormalize p).1
noncomputable def lateS (p : LowerPair) : ℝ := lowerRatio (lowerNormalize p).2
noncomputable def lateQ (p : LowerPair) : ℝ := lowerScale (lowerNormalize p)
def lateMatches (p : LowerPair) (right3 : Bool) : Prop :=
  ¬ lowerMixed p ∧ lowerL p ∧
  (right3 = true ↔ lowerEnds (lowerNormalize p).2 [3])
noncomputable def lateActualEndpoint (p : LowerPair) (words : LowerPair) (upper : Bool) : ℝ :=
  lowerHistoryEndpointReal (lowerNormalize p) (lateContext false) words upper
noncomputable def lateActualValue (p : LowerPair) (z : CertField × CertField) : ℝ :=
  lowerHistoryValue (lowerNormalize p) (lateContext false) z
noncomputable def lateSpecHolds (p : LowerPair) (sp : LateSpec) : Prop :=
  if sp.2.2.2.2 then
    lateActualEndpoint p sp.2.2.1 sp.2.2.2.1 < lateActualEndpoint p sp.1 sp.2.1
  else lateActualEndpoint p sp.2.2.1 sp.2.2.2.1 ≤ lateActualEndpoint p sp.1 sp.2.1
def lateValueComparison (p : LowerPair) (x y : CertField × CertField) (strict : Bool) : Prop :=
  if strict then lateActualValue p y < lateActualValue p x
  else lateActualValue p y ≤ lateActualValue p x
def lateNormalizationHolds (p : LowerPair) (n : LateNormalization) : Prop :=
  let child := lowerChild p n.label
  lowerNormalize child =
    if n.wide then (child.2,child.1) else child
def lateForkAlignment (p : LowerPair) (path : LatePath) : Prop :=
  ∀ n ∈ path.normalizations, ∀ d ∈ ([1,2] : List ℕ+), ∀ upper : Bool,
    lowerEndpoint (lowerChild (lowerChild p n.label) ([d],[])) upper =
      lowerEndpoint (lowerHistoryAppend (lowerNormalize p) (lateForkWords n d)) upper
def lateProofSound (C : LateCatalog) : Prop :=
  ∀ fuel bs R id, lateProofValid C fuel bs R id →
    ∀ r s q : ℝ, certRectangleMem R r s → ¬ lateHolds bs r s q
def lateEndpointLaw : Prop :=
  ∀ (p : LowerPair) (e : LateEndpoint), lateMatches p e.right3 →
    e.words.1 ≠ [] → e.words.2 ≠ [] → lateEndpointValid lateCatalog e →
    ∀ ids ∈ e.modes,
      lateHolds (lateBounds lateCatalog ids) (lateR p) (lateS p) (lateQ p) →
      lateActualEndpoint p e.words e.upper = lateActualValue p e.value
def lateGreaterLaw : Prop :=
  ∀ (p : LowerPair), ¬ lowerMixed p → ∀ x y : CertField × CertField,
    0 ≤ certFieldVal x.1 → 0 ≤ certFieldVal x.2 →
    0 ≤ certFieldVal y.1 → 0 ≤ certFieldVal y.2 →
    ∀ strict,
      lowerHistoryComparisonHolds (lateGreater x y strict) (lateR p) (lateS p) (lateQ p) →
      lateValueComparison p x y strict
def lateChecksLaw : Prop :=
  ∀ (p : LowerPair) (i : ℕ), lateIndex i lateCatalog.paths.size →
    lateMatches p (latePath lateCatalog i).right3 →
    latePathValid lateCatalog (latePath lateCatalog i) →
    lateAllEndpoints lateCatalog →
    lateHolds (lateBounds lateCatalog (latePath lateCatalog i).required) (lateR p) (lateS p) (lateQ p) →
    ∀ c ∈ (latePath lateCatalog i).checks, lateSpecHolds p (lateCheckSpec lateCatalog c)

end Freiman


