-- Prove2me | Definitions.Def_Submission_ThreeSum_SharedReportingBankData
-- name    : Submission_ThreeSum_SharedReportingBankData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:58:28.258477+00:00
-- url     : https://prove2.me/theorems/4a774051-3710-4546-a94e-85ed4d1a2d22
-- title:
--   Shared Reporting Bank Data
-- statement:
--   Definitions and structural lemmas for Shared Reporting Bank Data, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankData.lean

import Definitions.Def_Submission_ThreeSum_ReportingHostLevelData
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogIndex
set_option autoImplicit false
namespace ThreeSum.SharedReportingBankData
open Light SubsetAddress ReportingHostSuffix ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData
set_option maxHeartbeats 1500000
set_option maxRecDepth 9000
structure Tables {h J k : ℕ} (μ : ℕ → ℤ) (D : Catalog) (hk : k ≤ J)
    (f g : Finset (Fin (J*(512*h))) → ℤ) : Prop where
  index : ∃ S : List ℤ, Seg μ D.indexBase S ∧
    S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J k) (count h k)) ∧
    S.Pairwise (· ≤ ·)
  pointers : SegN μ D.ptrBase (List.ofFn fun i : Fin (count h k) =>
    D.boxBase+i.val*stride ((J-k)*(512*h)) D.boxCut)
  boxes : ∀ i < count h k, LightBoxStages.StoredThrough μ
    (D.boxBase+i*stride ((J-k)*(512*h)) D.boxCut) D.boxCut
    (leafWeight (block_fit hk) f g ((J-k)*(512*h)) (preL h J k i) (preR h J k i))
    ((J-k)*(512*h))
structure Entry {h J k : ℕ} (μ : ℕ → ℤ) (record : ℕ) (D : Catalog) (hk : k ≤ J)
    (f g : Finset (Fin (J*(512*h))) → ℤ) : Prop where
  header : SegN μ record (D.record h k)
  tables : Tables μ D hk f g
end ThreeSum.SharedReportingBankData


