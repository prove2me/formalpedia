-- Prove2me | Definitions.Def_Submission_ThreeSum_ReportingHostLevelData
-- name    : Submission_ThreeSum_ReportingHostLevelData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:54:11.626216+00:00
-- url     : https://prove2.me/theorems/90ca6654-c63d-4bab-9b22-1dfe789cacfa
-- title:
--   Reporting Host Level Data
-- statement:
--   Definitions and structural lemmas for Reporting Host Level Data, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ReportingHostLevelData.lean

import Definitions.Def_Submission_ThreeSum_LightReportingCatalogQuery
import Definitions.Def_Submission_ThreeSum_LightReportingFrontierStep
import Theorems.Thm_ThreeSum_ReportingHostRelocation_lookup

set_option autoImplicit false
namespace ThreeSum.ReportingHostLevelData
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
structure Catalog where
  t : ℕ
  boxCut : ℕ
  boxBase : ℕ
  indexBase : ℕ
  ptrBase : ℕ
def Catalog.record (D : Catalog) (h k : ℕ) : List ℕ :=
  [D.t,D.boxCut,D.indexBase,D.ptrBase,count h k]
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
structure Sources {h J : ℕ} (μ : ℕ→ℤ) (pMod shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β→ℤ) (c : γ→ℤ) (q : GlobalOutput h J) (baseL baseR : ℕ) : Prop where
  left : LightZetaStages.StoredThrough μ baseL (sourceCut h J) (leftSource pMod B b q) (width h J)
  right : LightZetaStages.StoredThrough μ baseR (sourceCut h J) (rightSource pMod shift C c q) (width h J)
structure Stored {h J k : ℕ} (μ : ℕ→ℤ) (D : Catalog) (hk : k≤J)
    (pMod shift : ℤ) (B : Finset β) (C : Finset γ) (b : β→ℤ) (c : γ→ℤ)
    (q : GlobalOutput h J) : Prop where
  index : ∃ S : List ℤ, Seg μ D.indexBase S ∧
    S.Perm (ReportingHostPackedCatalog.codes (ReportingHostPackedCatalog.prefixKey h J k) (count h k)) ∧
    S.Pairwise (· ≤ ·)
  pointers : SegN μ D.ptrBase (List.ofFn fun i : Fin (count h k) =>
    D.boxBase+i.val*stride (suffixStage J (512*h) k) D.boxCut)
  boxes : ∀ i<count h k, LightBoxStages.StoredThrough μ
    (D.boxBase+i*stride (suffixStage J (512*h) k) D.boxCut) D.boxCut
    (leafWeight (block_fit hk) (leftSource pMod B b q) (rightSource pMod shift C c q)
      (suffixStage J (512*h) k) (preL h J k i) (preR h J k i)) (suffixStage J (512*h) k)
structure Bounds (h J k : ℕ) (D : Catalog) (baseL baseR stop : ℕ) : Prop where
  left : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J)≤stop
  right : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J)≤stop
  index : D.indexBase+count h k≤stop
  pointers : D.ptrBase+count h k≤stop
  boxes : D.boxBase+count h k*stride (suffixStage J (512*h) k) D.boxCut≤stop
structure Scratch (lim : Limits) (h J k : ℕ) (D : Catalog) (bCard cCard maskBase work : ℕ) : Prop where
  masks : maskBase+LightSparseQuery.queryItems (residualSize h J k) D.t≤work
  space : work+1+tableSize (width h J)+(width h J+1)≤lim.space
  powers : work+(2*width h J+2)≤lim.space
  emod : work+(Nat.log 2 (LightReportingCatalogLookup.valueBound (width h J) (count h k)+1)+2)≤lim.space
  word : (((width h J+1)*2^(width h J+1) : ℕ) : ℤ)≤lim.word
  lookup : (LightReportingCatalogLookup.word (width h J) (count h k) : ℤ)≤lim.word
  values : (LightSparseQuery.magnitudeBound (suffixStage J (512*h) k) (suffixStage J (512*h) k)
    (residualSize h J k) D.t bCard cCard : ℤ)≤lim.word
  t : D.t≤residualSize h J k+1
  cut : D.boxCut≤residualSize h J k
  flags : residualSize h J k-D.t≤D.boxCut
end ThreeSum.ReportingHostLevelData


