-- Prove2me | Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
-- name    : Submission_ThreeSum_SharedReportingBankLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:02:26.651638+00:00
-- url     : https://prove2.me/theorems/3b388183-d7b1-4276-acb6-91a0f9c6a251
-- title:
--   Shared Reporting Bank Layout
-- statement:
--   Definitions and structural lemmas for Shared Reporting Bank Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLayout.lean

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
set_option autoImplicit false
namespace ThreeSum.SharedReportingBankLayout
open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000
def localWidth (h : ℕ) : ℕ := 512*h
def width (h J : ℕ) : ℕ := J*localWidth h
def suffixWidth (h J k : ℕ) : ℕ := (J-k)*localWidth h
def localChoose (h : ℕ) : ℕ := (localWidth h).choose h
def localPairs (h : ℕ) : ℕ := LightReportingPrefixArrays.localCount (localWidth h) h
def prefixSpan (h k : ℕ) : ℕ := LightRadixKeys.offset (localPairs h) k+1+count h k
def cap (h J k boxCut : ℕ) : ℕ := downsetCap (suffixWidth h J k) boxCut
def pairL (base h : ℕ) : ℕ := base+localChoose h
def pairR (base h : ℕ) : ℕ := pairL base h+localPairs h
def stageL (base h : ℕ) : ℕ := pairR base h+localPairs h
def stageR (base h k : ℕ) : ℕ := stageL base h+prefixSpan h k
def pointers (base h k : ℕ) : ℕ := stageR base h k+prefixSpan h k
def boxes (base h k : ℕ) : ℕ := pointers base h k+count h k
def masks (base h J k boxCut : ℕ) : ℕ :=
  boxes base h k+count h k*stride (suffixWidth h J k) boxCut
def index (base h J k boxCut : ℕ) : ℕ := masks base h J k boxCut
def work (base h J k boxCut : ℕ) : ℕ := masks base h J k boxCut+cap h J k boxCut+count h k
def finish (base h J k boxCut : ℕ) : ℕ :=
  work base h J k boxCut+2*localWidth h+2+1+tableSize (width h J)+(width h J+1)+count h k
def cellSize (h J k boxCut : ℕ) : ℕ := finish 0 h J k boxCut
def catalog (base h J k boxCut t : ℕ) : ReportingHostLevelData.Catalog :=
  ⟨t,boxCut,boxes base h k,index base h J k boxCut,pointers base h k⟩
def levelOffset (h J : ℕ) (boxCut : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => levelOffset h J boxCut k+cellSize h J k (boxCut k)
end ThreeSum.SharedReportingBankLayout


