-- Prove2me | Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
-- name    : Submission_ThreeSum_SharedReportingBankLevels
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:12:54.038184+00:00
-- url     : https://prove2.me/theorems/4e5d2e51-136c-4392-80cc-b0ec6de5790a
-- title:
--   Shared Reporting Bank Levels
-- statement:
--   Definitions and structural lemmas for Shared Reporting Bank Levels, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankLevels.lean

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
set_option autoImplicit false
namespace ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000
def residual (h J k : ℕ) : ℕ := 2*h*(J-k)
def switch (h J k : ℕ) : ℕ := Switch.switchIndex J k (residual h J k)
def boxCut (h J k : ℕ) : ℕ := residual h J k-switch h J k
def offset (h J : ℕ) : ℕ → ℕ := levelOffset h J (boxCut h J)
def baseAt (base h J k : ℕ) : ℕ := base+offset h J k
def catalogAt (base h J k : ℕ) : ReportingHostLevelData.Catalog :=
  catalog (baseAt base h J k) h J k (boxCut h J k) (switch h J k)
def Built (μ : ℕ → ℤ) (record base h J K : ℕ)
    (f g : Finset (Fin (J*(512*h))) → ℤ) : Prop :=
  ∀ k < K, ∃ hk : k ≤ J, Entry μ (record+5*k) (catalogAt base h J k) hk f g
end ThreeSum.SharedReportingBankLevels


