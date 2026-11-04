-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceBandBankData
-- name    : Submission_ThreeSum_SourceBandBankData
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:02:48.332918+00:00
-- url     : https://prove2.me/theorems/e55f685f-01a3-4463-8602-e739ccc63b5f
-- title:
--   Source Band Bank Data
-- statement:
--   Definitions and structural lemmas for Source Band Bank Data, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceBandBankData.lean

import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
set_option autoImplicit false
namespace ThreeSum.SourceBandBankData
open Light GlobalEncoding SourceBandBankLayout OutputDecodeRecords
def first (base : ℕ) : ℕ := base+5
def finish (base NL NR g h J cut : ℕ) : ℕ :=
  baseAt (first base) h J cut (SourceBandPairSlices.count NL NR g)
def header (base NL NR g h J cut occ : ℕ) : List ℤ :=
  [first base,SourceBandPairSlices.count NL NR g,span h J cut,
    finish base NL NR g h J cut,occ]
structure Stored (μ : ℕ → ℤ) (fL fR : ℕ → ℤ) (base NL NR g h J cut occ : ℕ) (p shift : ℤ) : Prop where
  heads : Seg μ base (header base NL NR g h J cut occ)
  banks : ∀ i < SourceBandPairSlices.count NL NR g,
    At μ fL fR (first base) NL NR g h J cut p shift i
  rows : ∀ k < LightBlockSourceCatalog.count h J, ∀ j < J,
    μ (occ+k*J+j)=((OutputDecodeOrder.indices (scheduleSize h) J k).getD j 0 : ℤ)
end ThreeSum.SourceBandBankData


