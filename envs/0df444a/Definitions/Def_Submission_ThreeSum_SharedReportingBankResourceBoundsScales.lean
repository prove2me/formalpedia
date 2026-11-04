-- Prove2me | Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
-- name    : Submission_ThreeSum_SharedReportingBankResourceBoundsScales
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:17:55.996604+00:00
-- url     : https://prove2.me/theorems/39b0bf7b-df29-4106-bbde-ef0695223735
-- title:
--   Shared Reporting Bank Resource Bounds Scales
-- statement:
--   Definitions and structural lemmas for Shared Reporting Bank Resource Bounds Scales, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SharedReportingBankResourceBoundsScales.lean

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Theorems.Thm_ThreeSum_SourceBandFinite_occurrence

set_option autoImplicit false
namespace ThreeSum.SharedReportingBankResourceBounds
open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000
def half (n : ℕ) : ℕ := microHalf (inputBits n)
def blocks (n : ℕ) : ℕ := blockCount (inputBits n)
def magnitude (n : ℕ) : ℕ := 2^(2048*(inputBits n+1))
def polynomialPart (n : ℕ) : ℕ := 5000*(magnitude n+1)^5*(n+1)^2
def envelope (n : ℕ) : ℕ := polynomialPart n+(magnitude n)^64
def scaledWord (n : ℕ) : ℕ := word (half n) (blocks n) n (BandScales.bandSize n)
def scaledExtent (n : ℕ) : ℕ := extent (half n) (blocks n) n
def scaledDepth (n : ℕ) : ℕ := depth (half n) (blocks n)
structure Components (n : ℕ) : Prop where
  positive : 1 ≤ magnitude n
  localWidthBound : 512*half n+1 ≤ magnitude n
  blocksBound : blocks n+1 ≤ magnitude n
  levelsBound : levels (blocks n)+1 ≤ magnitude n
  widthBound : width (half n) (blocks n)+1 ≤ magnitude n
  prefixBound : prefixCount (half n) (blocks n) ≤ magnitude n
  localPower : 2^(512*half n+1) ≤ magnitude n
  pairsPower : 2^(2*(512*half n)) ≤ magnitude n
  widthPower : 2^(width (half n) (blocks n)+1) ≤ magnitude n
  indexPower : 2^(2*width (half n) (blocks n)) ≤ magnitude n
  occurrence : LightBlockSourceCatalog.count (half n) (blocks n) ≤ magnitude n
  prime : LocalCoverBounds.localPrime (half n) ≤ magnitude n
  primePower : LocalCoverBounds.localPrime (half n)^(blocks n)*LocalCoverBounds.localPrime (half n) ≤ magnitude n
  radixPower : (2^(512*half n)+1)^(blocks n) ≤ magnitude n
  switchBase : blocks n+2*half n*blocks n+1001 ≤ magnitude n
  depthWord : LightSwitchDepth.word (blocks n) ≤ magnitude n
end ThreeSum.SharedReportingBankResourceBounds


