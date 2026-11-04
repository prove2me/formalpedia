-- Prove2me | Definitions.Def_Submission_ThreeSum_SourceFiniteCosts
-- name    : Submission_ThreeSum_SourceFiniteCosts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T12:51:58.009755+00:00
-- url     : https://prove2.me/theorems/5ae800f5-a446-4b90-ad73-82d419027a63
-- title:
--   Source Finite Costs
-- statement:
--   Definitions and structural lemmas for Source Finite Costs, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFiniteCosts.lean

import Definitions.Def_Submission_ThreeSum_SourceControlCosts
set_option autoImplicit false
namespace ThreeSum.SourceFiniteCosts
open Scales TrimScales StageBounds CostLedger BandScales
def time (n p U D : ℕ) : ℕ :=
  (LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)+
    2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
    SourceControlCosts.factor (microHalf (inputBits n)) (blockCount (inputBits n))+5705)*encoderCount n+4859
def space (base n p U D : ℕ) : ℕ :=
  base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n+
      (256*mu n+1)^2+(256*mu n+1))*encoderCount n+
    Nat.log 2 (scheduleCount n+1)+
    max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2)+19
def finish (base n : ℕ) : ℕ :=
  base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n)*encoderCount n+17
def word (n p U D : ℕ) : ℕ :=
  LightSourceControlsHost.word n n (bandSize n) p
    (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D
end ThreeSum.SourceFiniteCosts


