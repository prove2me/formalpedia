-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
-- name    : Submission_ThreeSum_TernaryWeightChannels
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:37:28.057753+00:00
-- url     : https://prove2.me/theorems/55b737c3-9a2a-40f4-8a61-9e6f27e49646
-- title:
--   Ternary Weight Channels
-- statement:
--   Definitions and structural lemmas for Ternary Weight Channels, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightChannels.lean

import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
set_option autoImplicit false
namespace ThreeSum.TernaryWeightChannels
open Finset LightFixedArithmetic TernaryJointType TernaryWeightedPhysicalSources
open scoped BigOperators
def powerCircuit (e : Circuit) : ℕ→Circuit
  | 0 => .literal 1
  | k+1 => .mul (powerCircuit e k) e
def scalarPower (k : ℕ) : Circuit := powerCircuit (.atom 0) k
def leftMoment (k j : ℕ) : Circuit :=
  .mul (.literal (k.choose j : ℤ)) (powerCircuit (.sub (.literal 0) (.atom 0)) j)
def rightMoment (k j : ℕ) : Circuit := scalarPower (k-j)
variable {ι κ I : Type*}
def productWeight (F : ι→I→ℤ) (a b : I) (i : ι) : ℤ := F i a*F i b
end ThreeSum.TernaryWeightChannels


