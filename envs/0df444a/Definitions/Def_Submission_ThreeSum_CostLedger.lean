-- Prove2me | Definitions.Def_Submission_ThreeSum_CostLedger
-- name    : Submission_ThreeSum_CostLedger
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:02:24.382062+00:00
-- url     : https://prove2.me/theorems/6869f45d-559d-429f-9edd-3428262c2a14
-- title:
--   Cost Ledger
-- statement:
--   Definitions and structural lemmas for Cost Ledger, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/CostLedger.lean

import Definitions.Def_Submission_ThreeSum_Switch
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false
namespace ThreeSum.CostLedger
open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators
set_option maxHeartbeats 400000
def bandCount (n : ℕ) : ℕ := n ⌈/⌉ BandScales.bandSize n
def microOutputs (n : ℕ) : ℕ := (256 * muZero n).choose (muZero n)
def microPartitions (n : ℕ) : ℕ := (muZero n).choose (muZero n / 2)
def prefixChoices (n j : ℕ) : ℕ := (microOutputs n * microPartitions n) ^ j
def suffixBoxes (n j : ℕ) : ℕ :=
  (256 * residualSize n j).choose (residualSize n j - actualSwitch n j)
def prefixBoxes (n j : ℕ) : ℕ := prefixChoices n j * suffixBoxes n j
def queryTerms (n j : ℕ) : ℕ := (residualSize n j).choose (actualSwitch n j)
def allPrefixBoxes (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (terminalDepth n + 1), prefixBoxes n j
def allQueryTerms (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (terminalDepth n + 1), queryTerms n j
noncomputable section
end
end ThreeSum.CostLedger


