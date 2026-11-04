-- Prove2me | Definitions.Def_Submission_ThreeSum_Switch
-- name    : Submission_ThreeSum_Switch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:58:12.838195+00:00
-- url     : https://prove2.me/theorems/e4a25f3b-8552-49a4-8f3f-78ba7bfc5bdb
-- title:
--   Switch
-- statement:
--   Definitions and structural lemmas for Switch, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Switch.lean

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
set_option autoImplicit false
namespace ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
def cubicNumerator (r q : ℕ) : ℕ := 799 * q * r ^ 2 + 72 * q ^ 2 * r + 24 * q ^ 3
def accepts (J j r q : ℕ) : Prop :=
  (291 * J + 1000 * j) * r ^ 3 ≤ 10 * (J - j) * cubicNumerator r q
instance (J j r q : ℕ) : Decidable (accepts J j r q) :=
  inferInstanceAs (Decidable (_ ≤ _))
def candidates (J j r : ℕ) : Finset ℕ :=
  (Finset.range (r / 2 + 1)).filter (accepts J j r)
def switchIndex (J j r : ℕ) : ℕ :=
  if h : (candidates J j r).Nonempty then (candidates J j r).min' h else 0
def residualSize (n j : ℕ) : ℕ := (blockCount (inputBits n) - j) * muZero n
def actualSwitch (n j : ℕ) : ℕ :=
  switchIndex (blockCount (inputBits n)) j (residualSize n j)
def terminalDepth (n : ℕ) : ℕ := 13 * blockCount (inputBits n) / 20
noncomputable section
end
end ThreeSum.Switch


