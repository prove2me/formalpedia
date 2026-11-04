-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
-- name    : Submission_ThreeSum_TernaryCodeSemantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:35:52.080559+00:00
-- url     : https://prove2.me/theorems/d6a0266c-9cb0-4cca-8dde-d929b0b4ad6d
-- title:
--   Ternary Code Semantics
-- statement:
--   Definitions and structural lemmas for Ternary Code Semantics, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
namespace ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000
def low {N : ℕ} (i : Fin N) : ℕ := 2*(N-1-i.val)
def high {N : ℕ} (i : Fin N) : ℕ := low i+1
def bitPosition {N : ℕ} (p : Fin N × Fin 2) : ℕ := low p.1+p.2.val
def live {N : ℕ} (w : TritWord N) (p : Fin N × Fin 2) : Prop :=
  if p.2=0 then 0<(w p.1).val else w p.1=2
instance {N : ℕ} (w : TritWord N) (p : Fin N × Fin 2) : Decidable (live w p) := by
  unfold live
  infer_instance
def supportPairs {N : ℕ} (w : TritWord N) : Finset (Fin N × Fin 2) :=
  univ.filter (live w)
def support {N : ℕ} (w : TritWord N) : Finset ℕ :=
  (supportPairs w).image bitPosition
def address {N : ℕ} (w : TritWord N) : ℕ := code (wordList w)
def clampOne (d : Fin 3) : Fin 3 := if d=0 then 0 else 1
def lowerCode {N : ℕ} (w : TritWord N) (i : Fin N) (d : Fin 3) : ℕ :=
  if d=0 then LightTernaryCodes.zeroCode (2*N) (low i) (high i) (address w)
  else if d=1 then LightTernaryCodes.oneCode (2*N) (high i) (address w)
  else address w
end ThreeSum.TernaryCodeSemantics


