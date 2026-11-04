-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
-- name    : Submission_Weighted_Global_TernaryNativePairMoments
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T14:52:21.293598+00:00
-- url     : https://prove2.me/theorems/fcb98781-b384-4b72-ac88-10313af9a522
-- title:
--   Ternary Native Pair Moments
-- statement:
--   Definitions and structural lemmas for Ternary Native Pair Moments, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryNativePairMoments.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryMomentChannelFactory
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalTensorChannels
import Definitions.Def_Submission_ThreeSum_TernaryPhysicalMomentSupport
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalNativePairMoments
open Finset TernaryJointType
open scoped BigOperators
def leftSet {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (i : ℕ) :=
  TernarySourceHostModel.channel S.left.records S.left.group (S.front.group i)
def rightSet {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (i : ℕ) :=
  TernarySourceHostModel.channel S.right.records S.right.group (S.front.group i)
def leftWord {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (p : ℕ×ℕ) :=
  S.front.E.word (S.left.key p.2)
def rightWord {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (p : ℕ×ℕ) :=
  S.front.E.word (S.right.key p.2)
def pairs {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (i : ℕ) :
    Finset ((ℕ×ℕ)×(ℕ×ℕ)) :=
  TernaryPhysicalTensorChannels.records (leftSet S i) (rightSet S i)
    (leftWord S) (rightWord S) (S.front.Q i)
abbrev Pair {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (i : ℕ) : Type := pairs S i
def mode {N : ℕ} {S : WeightedSourceCountExecutionFactory.Setup N} {i : ℕ}
    (B C : ℕ→ℤ) (p : Pair S i) : ℤ := C p.val.2.1-B p.val.1.1
def mass {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N) (i : ℕ) (_ : Pair S i) : ℤ :=
  TernaryConvolution.factorial (S.front.Q i)
end ThreeSum.WeightedGlobalNativePairMoments


