-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
-- name    : Submission_Weighted_Global_TernaryPreparedOriginals
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:56:06.620951+00:00
-- url     : https://prove2.me/theorems/b7215567-d02f-4e41-bb72-11863e6bae18
-- title:
--   Ternary Prepared Originals
-- statement:
--   Definitions and structural lemmas for Ternary Prepared Originals, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPreparedOriginals.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaOriginalInputs
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
import Definitions.Def_Submission_Weighted_Global_TernaryComputedExtensionMenu
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectedSigned
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalPreparedOriginals
open Light LightWeightedGlobalColorPreparation LightWeightedGlobalColorPreparationProof
open WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate WeightedGlobalArenaLayout
open WeightedGlobalArenaSeedData TernarySignedReduction TernarySignedLayout
open WeightedGlobalArenaSelectedSigned TernaryExtensionEncoding
set_option maxHeartbeats 6000000
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
def input (free n U J C0 weightCap queryTime : ℕ) (A B C : List ℤ) : Input where
  free:=arenaFree free n (LightColorParametersCosts.width n) A.length B.length C.length J U
  capacity:=C0
  prefixFree:=addr (arenaFree free n (LightColorParametersCosts.width n) A.length B.length C.length J U) C0 13
  nB:=B.length
  nC:=C.length
  leftInput:=0
  rightInput:=0
  targets:=0
  positions:=WeightedGlobalNativeRequesterCoverage.position J
  requesterCount:=A.length*2^J
  weightCap:=weightCap
  queryTime:=queryTime
def inputs (free n J menu : ℕ) (A B C : List ℤ) : Inputs where
  menu:=menu
  J:=J
  Bmatrix:=bMatrix free n (LightColorParametersCosts.width n)
  Cmatrix:=cMatrix free n (LightColorParametersCosts.width n) B.length J
  Omatrix:=oMatrix free n (LightColorParametersCosts.width n) A.length B.length C.length J
  positions:=positions free n (LightColorParametersCosts.width n) A.length B.length C.length J
  leftTagged:=bMatrix free n (LightColorParametersCosts.width n)
  rightTagged:=cMatrix free n (LightColorParametersCosts.width n) B.length J
structure Metadata (n U : ℕ) (A B C : List ℤ) : Prop where
  lengthA : A.length≤n
  lengthB : B.length≤n
  lengthC : C.length≤n
  boundA : ∀i<A.length,|A.getD i 0|≤(U:ℤ)
  boundB : ∀i<B.length,|B.getD i 0|≤(U:ℤ)
  boundC : ∀i<C.length,|C.getD i 0|≤(U:ℤ)
  injectiveB : Function.Injective (fun i : Fin B.length => B.getD i.val 0)
  injectiveC : Function.Injective (fun i : Fin C.length => C.getD i.val 0)
variable {d c : ℕ} [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus p d c))]
end ThreeSum.WeightedGlobalPreparedOriginals


