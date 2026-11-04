-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryColoredLoopSetup
-- name    : Submission_Weighted_Global_TernaryColoredLoopSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:59:23.114851+00:00
-- url     : https://prove2.me/theorems/c4e95e79-657f-44d0-91b0-7e48ba25a51e
-- title:
--   Ternary Colored Loop Setup
-- statement:
--   Definitions and structural lemmas for Ternary Colored Loop Setup, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryColoredLoopSetup.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLoopState
import Definitions.Def_Submission_Weighted_Global_TernaryPreparedOriginals
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixPrepareAllocation
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSelectorAllocation
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_menuDegree_pos
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFrontBounds_capacity
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseBudget_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPhaseFrames_output
import Theorems.Thm_ThreeSum_WeightedGlobalArenaScoreScan_initial
set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalColoredLoopSetup
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open WeightedGlobalConcreteProfile WeightedGlobalLocalParameters
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}
def J (P : Profile κ) (n : ℕ) :=
  LightWeightedGlobalDimensions.J P.M P.radix n (n ^ κ)
def rounds (P : Profile κ) (n : ℕ) :=
  LightWeightedGlobalDimensions.r P.M n
def dim (P : Profile κ) (n : ℕ) :=
  LightWeightedGlobalDimensions.dim P.M P.radix P.p P.K n (n ^ κ)
def q (P : Profile κ) (n : ℕ) :=
  P.p ^ (dim P n)
def cells (P : Profile κ) (n : ℕ) :=
  capacity P.allocation.D P.allocation.E (n + n ^ κ)
def weight (P : Profile κ) (n : ℕ) :=
  WeightedGlobalArenaPrefixFootprints.weight P.H (4 ^ fixedLength P.m) (n ^ κ)
def baseInput (P : Profile κ) (n free : ℕ) (A B C : List ℤ) : Input :=
  WeightedGlobalPreparedOriginals.input free n (n ^ κ) (J P n) (cells P n) (weight P n) 0 A B C
def queryTime (P : Profile κ) (n free : ℕ) (A B C : List ℤ) : ℕ :=
  (Finset.range (rounds P n + 1)).sup fun j =>
    WeightedGlobalArenaCountReady.queryTime (m := P.m) (r := j) (baseInput P n free A B C)
      (valueCap (r := j) P.maps P.cap (baseInput P n free A B C))
def input (P : Profile κ) (n free : ℕ) (A B C : List ℤ) : Input :=
  { baseInput P n free A B C with queryTime := queryTime P n free A B C }
def arrays (P : Profile κ) (n free menu : ℕ) (A B C : List ℤ) : Inputs :=
  WeightedGlobalPreparedOriginals.inputs free n (J P n) menu A B C
def initialBudget (P : Profile κ) (n : ℕ) (A : List ℤ) :=
  LightTernaryInitialBudgets.initial P.K P.radix n (J P n) (A.length * 2 ^ (J P n))
abbrev Extension (P : Profile κ) (n c : ℕ) :=
  AdjoinRoot (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c)
theorem dim_pos (P : Profile κ) (n : ℕ) : 0 < dim P n :=
  TernaryExtensionEncoding.menuDegree_pos (p := P.p) (J P n + 2) P.K
def setup (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ → ℤ)
    [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))] :
    WeightedGlobalArenaLoop.Setup P.p P.m P.F P.K (q P n * q P n) (Extension P n c)
    where
  maps := P.maps
  threshold := P.threshold
  cap := P.cap
  Q := P.output
  M := P.M
  radix := P.radix
  H := P.H
  drift := P.drift
  scale := P.scale
  allocation := P.allocation
  input := input P n free A B C
  arrays := arrays P n free menu A B C
  n := n
  U := n ^ κ
  rounds := rounds P n
  U0 := initialBudget P n A
  featureBound := P.radix
  tagBound := P.radix
  positionCap := n
  valueTag := n ^ κ
  V := 0
  scoreBound := 0
  enumeration := WeightedGlobalComputedExtensionMenu.seeds
  ell := WeightedGlobalComputedExtensionMenu.functional (dim_pos P n)
  L := WeightedGlobalArenaSelectedSigned.left (n ^ κ) P.radix (J P n) (fun i => B.getD i 0)
  R := WeightedGlobalArenaSelectedSigned.right (n ^ κ) P.radix (J P n) (fun i => C.getD i 0)
  O := WeightedGlobalArenaSelectedSigned.requester (n ^ κ) P.radix (J P n) (fun i => A.getD i 0)
  catalogs := fun _ _ _ => 0
  initial := μ
section Facts
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ → ℤ)
variable [Fact (Irreducible (WeightedGlobalComputedExtensionMenu.modulus P.p (dim P n) c))]
end Facts
end ThreeSum.WeightedGlobalColoredLoopSetup


