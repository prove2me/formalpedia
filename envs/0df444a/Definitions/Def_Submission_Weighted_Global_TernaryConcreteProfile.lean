-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryConcreteProfile
-- name    : Submission_Weighted_Global_TernaryConcreteProfile
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:13:28.327358+00:00
-- url     : https://prove2.me/theorems/9f171abf-9243-4399-bac5-9a2132152560
-- title:
--   Ternary Concrete Profile
-- statement:
--   Definitions and structural lemmas for Ternary Concrete Profile, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryConcreteProfile.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFixedParameters
import Definitions.Def_Submission_Weighted_Global_TernaryExecutableParameters
import Definitions.Def_Submission_Weighted_Global_TernaryColoredSolverNeed
import Definitions.Def_Submission_Weighted_Global_TernaryFastProgramResources
import Definitions.Def_Submission_Weighted_Global_TernaryActualRuntimeParameters
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_main
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_main
import Theorems.Thm_ThreeSum_TernaryCoverScale_outputSize_ge_sixteen
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_cutoff
import Theorems.Thm_ThreeSum_WeightedGlobalArenaFixedParameters_simultaneous_cutoff
import Theorems.Thm_ThreeSum_WeightedGlobalCoverScale_outputSize_ge_sixteen
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_selectedMoment_pos
attribute [local simp] ThreeSum.LightTernaryCountFrontend.main
attribute [local simp] ThreeSum.LightWeightedCountFrontend.main


set_option autoImplicit false
noncomputable section
namespace ThreeSum.WeightedGlobalConcreteProfile
open Light WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalCoverScale
open WeightedGlobalOversizePrime WeightedGlobalOversizeRates WeightedGlobalOversizeOverhead WeightedGlobalSignedPadding
open WeightedGlobalArenaFixedParameters WeightedGlobalArenaBudgetExistence
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
structure Profile (κ : ℕ) where
  K : ℕ
  t : ℕ
  m : ℕ
  cutoff : ℕ
  large : 100000000000000000000≤K
  basePositive : 0<t
  blockPositive : 0<m
  good : GoodBlock K m
  overhead : overheadCharge (selectedMoment K) 19 3 m<microAllowance K
  carry : carryExponent m (2^t) (κ : ℝ)<microAllowance K
  minor : (2*K).factorial*(2^t)^(2*K)<nativePrime K m
  basePrime : 2*(2^t)<nativePrime K m
  driftBound : (9*pairFactor m (familyLength K m) K)^4*(outputSize m)^(4*K+3)≤
    ((nativePrime K m)^(2*K))^4
  primeLarge : 9<nativePrime K m
  collisionRate : WeightedGlobalPairedCollisionRate.charge K m<(7483/10000 : ℝ)
  inputGuards : ∀n≥cutoff, InputGuards K m (2^t) κ n
theorem exists_profile (κ : ℕ) : Nonempty (Profile κ) := by
  have hKex : ∃K : ℕ, 100000000000000000000≤K := ⟨100000000000000000000,le_rfl⟩
  let K := Classical.choose hKex
  have hK : 100000000000000000000≤K := Classical.choose_spec hKex
  obtain ⟨t,m,n0,ht,hm,hg,ho,hc,hd,hp,hdrift,hp9,hcharge,hinputs⟩ :=
    simultaneous_cutoff hK κ 19 3 1
  exact ⟨⟨K,t,m,n0,hK,ht,by omega,hg,ho,hc,hd,hp,hdrift,hp9,hcharge,hinputs⟩⟩
def profile (κ : ℕ) : Profile κ := Classical.choice (exists_profile κ)
namespace Profile
variable {κ : ℕ}
def p (P : Profile κ) := nativePrime P.K P.m
def M (P : Profile κ) := outputSize P.m
def radix (P : Profile κ) := 2^P.t
def k (P : Profile κ) := selectedMoment P.K
def F (P : Profile κ) := WeightedGlobalExecutableParameters.F P.K P.m P.k
def cap (P : Profile κ) := WeightedGlobalExecutableParameters.cap P.K P.m
def threshold (P : Profile κ) := WeightedGlobalExecutableParameters.threshold P.K P.m P.k
instance (P : Profile κ) : Fact P.p.Prime := inferInstanceAs (Fact (nativePrime P.K P.m).Prime)
def maps (P : Profile κ) : Fin P.F→Weight P.m P.p :=
  WeightedGlobalExecutableParameters.maps P.K P.m P.k
def H (P : Profile κ) := 2*P.p^P.K
def drift (P : Profile κ) := 9*P.F*P.M*(WeightedGlobalGoodOutputCatalog.Rbar P.m)^P.K
def scale (P : Profile κ) := 2^((fixedPi P.m 2)*P.K)
theorem K_pos (P : Profile κ) : 0<P.K := by have := P.large; omega
theorem M_gt_one (P : Profile κ) : 1<P.M := by
  have hh := outputSize_ge_sixteen P.blockPositive
  exact lt_of_lt_of_le (by decide : 1<16) hh
theorem radix_gt_one (P : Profile κ) : 1<P.radix := by
  have hh := Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) (show 1≤P.t by have := P.basePositive; omega)
  exact lt_of_lt_of_le (by decide : 1<2) hh
theorem k_pos (P : Profile κ) : 0<P.k := selectedMoment_pos P.K_pos
def output (P : Profile κ) : WeightedGlobalGoodOutputCatalog.Output P.m :=
  WeightedGlobalExecutableParameters.output P.K_pos P.blockPositive P.k_pos
def allocation (P : Profile κ) :
    WeightedGlobalArenaAllocation.Allocation P.maps P.threshold P.cap P.M P.radix P.K P.H P.drift P.scale :=
  WeightedGlobalArenaAllocation.allocation P.maps P.threshold P.cap P.M P.radix P.K P.H P.drift P.scale
    P.M_gt_one P.radix_gt_one
def color (P : Profile κ) : Program :=
  WeightedGlobalExecutable.color P.maps P.threshold P.cap P.M P.radix P.K
    P.allocation.D P.allocation.E P.output
def program (P : Profile κ) : Program :=
  WeightedGlobalExecutable.program P.maps P.threshold P.cap P.M P.radix P.K
    P.allocation.D P.allocation.E κ P.output
def main (P : Profile κ) := WeightedGlobalExecutable.main (p:=P.p) P.K
def colorNeed (P : Profile κ) : ℕ→ℕ→Need := WeightedGlobalColoredSolverNeed.fixedNeed P.allocation κ
def need (P : Profile κ) : ℕ→ℕ→Need :=
  WeightedGlobalFastProgramResources.need P.M P.radix P.p P.K κ P.colorNeed
end Profile
end ThreeSum.WeightedGlobalConcreteProfile


