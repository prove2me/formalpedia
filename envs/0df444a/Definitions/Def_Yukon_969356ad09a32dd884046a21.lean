-- Prove2me | Definitions.Def_Yukon_969356ad09a32dd884046a21
-- name    : Yukon_969356ad09a32dd884046a21
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T11:24:26.374794+00:00
-- url     : https://prove2.me/theorems/f567983c-0ca7-4601-b04c-077705ecfbc0
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberInitialCore6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberInitialCore6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberInitialCore6814.lean
--
--   yukon-proof-operation:foundation-direct-b336ea30b4bad730e6ce0a820bf981d282a676858320dc61326376ffe51328f7
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNGRhYzNjODRhMjIyNmVhYzI0NGE3NWI2NzBkZTRjMDRjOWUyZDhhNjBiNjU0OGQwZjExMjUwMjlhYjM3YmUyOSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWIzMzZlYTMwYjRiYWQ3MzBlNmNlMGE4MjBiZjk4MWQyODJhNjc2ODU4MzIwZGM2MTMyNjM3NmZmZTUxMzI4ZjciLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl85NjkzNTZhZDA5YTMyZGQ4ODQwNDZhMjEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_8bce6c5c34a90d671d777e22

import Definitions.Def_Yukon_b8e3ef30ac92375cae4e4160

import Definitions.Def_Yukon_9fd7c568bc98e339bf933fdc

import Definitions.Def_Yukon_68c36723892eb4da8b78c8fc



















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
section InitialGeometry
namespace ProximityPrize.SubmissionLower.Lower80889.InitialSupports
open RCN130 RCN238 RCN275
-- Raw cumulative support caps for the common carrier and its A-universal factors.
def wideSupport : ResidualSupportParameters := ⟨40, 185, 10714, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
def wholeSupport : ResidualSupportParameters := ⟨37, 175, 10714, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
end ProximityPrize.SubmissionLower.Lower80889.InitialSupports
namespace ProximityPrize.SubmissionLower.Lower80889.InitialBridge

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN081 RCN095 RCN100 RCN101 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN243 RCN259 RCN260 RCN266 RCN275 RCN319
open Selection LocatorFactorAggregate LocatorBatchProductRoute

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

local instance _root_.ProximityPrize.SubmissionLower.Lower80889.InitialBridge.instDecidableEqK :DecidableEq K:=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.Lower80889.InitialBridge.instDecidableEqI :DecidableEq I:=Classical.decEq _
local instance _root_.ProximityPrize.SubmissionLower.Lower80889.InitialBridge.instGCDMonoidP4 :GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4

/-- Exact direct helper charge for one factor exiting at the A source. -/
def initialAHelperCap (p:FlagDegree):ℕ:=
  AsymmetricHelper.leftRegularCountCap (Lower80889.FactorSwitch.helperPair
    188820 175 37 (middle p) p.all (total p))

/-- Linear reconstruction of the independent A source. -/
def initialAMap (u0 u1:I → K):Caps.AKernel u0 u1 →ₗ[K] P4:=
  kernelReconstructLinear (K:=K) 23019385 131071 188820 37 127
    IRSProfile.domain u0 u1

/-- Factors universal on the current A source. -/
def initialAUniversalFactors (u0 u1:I → K) (H:P4):
    Finset (RegularIndex H):=
  universalFactors H (Finset.univ:Finset (RegularIndex H))
    (initialAMap u0 u1)

@[simp] theorem mem_initialAUniversalFactors
    (u0 u1:I → K) (H:P4) (F:RegularIndex H):
    F ∈ initialAUniversalFactors u0 u1 H ↔
      ∀ v:Caps.AKernel u0 u1,
        F.1 ∣ reconstruct K 23019385 131071 188820 37 v.1:=by
  simp only [initialAUniversalFactors,mem_universalFactors,Finset.mem_univ,
    true_and,initialAMap,kernelReconstructLinear_apply]

/-- The universal A factors divide every A row jointly. -/
theorem initialAUniversalProduct_dvd
    (u0 u1:I → K) (H:P4):
    ∀ v:Caps.AKernel u0 u1,
      regularProduct H (initialAUniversalFactors u0 u1 H) ∣
        reconstruct K 23019385 131071 188820 37 v.1:=by
  intro v
  have h:=universalProduct_dvd H
    (Finset.univ:Finset (RegularIndex H)) (initialAMap u0 u1) v
  simpa only [initialAUniversalFactors,initialAMap,
    kernelReconstructLinear_apply] using h

/-- The same universal product divides the selected carrier. -/
theorem initialAUniversalProduct_dvd_carrier
    (u0 u1:I → K) (H:P4):
    regularProduct H (initialAUniversalFactors u0 u1 H) ∣ H:=
  regularProduct_dvd_carrier H (initialAUniversalFactors u0 u1 H)

public theorem degreeY_le_ysWeight (Q:P4):
    Q.degreeOf (1:Fin 4) ≤ wt residualYSWeights Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*0 ≤ wt residualYSWeights Q at h
  omega

public theorem degreeZ_le_totalWeight (Q:P4):
    Q.degreeOf (3:Fin 4) ≤ wt residualTotalWeights Q:=by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h:=MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0*0+d 1*1+d 2*1+d 3*1 ≤ wt residualTotalWeights Q at h
  omega

public theorem initialA_helper_gates (p:FlagDegree)
    (hr:1 ≤ p.all) (hs:p.all ≤ 40)
    (hy:middle p ≤ 185) (ht:total p ≤ 10714):
    Lower80889.FactorSwitch.HelperPairGates
      188820 175 37 (middle p) p.all (total p):=by
  unfold Lower80889.FactorSwitch.HelperPairGates
  change 1 ≤ p.all ∧ middle p < 2130706433 ∧ p.all < 2130706433 ∧
    total p < 2130706433 ∧
    p.all*188820+total p*37 < 2130706433 ∧
    middle p*188820+total p*175 < 2130706433 ∧
    middle p*37+p.all*175 < 2130706433
  omega

/-- Every factor outside the A-universal set gets the direct coprime A
helper, with no minimum against its ordinary cost. -/
theorem initialA_nonuniversal_count
    (u0 u1:I → K) (H:P4) (hH:H ≠ 0)
    (hwide:ResidualSupportData InitialSupports.wideSupport H)
    (selected:K → Polynomial K) (Gamma:Finset K)
    (hdegree:∀ gamma ∈ Gamma,(selected gamma).natDegree ≤ 131071)
    (hagreement:∀ gamma ∈ Gamma,181255 ≤
      ((Finset.univ:Finset I).filter (fun i=>
        (selected gamma).eval (IRSProfile.domain i)=u0 i+gamma*u1 i)).card)
    (hno:NoLargeSelectedPencil selected Gamma 131071 80889)
    (F:RegularIndex H) (hFU:F ∉ initialAUniversalFactors u0 u1 H):
    (regularSeeds H selected Gamma F).card ≤
      initialAHelperCap (regularCumulativeFlag H F):=by
  have hFsupport:=MovingFiberOrdinary6814.factor_support H hH hwide F
  have hc:=originalCumulativeFlag_cumulative F.1
  have hs:(regularCumulativeFlag H F).all ≤ 40:=by
    simpa only [regularCumulativeFlag,hc.1,InitialSupports.wideSupport]
      using hFsupport.s_weight
  have hy:middle (regularCumulativeFlag H F) ≤ 185:=by
    simpa only [regularCumulativeFlag,middle,hc.2.1,
      InitialSupports.wideSupport] using hFsupport.ys_weight
  have ht:total (regularCumulativeFlag H F) ≤ 10714:=by
    simpa only [regularCumulativeFlag,total,hc.2.2,
      InitialSupports.wideSupport] using hFsupport.total_weight
  have hr:1 ≤ (regularCumulativeFlag H F).all:=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
  have hFY:F.1.degreeOf 1 ≤ middle (regularCumulativeFlag H F):=by
    rw [regularCumulativeFlag,middle,hc.2.1]
    exact degreeY_le_ysWeight F.1
  have hFR:F.1.degreeOf 2 ≤ (regularCumulativeFlag H F).all:=by
    rw [regularCumulativeFlag,originalCumulativeFlag_all]
  have hFZ:F.1.degreeOf 3 ≤ total (regularCumulativeFlag H F):=by
    rw [regularCumulativeFlag,total,hc.2.2]
    exact degreeZ_le_totalWeight F.1
  rcases Lower80889.FactorSwitch.divisor_or_helper_count
      23019385 188820 37 127 175 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      selected Gamma hdegree hagreement hno F
      (middle (regularCumulativeFlag H F)) (regularCumulativeFlag H F).all
      (total (regularCumulativeFlag H F)) hFY hFR hFZ
      (initialA_helper_gates (regularCumulativeFlag H F) hr hs hy ht) with
    hdiv | hcount
  · exact False.elim (hFU ((mem_initialAUniversalFactors u0 u1 H F).2 hdiv))
  · simpa only [initialAHelperCap] using hcount



end
end ProximityPrize.SubmissionLower.Lower80889.InitialBridge


namespace ProximityPrize.SubmissionLower.Lower80889.Initial
open RCN095 RCN260 LocatorFactorAggregate Lower80889.InitialBridge Lower80889.FactorSwitch
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem initialA_majorant (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 40)
    (hy : middle p ≤ 185) (ht : total p ≤ 10714) :
    InitialBridge.initialAHelperCap p ≤ initialAPotential.eval p := by
  change AsymmetricHelper.leftRegularCountCap
      (helperPair 188820 175 37 (middle p) p.all (total p)) ≤
    9419418648*total p+5377994938571*middle p+25200613727349*p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _
    48496271 10354609 2808589389 9419418648 5377994938571 25200613727349
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1+2*131071*middle p ≤ 48496271
    omega
  · change 131071*(2*p.all-1) ≤ 10354609
    omega
  · change 2*131071*total p+1 ≤ 2808589389
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]
end ProximityPrize.SubmissionLower.Lower80889.Initial


end InitialGeometry


