-- Prove2me | Definitions.Def_Yukon_dfd305be17d46cecd47c7820
-- name    : Yukon_dfd305be17d46cecd47c7820
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:43:43.687724+00:00
-- url     : https://prove2.me/theorems/1c3e5aaa-de81-4884-9f1e-c7d9775a5529
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberSourceSound6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberSourceSound6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberSourceSound6814.lean
--
--   yukon-proof-operation:foundation-direct-31e8ef63a5f873f1356e39b40adccb43fca6bdf0b771013ec26fa2b497687439
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMzJhMjI5NmYwZTM4MTc5Y2E4YzUxODJiYmI0YjJiYzVkM2JmNTYzZTJlMGU0NzdmYzgwZGZhZWQwZTk4NDBjZSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTMxZThlZjYzYTVmODczZjEzNTZlMzliNDBhZGNjYjQzZmNhNmJkZjBiNzcxMDEzZWMyNmZhMmI0OTc2ODc0MzkiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9kZmQzMDViZTE3ZDQ2Y2VjZDQ3Yzc4MjAiLCJ2IjoyfQ]

import Definitions.Def_Yukon_9fd7c568bc98e339bf933fdc












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.Lower80889.SourceSound

open RCN095 RCN223 RCN260 RCN294 LocatorFactorAggregate
open Lower80889.FactorSwitch Lower80889.PowerRoute
open Lower80889.Oracle
open LocatorPhase6800Oracle (Potential)

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem helperPair_regularCountCap_mono_right
    (L₁ Y₁ S₁ L₂ Y₂ S₂ leftY leftR leftZ : ℕ)
    (hL : L₁ ≤ L₂) (hY : Y₁ ≤ Y₂) (hS : S₁ ≤ S₂) :
    AsymmetricHelper.leftRegularCountCap (helperPair L₁ Y₁ S₁ leftY leftR leftZ) ≤
      AsymmetricHelper.leftRegularCountCap (helperPair L₂ Y₂ S₂ leftY leftR leftZ) := by
  let P₁ := helperPair L₁ Y₁ S₁ leftY leftR leftZ
  let P₂ := helperPair L₂ Y₂ S₂ leftY leftR leftZ
  have ha : vectorLE P₁.leftAgreement P₂.leftAgreement := by
    exact ⟨le_rfl, le_rfl, le_rfl⟩
  have hm : vectorLE P₁.mixedCost P₂.mixedCost := by
    refine ⟨?_, ?_, ?_⟩
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftR hL)
        (Nat.mul_le_mul_left leftZ hS)
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftY hL)
        (Nat.mul_le_mul_left leftZ hY)
    · exact Nat.add_le_add (Nat.mul_le_mul_left leftY hS)
        (Nat.mul_le_mul_left leftR hY)
  have hdot : dot P₁.leftAgreement P₁.mixedCost ≤
      dot P₂.leftAgreement P₂.mixedCost := by
    unfold dot
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul ha.1 hm.1)
        (Nat.mul_le_mul ha.2.1 hm.2.1))
      (Nat.mul_le_mul ha.2.2 hm.2.2)
  have hnum : AsymmetricHelper.leftRegularNumerator P₁ ≤ AsymmetricHelper.leftRegularNumerator P₂ := by
    unfold AsymmetricHelper.leftRegularNumerator
    exact Nat.add_le_add (Nat.mul_le_mul_left (P₁.n - P₁.w) hdot)
      (Nat.mul_le_mul_left ((P₁.errors + 1) * P₁.gap) hm.2.2)
  exact Nat.div_le_div_right hnum

theorem stageCost_le_stageZero (L YS S : ℕ) (p : FlagDegree) (j : ℕ) :
    stageCost L YS S (exactRouteBox p) j ≤
      stageCost L YS S (exactRouteBox p) 0 := by
  apply helperPair_regularCountCap_mono_right
  · simpa only [exactRouteBox, Nat.zero_mul, Nat.sub_zero] using
      Nat.sub_le L (j * total p)
  · simpa only [exactRouteBox, Nat.zero_mul, Nat.sub_zero] using
      Nat.sub_le YS (j * middle p)
  · simpa only [exactRouteBox, Nat.zero_mul, Nat.sub_zero] using
      Nat.sub_le S (j * p.all)

theorem helperPair_gates_of_right_le
    (L₁ Y₁ S₁ L₂ Y₂ S₂ leftY leftR leftZ : ℕ)
    (hL : L₁ ≤ L₂) (hY : Y₁ ≤ Y₂) (hS : S₁ ≤ S₂)
    (hgate : HelperPairGates L₂ Y₂ S₂ leftY leftR leftZ) :
    HelperPairGates L₁ Y₁ S₁ leftY leftR leftZ := by
  rcases hgate with ⟨hr, hy, hs, hz, hmy, hmr, hmz⟩
  refine ⟨hr, hy, hs, hz, ?_, ?_, ?_⟩
  · exact (Nat.add_le_add (Nat.mul_le_mul_left leftR hL)
      (Nat.mul_le_mul_left leftZ hS)).trans_lt hmy
  · exact (Nat.add_le_add (Nat.mul_le_mul_left leftY hL)
      (Nat.mul_le_mul_left leftZ hY)).trans_lt hmr
  · exact (Nat.add_le_add (Nat.mul_le_mul_left leftY hS)
      (Nat.mul_le_mul_left leftR hY)).trans_lt hmz

theorem stageGates_of_stageZero (L YS S : ℕ) (p : FlagDegree) (j : ℕ)
    (hgate : HelperPairGates L YS S (middle p) p.all (total p)) :
    HelperPairGates (L - j * total p) (YS - j * middle p)
      (S - j * p.all) (middle p) p.all (total p) := by
  apply helperPair_gates_of_right_le
  · exact Nat.sub_le _ _
  · exact Nat.sub_le _ _
  · exact Nat.sub_le _ _
  · exact hgate


namespace Phase00
def source : SourceNumbers := ⟨3840000, 88502, 19840, 97611002981890704000452⟩
def potential : Potential := ⟨4588914142455, 241504172033374, 1109325007620895⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 37)
    (hy : middle p ≤ 175) (ht : total p ≤ 10714) :
    stageCost 3840000 88502 19840 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3840000 88502 19840 (middle p) p.all (total p)) ≤
    4588914142455 * total p + 241504172033374 * middle p + 1109325007620895 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 45874851 9568183 2808589389 4588914142455 241504172033374 1109325007620895
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 45874851
    omega
  · change 131071*(2*p.all-1) ≤ 9568183
    omega
  · change 2*131071*total p+1 ≤ 2808589389
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 37)
    (hy : middle p ≤ 175) (ht : total p ≤ 10714) :
    HelperPairGates 3840000 88502 19840 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)

noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80889.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 11600138745
  m := 63999
  weighted := by decide
  shape := MovingFiberKernels6814.Source00.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6814.Source00.finrank_gap u0 u1
end Phase00

namespace Phase01
def source : SourceNumbers := ⟨3200000, 44252, 9888, 12446163187974310543276⟩
def potential : Potential := ⟨2290647880876, 152505367520269, 708037079293745⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 37)
    (hy : middle p ≤ 175) (ht : total p ≤ 10714) :
    stageCost 3200000 44252 9888 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3200000 44252 9888 (middle p) p.all (total p)) ≤
    2290647880876 * total p + 152505367520269 * middle p + 708037079293745 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 45874851 9568183 2808589389 2290647880876 152505367520269 708037079293745
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 45874851
    omega
  · change 131071*(2*p.all-1) ≤ 9568183
    omega
  · change 2*131071*total p+1 ≤ 2808589389
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 37)
    (hy : middle p ≤ 175) (ht : total p ≤ 10714) :
    HelperPairGates 3200000 44252 9888 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)

noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80889.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 5800160000
  m := 32000
  weighted := by decide
  shape := MovingFiberKernels6814.Source01.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6814.Source01.finrank_gap u0 u1
end Phase01

namespace Phase02
def source : SourceNumbers := ⟨2880000, 44252, 9888, 10849238628434268943276⟩
def potential : Potential := ⟨2290647880876, 144508361619685, 669695269345567⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 37)
    (hy : middle p ≤ 175) (ht : total p ≤ 10714) :
    stageCost 2880000 44252 9888 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 2880000 44252 9888 (middle p) p.all (total p)) ≤
    2290647880876 * total p + 144508361619685 * middle p + 669695269345567 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 45874851 9568183 2808589389 2290647880876 144508361619685 669695269345567
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 45874851
    omega
  · change 131071*(2*p.all-1) ≤ 9568183
    omega
  · change 2*131071*total p+1 ≤ 2808589389
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 37)
    (hy : middle p ≤ 175) (ht : total p ≤ 10714) :
    HelperPairGates 2880000 44252 9888 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)

noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80889.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 5800160000
  m := 32000
  weighted := by decide
  shape := MovingFiberKernels6814.Source02.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6814.Source02.finrank_gap u0 u1
end Phase02

namespace Phase03
def source : SourceNumbers := ⟨1062000, 22126, 4940, 439344453174038863335⟩
def potential : Potential := ⟨1144844667814, 62778374827435, 289556371671499⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 37)
    (hy : middle p ≤ 175) (ht : total p ≤ 10714) :
    stageCost 1062000 22126 4940 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 1062000 22126 4940 (middle p) p.all (total p)) ≤
    1144844667814 * total p + 62778374827435 * middle p + 289556371671499 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 45874851 9568183 2808589389 1144844667814 62778374827435 289556371671499
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 45874851
    omega
  · change 131071*(2*p.all-1) ≤ 9568183
    omega
  · change 2*131071*total p+1 ≤ 2808589389
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 37)
    (hy : middle p ≤ 175) (ht : total p ≤ 10714) :
    HelperPairGates 1062000 22126 4940 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)

noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80889.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 2900080000
  m := 16000
  weighted := by decide
  shape := MovingFiberKernels6814.Source03.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6814.Source03.finrank_gap u0 u1
end Phase03

namespace Phase04
def source : SourceNumbers := ⟨531000, 11063, 2470, 27148538556096117398⟩
def potential : Potential := ⟨572422333907, 31389187413718, 144778185835750⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 37)
    (hy : middle p ≤ 175) (ht : total p ≤ 10714) :
    stageCost 531000 11063 2470 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 531000 11063 2470 (middle p) p.all (total p)) ≤
    572422333907 * total p + 31389187413718 * middle p + 144778185835750 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 45874851 9568183 2808589389 572422333907 31389187413718 144778185835750
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 45874851
    omega
  · change 131071*(2*p.all-1) ≤ 9568183
    omega
  · change 2*131071*total p+1 ≤ 2808589389
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 37)
    (hy : middle p ≤ 175) (ht : total p ≤ 10714) :
    HelperPairGates 531000 11063 2470 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)

noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80889.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 1450040000
  m := 8000
  weighted := by decide
  shape := MovingFiberKernels6814.Source04.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6814.Source04.finrank_gap u0 u1
end Phase04

namespace Phase05
def source : SourceNumbers := ⟨88902, 1382, 308, 8567288215222491⟩
def potential : Potential := ⟨71441061309, 4481110883533, 20789998102402⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 37)
    (hy : middle p ≤ 175) (ht : total p ≤ 10714) :
    stageCost 88902 1382 308 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 88902 1382 308 (middle p) p.all (total p)) ≤
    71441061309 * total p + 4481110883533 * middle p + 20789998102402 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 45874851 9568183 2808589389 71441061309 4481110883533 20789998102402
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 45874851
    omega
  · change 131071*(2*p.all-1) ≤ 9568183
    omega
  · change 2*131071*total p+1 ≤ 2808589389
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 37)
    (hy : middle p ≤ 175) (ht : total p ≤ 10714) :
    HelperPairGates 88902 1382 308 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)

noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80889.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 181255000
  m := 1000
  weighted := by decide
  shape := MovingFiberKernels6814.Source05.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6814.Source05.finrank_gap u0 u1
end Phase05

namespace Phase06
def source : SourceNumbers := ⟨3640000, 19360, 4267, 1362027561383642773059⟩
def potential : Potential := ⟨995082929014, 122267333849628, 578157057905613⟩
theorem stageZero_le (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 37)
    (hy : middle p ≤ 175) (ht : total p ≤ 10714) :
    stageCost 3640000 19360 4267 (exactRouteBox p) 0 ≤ potential.eval p := by
  simp only [stageCost, stagePair, exactRouteBox, Nat.zero_mul, Nat.sub_zero]
  change AsymmetricHelper.leftRegularCountCap (helperPair 3640000 19360 4267 (middle p) p.all (total p)) ≤
    995082929014 * total p + 122267333849628 * middle p + 578157057905613 * p.all
  apply AsymmetricHelper.leftRegularCountCap_le_linear _ 45874851 9568183 2808589389 995082929014 122267333849628 578157057905613
  · norm_num [helperPair, UnequalParameters.gap]
  · change 1 + 2*131071*middle p ≤ 45874851
    omega
  · change 131071*(2*p.all-1) ≤ 9568183
    omega
  · change 2*131071*total p+1 ≤ 2808589389
    omega
  all_goals norm_num [helperPair, UnequalParameters.gap, UnequalParameters.errors]

theorem stageZero_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 37)
    (hy : middle p ≤ 175) (ht : total p ≤ 10714) :
    HelperPairGates 3640000 19360 4267 (middle p) p.all (total p) := by
  unfold HelperPairGates helperPair UnequalParameters.mixedCost
  norm_num
  constructor
  · exact hr
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · nlinarith
  constructor <;> nlinarith

def sound : PhaseSourceSound where
  source := source
  potential := potential
  stageCost_le := by
    intro p j hr hs hy ht _hj
    exact (stageCost_le_stageZero _ _ _ p j).trans (stageZero_le p hr hs hy ht)
  stageGates := by
    intro p j hr hs hy ht _hj
    exact stageGates_of_stageZero _ _ _ p j (stageZero_gates p hr hs hy ht)

noncomputable def kernel (u0 u1 : ProximityPrize.Benchmark.IRSProfile.Index → ProximityPrize.Benchmark.IRSProfile.Field) :
    Lower80889.BatchPhase.PhaseKernelRealization sound u0 u1 where
  D := 2537570000
  m := 14000
  weighted := by decide
  shape := MovingFiberKernels6814.Source06.shape
  slope_le_m := by decide
  m_lt_char := by decide
  gap_le_finrank := MovingFiberKernels6814.Source06.finrank_gap u0 u1
end Phase06

end ProximityPrize.SubmissionLower.Lower80889.SourceSound


