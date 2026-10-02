-- Prove2me | Definitions.Def_Yukon_ed800dd138a6a87dff9457b0
-- name    : Yukon_ed800dd138a6a87dff9457b0
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T11:23:53.111537+00:00
-- url     : https://prove2.me/theorems/574168ad-320a-47a4-b711-97397a416822
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberShape6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberShape6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberShape6814.lean
--
--   yukon-proof-operation:foundation-direct-61b5694831701415b4e5aa88176294d1311a754819a18aa4347ba55858e88667
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMzY5YjkyZmFhZDkwYTEzZmM3ODQ1MmZiM2M1NTk1MmFlNzczNzg0Mzk3MjJkMWQ4NWMzM2VhMmQ1YTIzNjNjZSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTYxYjU2OTQ4MzE3MDE0MTViNGU1YWE4ODE3NjI5NGQxMzExYTc1NDgxOWExOGFhNDM0N2JhNTU4NThlODg2NjciLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9lZDgwMGRkMTM4YTZhODdkZmY5NDU3YjAiLCJ2IjoyfQ]

import Definitions.Def_Yukon_68c36723892eb4da8b78c8fc













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingFiberShape6814
open RCN095 RCN146 LocatorFactorAggregate LocatorPhase6800Oracle
open LocatorHybridCostC2 LocatorHybridCells
open BoundaryTailIdentityArithmetic Lower80788.HybridIdentityC2
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
noncomputable section

def cost (r v z : ℕ) : ℕ := MovingFiberOrdinary6814.rawCost (rawFlag r v z)

/-- Subtraction-free in the varying total-degree coordinate. The remaining
natural subtractions are constant as z varies. -/
def high (r v z : ℕ) : ℕ := newCost ⟨z,v,r⟩ z (v-1) (r-2)

theorem high_mono (r v : ℕ) : Monotone (high r v) := by
  intro a b hab
  simp only [high,newCost,newNormal,reducedABS,rationalABS,mfibABS,mcutABS,
    flagMixed,unitAllFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all]
  gcongr

theorem high_affine (r v z : ℕ) :
    2*high r v (z+1) = high r v z + high r v (z+2) := by
  simp only [high,newCost,newNormal,reducedABS,rationalABS,mfibABS,mcutABS,
    flagMixed,unitAllFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all]
  ring

theorem hybrid_iff (r v z : ℕ) :
    HybridAppliesC2 (rawFlag r v z) ↔ 3 ≤ r ∧ 2 ≤ v := by
  unfold HybridAppliesC2 rawFlag middle
  dsimp
  omega

theorem cost_eq_high (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    cost r v z = high r v z := by
  have ha := (hybrid_iff r v z).mpr ⟨hr,hv⟩
  unfold cost MovingFiberOrdinary6814.rawCost
  rw [if_pos ha]
  simp only [rawFlag_all,rawFlag_middle,rawFlag_total]
  rw [MovingFiberOrdinaryHigh6814.bound_eq_abs _ _ _ _ hr (by omega)]
  unfold high
  congr 1 <;> simp only [rawFlag,total,middle,cellA,cellB,cellS] <;> omega

theorem cost_eq_old (r v z : ℕ) (h : ¬ (3 ≤ r ∧ 2 ≤ v)) :
    cost r v z = LocatorOrdinaryZConvex.rawCost r v z := by
  have ha : ¬ HybridAppliesC2 (rawFlag r v z) := by
    simpa only [hybrid_iff] using h
  change MovingFiberOrdinary6814.rawCost (rawFlag r v z) =
    LocatorHybridCost.ordinaryCostOf (rawFlag r v z)
  simp only [MovingFiberOrdinary6814.rawCost,LocatorHybridCost.ordinaryCostOf,if_neg ha]

theorem cost_mono (r v : ℕ) : Monotone (cost r v) := by
  intro a b hab
  by_cases h : 3 ≤ r ∧ 2 ≤ v
  · rw [cost_eq_high r v a h.1 h.2,cost_eq_high r v b h.1 h.2]
    exact high_mono r v hab
  · rw [cost_eq_old r v a h,cost_eq_old r v b h]
    exact LocatorOrdinaryZConvex.rawCost_mono_z r v hab

end
theorem raw_affine (r v z : ℕ) (hr : 1 ≤ r) (hz : 3 ≤ z) :
    cost r v z = cost r v 3+(cost r v 4-cost r v 3)*(z-3) := by
  apply LocatorOrdinaryZConvex.affine_formula_from_three _ (cost_mono r v) _ z hz
  intro n hn
  by_cases h : 3 ≤ r ∧ 2 ≤ v
  · rw [cost_eq_high r v (n+1) h.1 h.2,cost_eq_high r v n h.1 h.2,
      cost_eq_high r v (n+2) h.1 h.2]
    exact high_affine r v n
  · rw [cost_eq_old r v (n+1) h,cost_eq_old r v n h,cost_eq_old r v (n+2) h]
    exact LocatorOrdinaryZConvex.rawCost_affine_step_from_two r v n hr hn

end ProximityPrize.SubmissionLower.MovingFiberShape6814


