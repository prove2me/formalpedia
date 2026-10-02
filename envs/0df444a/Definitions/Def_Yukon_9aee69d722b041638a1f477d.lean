-- Prove2me | Definitions.Def_Yukon_9aee69d722b041638a1f477d
-- name    : Yukon_9aee69d722b041638a1f477d
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T04:40:29.18047+00:00
-- url     : https://prove2.me/theorems/c57886f9-b15f-4189-86a7-1311694bddce
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeContactRank.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeContactRank.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeContactRank.lean
--
--   yukon-proof-operation:foundation-direct-0bb2f1ed38a68a287e79d2a45d2a998530e7e0988fa9ef44cd38dd842e9cdf13
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNjUxZWI2NGI3ZGRjNzNjMDMwOTVmMzI3MWU1OTA5NzBmYThkZTEzMGY1ZjhlZmMzZmQzYjY2M2I4NDhmYTU0MCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTBiYjJmMWVkMzhhNjhhMjg3ZTc5ZDJhNDVkMmE5OTg1MzBlN2UwOTg4ZmE5ZWY0NGNkMzhkZDg0MmU5Y2RmMTMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl85YWVlNjlkNzIyYjA0MTYzOGExZjQ3N2QiLCJ2IjoyfQ]

import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_755f5ab5e1dfa660f8e11f09







































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.RelativeContactRank6814
open scoped BigOperators
open MvPolynomial RCN119
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

variable (K : Type*) [Field K]

def totalWeights : Fin 3 → ℕ := fun _ => 1

theorem coefficientBox_bounds (M L s : ℕ) (p : RCN119.Poly K) :
    p ∈ coefficientBox K M L s ↔
      p.degreeOf 0 ≤ M ∧ weightedTotalDegree totalWeights p ≤ L ∧ p.degreeOf 1 ≤ s := by
  classical
  rw [coefficientBox, MvPolynomial.mem_restrictSupport_iff K]
  constructor
  · intro hp
    refine ⟨MvPolynomial.degreeOf_le_iff.mpr (fun d hd => (hp hd).1), ?_,
      MvPolynomial.degreeOf_le_iff.mpr (fun d hd => (hp hd).2.2)⟩
    change p.support.sup (Finsupp.weight totalWeights) ≤ L
    apply Finset.sup_le
    intro d hd
    simpa [totalWeights, RCN372.weight_fin3] using (hp hd).2.1
  · rintro ⟨h0,ht,h1⟩ d hd
    have htot : Finsupp.weight totalWeights d ≤ L :=
      (Finset.le_sup (f := Finsupp.weight totalWeights) hd).trans ht
    exact ⟨MvPolynomial.degreeOf_le_iff.mp h0 d hd,
      by simpa [totalWeights, RCN372.weight_fin3] using htot,
      MvPolynomial.degreeOf_le_iff.mp h1 d hd⟩

theorem slope_degrees :
    (slopeDifference K).degreeOf 0 = 1 ∧
      weightedTotalDegree totalWeights (slopeDifference K) = 1 ∧
      (slopeDifference K).degreeOf 1 = 1 := by
  classical
  have hb := (coefficientBox_bounds K 1 1 1 _).mp (slopeDifference_mem_coefficientBox K)
  have h0 : Finsupp.single (0 : Fin 3) 1 ∈ (slopeDifference K).support := by
    simp [MvPolynomial.mem_support_iff, slopeDifference]
  have h1 : Finsupp.single (1 : Fin 3) 1 ∈ (slopeDifference K).support := by
    simp [MvPolynomial.mem_support_iff, slopeDifference]
  have hlo0 := MvPolynomial.degreeOf_le_iff.mp (le_refl ((slopeDifference K).degreeOf 0)) _ h0
  have hlo1 := MvPolynomial.degreeOf_le_iff.mp (le_refl ((slopeDifference K).degreeOf 1)) _ h1
  have hlot := Finset.le_sup (f := Finsupp.weight totalWeights) h0
  change Finsupp.weight totalWeights (Finsupp.single 0 1) ≤
    weightedTotalDegree totalWeights (slopeDifference K) at hlot
  simp only [Finsupp.single_eq_same] at hlo0 hlo1
  have hlot' : 1 ≤ weightedTotalDegree totalWeights (slopeDifference K) := by
    simpa [totalWeights, RCN372.weight_fin3] using hlot
  exact ⟨Nat.le_antisymm hb.1 hlo0, Nat.le_antisymm hb.2.1 hlot',
    Nat.le_antisymm hb.2.2 hlo1⟩

theorem slope_power_degrees (h : ℕ) :
    (slopeDifference K ^ h).degreeOf 0 = h ∧
      weightedTotalDegree totalWeights (slopeDifference K ^ h) = h ∧
      (slopeDifference K ^ h).degreeOf 1 = h := by
  have hd := slope_degrees K
  have ht : weightedTotalDegree totalWeights (slopeDifference K ^ h) = h := by
    induction h with
    | zero => simp [MvPolynomial.weightedTotalDegree]
    | succ h ih =>
        rw [pow_succ, RCN071.weightedTotalDegree_mul_fin3 _ _ _
          (pow_ne_zero h (slopeDifference_ne_zero K)) (slopeDifference_ne_zero K), ih, hd.2.1]
  refine ⟨?_,ht,?_⟩
  · rw [MvPolynomial.degreeOf_pow_eq _ _ _ (slopeDifference_ne_zero K), hd.1, mul_one]
  · rw [MvPolynomial.degreeOf_pow_eq _ _ _ (slopeDifference_ne_zero K), hd.2.2, mul_one]

theorem quotient_mem_coefficientBox {M L s h : ℕ} (q : RCN119.Poly K)
    (hq : slopeDifference K ^ h * q ∈ coefficientBox K M L s) :
    q ∈ coefficientBox K (M-h) (L-h) (s-h) := by
  by_cases hz : q = 0
  · rw [hz]; exact Submodule.zero_mem _
  have hn := pow_ne_zero h (slopeDifference_ne_zero K)
  have hb := (coefficientBox_bounds K M L s _).mp hq
  have hd := slope_power_degrees K h
  have h0 := hb.1
  have ht := hb.2.1
  have h1 := hb.2.2
  rw [MvPolynomial.degreeOf_mul_eq hn hz, hd.1] at h0
  rw [RCN071.weightedTotalDegree_mul_fin3 _ _ _ hn hz, hd.2.1] at ht
  rw [MvPolynomial.degreeOf_mul_eq hn hz, hd.2.2] at h1
  exact (coefficientBox_bounds K _ _ _ q).mpr ⟨by omega,by omega,by omega⟩

theorem kernelEmbedding_surjective {M L s h : ℕ}
    (hM : h ≤ M) (hL : h ≤ L) (hs : h ≤ s) :
    Function.Surjective (kernelEmbedding K hM hL hs) := by
  intro p
  have hp : contactJet K h p.val.val = 0 := p.property
  obtain ⟨q,hq⟩ := (contactJet_eq_zero_iff K h p.val.val).mp hp
  have hmem : q ∈ coefficientBox K (M-h) (L-h) (s-h) := by
    apply quotient_mem_coefficientBox K q
    rw [← hq]
    exact p.val.property
  refine ⟨⟨q,hmem⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hq.symm

theorem blockJet_rank_add_quotient_finrank_eq {M L s h : ℕ}
    (hM : h ≤ M) (hL : h ≤ L) (hs : h ≤ s) :
    Module.finrank K (LinearMap.range (blockJet K M L s h)) +
      Module.finrank K (coefficientBox K (M-h) (L-h) (s-h)) =
      Module.finrank K (coefficientBox K M L s) := by
  have he := (LinearEquiv.ofBijective (kernelEmbedding K hM hL hs)
    ⟨kernelEmbedding_injective K hM hL hs,kernelEmbedding_surjective K hM hL hs⟩).finrank_eq
  have hr := (blockJet K M L s h).finrank_range_add_finrank_ker
  omega

theorem blockJet_kernel_eq_bot_of_large (M L s h : ℕ) (hh : M < h ∨ s < h) :
    LinearMap.ker (blockJet K M L s h) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro p hp
  rw [Submodule.mem_bot]
  apply Subtype.ext
  change p.val = 0
  by_contra hne
  have hz : contactJet K h p.val = 0 := hp
  obtain ⟨q,hq⟩ := (contactJet_eq_zero_iff K h p.val).mp hz
  have hqne : q ≠ 0 := by
    intro h
    apply hne
    rw [hq,h,mul_zero]
  have hn := pow_ne_zero h (slopeDifference_ne_zero K)
  have hb := (coefficientBox_bounds K M L s p.val).mp p.property
  have h0 := hb.1
  have h1 := hb.2.2
  rw [hq,MvPolynomial.degreeOf_mul_eq hn hqne,(slope_power_degrees K h).1] at h0
  rw [hq,MvPolynomial.degreeOf_mul_eq hn hqne,(slope_power_degrees K h).2.2] at h1
  omega

theorem blockJet_rank_eq_contactRankBound (M L s h : ℕ) (hML : M ≤ L) :
    Module.finrank K (LinearMap.range (blockJet K M L s h)) =
      contactRankBound M L s h := by
  by_cases hM : h ≤ M
  · by_cases hs : h ≤ s
    · have hL := hM.trans hML
      have he := blockJet_rank_add_quotient_finrank_eq K hM hL hs
      rw [coefficientBox_finrank_range K M L s hML,
        coefficientBox_finrank_range K (M-h) (L-h) (s-h) (Nat.sub_le_sub_right hML h)] at he
      have hm : M-h+1 = M+1-h := by omega
      have hl : L-h+1 = L+1-h := by omega
      have hs' : s-h+1 = s+1-h := by omega
      simp only [hm,hl,hs'] at he
      unfold contactRankBound blockInputCount blockKernelLowerBound
      omega
    · have hk := blockJet_kernel_eq_bot_of_large K M L s h (Or.inr (by omega))
      have he := (blockJet K M L s h).finrank_range_add_finrank_ker
      rw [hk,finrank_bot,Nat.add_zero] at he
      rw [coefficientBox_finrank_range K M L s hML] at he
      have hz : s+1-h=0 := by omega
      simpa [contactRankBound,blockInputCount,blockKernelLowerBound,hz] using he
  · have hk := blockJet_kernel_eq_bot_of_large K M L s h (Or.inl (by omega))
    have he := (blockJet K M L s h).finrank_range_add_finrank_ker
    rw [hk,finrank_bot,Nat.add_zero] at he
    rw [coefficientBox_finrank_range K M L s hML] at he
    have hz : M+1-h=0 := by omega
    simpa [contactRankBound,blockInputCount,blockKernelLowerBound,hz] using he

theorem localTarget_finrank_eq (m L s : ℕ) :
    Module.finrank K (RCN100.LocalTarget K m L s) = localRankBound m L s := by
  change Module.finrank K ((r : Fin m) → LinearMap.range
    (blockJet K (min r.val L) L s (m-r.val))) = _
  rw [Module.finrank_pi_fintype]
  unfold localRankBound
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro r _
  rw [blockJet_rank_eq_contactRankBound K _ _ _ _ (min_le_right _ _),
    RCN100.full_contactRankBound_eq]

end
end ProximityPrize.SubmissionLower.RelativeContactRank6814


