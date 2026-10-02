-- Prove2me | Definitions.Def_Yukon_aa49d06014b5907015f56d9e
-- name    : Yukon_aa49d06014b5907015f56d9e
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T06:03:17.20101+00:00
-- url     : https://prove2.me/theorems/72aa9721-4170-4088-931d-ba141357f06c
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.BoundaryTailFlags.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.BoundaryTailFlags.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/BoundaryTailFlags.lean
--
--   yukon-proof-operation:foundation-direct-3f382481707850ff6b0599a79fe83fa637035d3a3318a6515b70f5d359766514
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNGNiNmQ4OTliNTlmODllMTc2YTQ3MDJhMjY1NzVlYTI1MGVhZWYyMjBkYjAyNTQ0ZTcyYWI1OGE4YmNhNmM1MCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTNmMzgyNDgxNzA3ODUwZmY2YjA1OTlhNzlmZTgzZmE2MzcwMzVkM2EzMzE4YTY1MTViNzBmNWQzNTk3NjY1MTQiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9hYTQ5ZDA2MDE0YjU5MDcwMTVmNTZkOWUiLCJ2IjoyfQ]

import Definitions.Def_Yukon_ca285380b3940c88ff602179

import Definitions.Def_Yukon_56f5e02e27ca1815c809ecfe












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.BoundaryTailAlgebra

open RCN055 RCN057 RCN095 RCN136 RCN156 RCN234 RCN313

noncomputable section
variable {K Ω : Type} [Field K] [Field Ω]

def coefficientFlag (m i r v z : ℕ) : FlagDegree :=
  ⟨min (2 * i) m * z, min (2 * i) m * v - i,
    2 * i + min (2 * i) m * (r - 2)⟩

theorem coefficientFlag_sub_safe {m i v : ℕ}
    (hm : 1 ≤ m) (hi : i ≤ m + 1) (hv : 2 ≤ v) : i ≤ min (2 * i) m * v := by
  have h : i ≤ 2 * min (2 * i) m := by
    by_cases hh : 2 * i ≤ m
    · rw [min_eq_left hh]; omega
    · rw [min_eq_right (by omega)]; omega
  have := Nat.mul_le_mul_left (min (2 * i) m) hv
  omega

theorem coefficientFlag_cumulative {m i r v : ℕ} (z : ℕ)
    (hm : 1 ≤ m) (hi : i ≤ m + 1) (hr : 2 ≤ r) (hv : 2 ≤ v) :
    ((coefficientFlag m i r v z).all : ℤ) = coefficientWeight m i r 0 ∧
    (((coefficientFlag m i r v z).yz + (coefficientFlag m i r v z).all : ℕ) : ℤ) =
      coefficientWeight m i (r + v) 1 ∧
    (((coefficientFlag m i r v z).zOnly + (coefficientFlag m i r v z).yz +
      (coefficientFlag m i r v z).all : ℕ) : ℤ) = coefficientWeight m i (r + v + z) 1 := by
  have hsafe := coefficientFlag_sub_safe hm hi hv
  simp only [coefficientFlag, coefficientWeight, Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub hr, Nat.cast_sub hsafe, Nat.cast_ofNat]
  constructor
  · ring
  constructor <;> ring

theorem weightBound_nat {w : Fin 4 → ℕ} {P : MvPolynomial (Fin 4) K} {a : ℕ}
    (h : WeightBound w P (a : ℤ)) : wt w P ≤ a := by
  rcases h with rfl | h
  · simp [wt, MvPolynomial.weightedTotalDegree]
  · exact_mod_cast h

theorem weightBounds_surfaceMap_flag (φ : Polynomial K →+* Ω)
    (P : MvPolynomial (Fin 4) K) (p : FlagDegree)
    (hR : WeightBound residualSWeights P (p.all : ℤ))
    (hYR : WeightBound residualYSWeights P ((p.yz + p.all : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights P ((p.zOnly + p.yz + p.all : ℕ) : ℤ)) :
    PolynomialInFlag p (surfaceMap φ P) := by
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (support_surfaceMap_subset φ P he)
  have hr := (MvPolynomial.le_weightedTotalDegree residualSWeights hd).trans (weightBound_nat hR)
  have hm := (MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans (weightBound_nat hYR)
  have ht := (MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans (weightBound_nat hAll)
  simp [RCN081.weight_fin4, residualSWeights] at hr
  simp [RCN081.weight_fin4, residualYSWeights] at hm
  simp [RCN081.weight_fin4, residualTotalWeights] at ht
  exact ⟨hr, hm, ht⟩

theorem refinedCoefficients_surfaceMap_flag (φ : Polynomial K →+* Ω)
    (F : MvPolynomial (Fin 4) K) (m i r v z : ℕ)
    (hm : 1 ≤ m) (hi : i ≤ m + 1) (hr : 2 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r + v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r + v + z : ℕ) : ℤ)) :
    PolynomialInFlag (coefficientFlag m i r v z) (surfaceMap φ (refinedCoefficients F m i)) := by
  obtain ⟨hcR, hcYR, hcAll⟩ := coefficientFlag_cumulative z hm hi hr hv
  apply weightBounds_surfaceMap_flag
  · rw [hcR]
    exact refinedCoefficients_weightBound residualSWeights 0 rfl rfl rfl (by omega) F _ hR m i
  · rw [hcYR]
    convert refinedCoefficients_weightBound residualYSWeights 1 rfl rfl rfl (by omega)
      F _ hYR m i using 1 <;> push_cast <;> rfl
  · rw [hcAll]
    convert refinedCoefficients_weightBound residualTotalWeights 1 rfl rfl rfl (by omega)
      F _ hAll m i using 1 <;> push_cast <;> rfl

theorem boundary_surfaceMap_flags (φ : Polynomial K →+* Ω)
    (F : MvPolynomial (Fin 4) K) (r v z : ℕ) (hr : 2 ≤ r) (hv : 1 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r + v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r + v + z : ℕ) : ℤ)) :
    PolynomialInFlag ⟨z, v, r - 1⟩ (surfaceMap φ (polyH K F)) ∧
    PolynomialInFlag ⟨z, v - 1, r + 1⟩ (surfaceMap φ (polyG K F)) ∧
    PolynomialInFlag ⟨z, v, r - 2⟩ (surfaceMap φ (boundaryJ F)) := by
  have hR' := boundary_polynomial_bounds residualSWeights 0 rfl rfl rfl (by omega) F _ hR
  have hYR' := boundary_polynomial_bounds residualYSWeights 1 rfl rfl rfl (by omega) F _ hYR
  have hAll' := boundary_polynomial_bounds residualTotalWeights 1 rfl rfl rfl (by omega) F _ hAll
  have hr1 : 1 ≤ r := by omega
  refine ⟨?_, ?_, ?_⟩
  · apply weightBounds_surfaceMap_flag
    · convert hR'.1 using 1 <;> simp only [Nat.cast_sub hr1, Nat.cast_one]
    · convert hYR'.1 using 1 <;> simp only [Nat.cast_add, Nat.cast_sub hr1, Nat.cast_one] <;> ring
    · convert hAll'.1 using 1 <;> simp only [Nat.cast_add, Nat.cast_sub hr1, Nat.cast_one] <;> ring
  · apply weightBounds_surfaceMap_flag
    · convert hR'.2.1 using 1 <;> simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
    · convert hYR'.2.1 using 1 <;> simp only [Nat.cast_add, Nat.cast_sub hv, Nat.cast_one] <;> ring
    · convert hAll'.2.1 using 1 <;> simp only [Nat.cast_add, Nat.cast_sub hv, Nat.cast_one] <;> ring
  · apply weightBounds_surfaceMap_flag
    · convert hR'.2.2 using 1 <;> simp only [Nat.cast_sub hr, Nat.cast_ofNat]
    · convert hYR'.2.2 using 1 <;> simp only [Nat.cast_add, Nat.cast_sub hr, Nat.cast_ofNat] <;> ring
    · convert hAll'.2.2 using 1 <;> simp only [Nat.cast_add, Nat.cast_sub hr, Nat.cast_ofNat] <;> ring

theorem coefficientFlag_pole {L : Type*} [Field L]
    (V : Valuation L (WithZero (Multiplicative ℤ))) (x : Fin 3 → L)
    (m i r v z : ℕ) (hm : 1 ≤ m) (hi : i ≤ m + 1) (hv : 2 ≤ v) :
    RCN204.flagPole V x (coefficientFlag m i r v z) =
      (i : ℤ) * (2 * RCN204.flagPole V x unitAllFlag - RCN204.flagPole V x unitYZFlag) +
      ((min (2 * i) m : ℕ) : ℤ) * RCN204.flagPole V x (⟨z, v, r - 2⟩ : FlagDegree) := by
  have hsafe := coefficientFlag_sub_safe hm hi hv
  simp only [RCN204.flagPole, coefficientFlag, unitAllFlag, unitYZFlag,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Nat.cast_sub hsafe]
  ring

theorem refinedCoefficients_value_le {L : Type*} [Field L]
    (V : Valuation L (WithZero (Multiplicative ℤ)))
    (coeff : Ω →+* L) (hcoeff : ∀ a, V (coeff a) ≤ 1) (x : Fin 3 → L)
    (φ : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K) (m i r v z : ℕ)
    (hm : 1 ≤ m) (hi : i ≤ m + 1) (hr : 2 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r + v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r + v + z : ℕ) : ℤ)) :
    V (MvPolynomial.eval₂Hom coeff x (surfaceMap φ (refinedCoefficients F m i))) ≤
      WithZero.exp ((i : ℤ) * (2 * RCN204.flagPole V x unitAllFlag -
        RCN204.flagPole V x unitYZFlag) + ((min (2 * i) m : ℕ) : ℤ) *
        RCN204.flagPole V x (⟨z, v, r - 2⟩ : FlagDegree)) := by
  rw [← coefficientFlag_pole V x m i r v z hm hi hv]
  exact RCN204.valuation_eval_le_flag V coeff hcoeff x _ _
    (refinedCoefficients_surfaceMap_flag φ F m i r v z hm hi hr hv hR hYR hAll)

end
end ProximityPrize.SubmissionLower.BoundaryTailAlgebra


