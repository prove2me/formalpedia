-- Prove2me | Definitions.Def_CK_GeneralCK_FCEtaPoints
-- name    : CK_GeneralCK_FCEtaPoints
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:28:41.231959+00:00
-- url     : https://prove2.me/theorems/0b98396e-b74e-44a5-ac3c-0e5ab631d2de
-- title:
--   Courtade–Kumar proof module `GeneralCK.FCEtaPoints` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.FCEtaPoints` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.FCEtaPoints` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.FCEtaPoints (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/FCEtaPoints.lean)

import Definitions.Def_CK_GeneralCK_FCDecrement

-- ===== source module GeneralCK.FCEtaPoints =====
section

/-!
# Lane F-C: rigorous numeric enclosures of `eta` at two rational points

The last inequality needs `eta (1/10) − eta (1/2) ≤ 49/10`, with a budget that
allows 24% of slack against the true value 3.782.  Both enclosures are obtained
the corpus way — a rational bracket on `H` at a rational point, transported
through `H_strictMonoOn` to `entropyInverse`, then through `J_antitone`.

Only `log x ≤ x − 1` and integer power comparisons are used; no interval
arithmetic on a singular quotient, and nothing near the `1e-09` bracket floor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace GeneralCK.FCEtaPoints

open GeneralCK

theorem log_96_upper : Real.log 96 ≤ (33 / 5 : ℝ) * Real.log 2 := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 96 ^ (5 : ℕ))
    (by norm_num : (96 : ℝ) ^ (5 : ℕ) ≤ 2 ^ (33 : ℕ))
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

theorem log_95_upper : Real.log 95 ≤ (33 / 5 : ℝ) * Real.log 2 := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 95 ^ (5 : ℕ))
    (by norm_num : (95 : ℝ) ^ (5 : ℕ) ≤ 2 ^ (33 : ℕ))
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

/-- `H (1/96) ≤ 1/10`. -/
theorem H_ninetysixth_upper : H (1 / 96 : ℝ) ≤ 1 / 10 := by
  have hLpos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hL := FCAnalytic.log_two_lb
  have hLu := FCAnalytic.log_two_ub
  have htail : Real.log ((96 : ℝ) / 95) ≤ 1 / 95 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 96 / 95)
    linarith
  have hHid : H (1 / 96 : ℝ) * Real.log 2
      = (1 / 96) * Real.log 96 + (95 / 96) * Real.log (96 / 95) := by
    unfold H Real.binEntropy
    rw [div_mul_cancel₀ _ hLpos.ne']
    rw [show (1 : ℝ) - 1 / 96 = 95 / 96 by norm_num]
    rw [show ((1 : ℝ) / 96)⁻¹ = 96 by norm_num,
      show ((95 : ℝ) / 96)⁻¹ = 96 / 95 by norm_num]
  have hbound : H (1 / 96 : ℝ) * Real.log 2 ≤ (1 / 10 : ℝ) * Real.log 2 := by
    rw [hHid]
    nlinarith only [log_96_upper, htail, hL, hLu, hLpos]
  exact le_of_mul_le_mul_right hbound hLpos

/-- `entropyInverse (1/10) ≥ 1/96`. -/
theorem entropyInverse_tenth_lower : (1 / 96 : ℝ) ≤ entropyInverse (1 / 10) := by
  by_contra hcon
  push_neg at hcon
  have hv : 0 < entropyInverse (1 / 10 : ℝ) :=
    entropyInverse_pos (by norm_num) (by norm_num)
  have hvhalf : entropyInverse (1 / 10 : ℝ) < 1 / 2 :=
    entropyInverse_lt_half (by norm_num) (by norm_num)
  have hHv : H (entropyInverse (1 / 10 : ℝ)) = 1 / 10 :=
    (entropyInverse_spec (by norm_num) (by norm_num)).2.2
  have hmono := H_strictMonoOn
    (show entropyInverse (1 / 10 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) from ⟨hv.le, hvhalf.le⟩)
    (show (1 / 96 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 2) by constructor <;> norm_num) hcon
  rw [hHv] at hmono
  linarith [H_ninetysixth_upper]

/-- `eta (1/10) ≤ 33/5`. -/
theorem eta_tenth_upper : eta (1 / 10 : ℝ) ≤ 33 / 5 := by
  have hv : 0 < entropyInverse (1 / 10 : ℝ) :=
    entropyInverse_pos (by norm_num) (by norm_num)
  have hvhalf : entropyInverse (1 / 10 : ℝ) < 1 / 2 :=
    entropyInverse_lt_half (by norm_num) (by norm_num)
  have hlow := entropyInverse_tenth_lower
  have hJ : J (entropyInverse (1 / 10 : ℝ)) ≤ J (1 / 96 : ℝ) :=
    J_antitone (by norm_num) hvhalf.le hlow
  have hJval : J (1 / 96 : ℝ) ≤ 33 / 5 := by
    unfold J
    rw [show ((1 : ℝ) - 1 / 96) / (1 / 96) = 95 by norm_num]
    rw [div_le_iff₀ log_two_pos]
    linarith [log_95_upper]
  have hJnn : 0 ≤ J (entropyInverse (1 / 10 : ℝ)) := J_nonneg hv hvhalf.le
  rw [eta_eq_profile (by norm_num : (0 : ℝ) ≤ 1 / 10) (by norm_num : (1 / 10 : ℝ) ≤ 1)]
  nlinarith only [hJ, hJval, hJnn, hv]

theorem log_87_13_lower : (27 / 10 : ℝ) * Real.log 2 ≤ Real.log (87 / 13) := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ (27 : ℕ))
    (by norm_num : (2 : ℝ) ^ (27 : ℕ) ≤ (87 / 13) ^ (10 : ℕ))
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

theorem log_100_87_lower : (1 : ℝ) / 8 ≤ Real.log (100 / 87) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 87 / 100)
  have hinv : Real.log ((87 : ℝ) / 100) = -Real.log ((100 : ℝ) / 87) := by
    rw [show (87 : ℝ) / 100 = ((100 : ℝ) / 87)⁻¹ by norm_num, Real.log_inv]
  rw [hinv] at h
  linarith

theorem log_100_13_lower : (29 / 10 : ℝ) * Real.log 2 ≤ Real.log (100 / 13) := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ (29 : ℕ))
    (by norm_num : (2 : ℝ) ^ (29 : ℕ) ≤ (100 / 13) ^ (10 : ℕ))
  rw [Real.log_pow, Real.log_pow] at h
  norm_num at h
  linarith

/-- `H (13/100) ≥ 1/2`. -/
theorem H_thirteenth_lower : (1 / 2 : ℝ) ≤ H (13 / 100) := by
  have hLpos : (0 : ℝ) < Real.log 2 := log_two_pos
  have hLu := FCAnalytic.log_two_ub
  have hHid : H (13 / 100 : ℝ) * Real.log 2
      = (13 / 100) * Real.log (100 / 13) + (87 / 100) * Real.log (100 / 87) := by
    unfold H Real.binEntropy
    rw [div_mul_cancel₀ _ hLpos.ne']
    rw [show (1 : ℝ) - 13 / 100 = 87 / 100 by norm_num]
    rw [show ((13 : ℝ) / 100)⁻¹ = 100 / 13 by norm_num,
      show ((87 : ℝ) / 100)⁻¹ = 100 / 87 by norm_num]
  have hbound : (1 / 2 : ℝ) * Real.log 2 ≤ H (13 / 100 : ℝ) * Real.log 2 := by
    rw [hHid]
    nlinarith only [log_100_13_lower, log_100_87_lower, hLu, hLpos]
  exact le_of_mul_le_mul_right hbound hLpos

/-- `entropyInverse (1/2) ≤ 13/100`. -/
theorem entropyInverse_half_upper : entropyInverse (1 / 2 : ℝ) ≤ 13 / 100 := by
  have hmono := entropyInverse_mono (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (H_le_one (13 / 100 : ℝ)) (le_trans (by norm_num) H_thirteenth_lower)
  rwa [entropyInverse_H_lower (by norm_num : (0 : ℝ) ≤ 13 / 100)
    (by norm_num : (13 : ℝ) / 100 ≤ 1 / 2)] at hmono

/-- `eta (1/2) ≥ 199/100`. -/
theorem eta_half_lower : (199 / 100 : ℝ) ≤ eta (1 / 2) := by
  have hv : 0 < entropyInverse (1 / 2 : ℝ) :=
    entropyInverse_pos (by norm_num) (by norm_num)
  have hvhalf : entropyInverse (1 / 2 : ℝ) < 1 / 2 :=
    entropyInverse_lt_half (by norm_num) (by norm_num)
  have hup := entropyInverse_half_upper
  have hJ : J (13 / 100 : ℝ) ≤ J (entropyInverse (1 / 2 : ℝ)) :=
    J_antitone hv (by norm_num) hup
  have hJval : (27 / 10 : ℝ) ≤ J (13 / 100 : ℝ) := by
    unfold J
    rw [show ((1 : ℝ) - 13 / 100) / (13 / 100) = 87 / 13 by norm_num]
    rw [le_div_iff₀ log_two_pos]
    linarith [log_87_13_lower]
  rw [eta_eq_profile (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  nlinarith only [hJ, hJval, hup, hv]

/-- The gap the split needs: `eta (1/10) − eta (1/2) ≤ 49/10`.
True value 3.782; the budget allows 4.97, so this carries 24% of headroom. -/
theorem eta_gap_tenth_half : eta (1 / 10 : ℝ) - eta (1 / 2) ≤ 49 / 10 := by
  linarith [eta_tenth_upper, eta_half_lower]

#check @eta_tenth_upper
#check @eta_half_lower
#check @eta_gap_tenth_half
#print axioms eta_tenth_upper
#print axioms eta_half_lower
#print axioms eta_gap_tenth_half

end GeneralCK.FCEtaPoints

end


