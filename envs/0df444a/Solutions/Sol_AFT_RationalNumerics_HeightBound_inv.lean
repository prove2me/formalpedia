-- Prove2me | solution 1 for AFT.RationalNumerics.HeightBound.inv
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T03:10:39.339581+00:00
-- url     : https://prove2.me/submissions/0698d97a-0e65-4bc4-98b4-3ba7c72b7be8

import Definitions.Def_InfoLossLAR_Native_AFT_RationalHeight
import Mathlib


/-! # Explicit binary height bounds for executable rational arithmetic -/
namespace AFT.RationalNumerics
end AFT.RationalNumerics
section AFT
section RationalNumerics
open AFT.RationalNumerics
open scoped BigOperators



namespace AFT.RationalNumerics.HeightBound
end AFT.RationalNumerics.HeightBound
section HeightBound
open AFT.RationalNumerics.HeightBound




















theorem solution {value : ℚ} {bits : ℕ} (h : HeightBound value bits) : HeightBound value⁻¹ bits := by
  by_cases hz : value=0
  · subst value
    norm_num [HeightBound]
    exact Nat.one_le_pow bits 2 (by decide)
  constructor
  · simp only [Rat.num_inv,Int.natAbs_mul,Int.natAbs_natCast]
    have hsign : value.num.sign.natAbs=1 := by
      rcases lt_or_gt_of_ne (Rat.num_ne_zero.mpr hz) with hn|hn
      · simp [Int.sign_eq_neg_one_of_neg hn]
      · simp [Int.sign_eq_one_of_pos hn]
    simpa only [hsign,one_mul,mul_one] using h.2
  · simpa only [Rat.den_inv_of_ne_zero hz] using h.1









end HeightBound
end RationalNumerics
end AFT
