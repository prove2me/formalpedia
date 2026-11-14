-- Prove2me | solution 1 for AFT.RationalNumerics.HeightBound.add
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T02:29:40.615608+00:00
-- url     : https://prove2.me/submissions/4a8f0db0-6dc9-45e4-8163-8c8b262505a3

import Definitions.Def_InfoLossLAR_Native_AFT_RationalHeight
import Mathlib


/-! # Explicit binary height bounds for executable rational arithmetic -/
namespace AFT.RationalNumerics
end AFT.RationalNumerics
section AFT.RationalNumerics
open AFT.RationalNumerics
open scoped BigOperators



namespace AFT.RationalNumerics.HeightBound
end AFT.RationalNumerics.HeightBound
section HeightBound
open AFT.RationalNumerics.HeightBound



private theorem _root_.AFT.RationalNumerics.HeightBound.reduced_le (num : ℤ) (den : ℕ) (hd : 0 < den) :
    (Rat.divInt num (den : ℤ)).num.natAbs ≤ num.natAbs ∧ (Rat.divInt num (den : ℤ)).den ≤ den := by
  constructor
  · by_cases hn : num=0
    · simp [hn]
    · exact Nat.le_of_dvd (Int.natAbs_pos.mpr hn)
        (Int.natAbs_dvd_natAbs.mpr (Rat.num_dvd num (by exact_mod_cast hd.ne')))
  · exact Nat.le_of_dvd hd (by exact_mod_cast Rat.den_dvd num (den : ℤ))












theorem solution {first second : ℚ} {firstBits secondBits : ℕ}
    (hf : HeightBound first firstBits) (hs : HeightBound second secondBits) :
    HeightBound (first+second) (firstBits+secondBits+1) := by
  have hr := reduced_le (first.num*second.den+first.den*second.num) (first.den*second.den)
    (Nat.mul_pos first.den_pos second.den_pos)
  rw [Nat.cast_mul] at hr
  rw [← Rat.add_num_den] at hr
  have hnum : (first.num*second.den+first.den*second.num).natAbs ≤
      2*(2^firstBits*2^secondBits) := by
    apply (Int.natAbs_add_le _ _).trans
    simp only [Int.natAbs_mul,Int.natAbs_natCast]
    have h1 := Nat.mul_le_mul hf.1 hs.2
    have h2 := Nat.mul_le_mul hf.2 hs.1
    omega
  have he : 2*(2^firstBits*2^secondBits)=2^(firstBits+secondBits+1) := by simp only [pow_add,pow_one]; ring
  refine ⟨hr.1.trans (hnum.trans_eq he),?_⟩
  have hh := hr.2.trans (Nat.mul_le_mul hf.2 hs.2)
  rw [← pow_add] at hh
  exact hh.trans (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega))













end HeightBound
end AFT.RationalNumerics
