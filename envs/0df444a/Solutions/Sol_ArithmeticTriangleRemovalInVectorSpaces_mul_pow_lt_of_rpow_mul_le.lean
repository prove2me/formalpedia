-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.mul_pow_lt_of_rpow_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:15.251699+00:00
-- url     : https://prove2.me/submissions/b23d23e7-3942-40f5-9a5b-e99f03c97d01

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent

set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {P ε γ a m : ℝ} {n : ℕ} (hP : 1 < P) (hε : 0 < ε) (hn : 0 < n)
    (ha : 1 - γ < a) (h : (P ^ γ) ^ n ≤ ε⁻¹) (hm : P ^ (a * n) ≤ m) : ε * P ^ n < m := by
  calc ε * P ^ n ≤ ((P ^ γ) ^ n)⁻¹ * P ^ n := by
        grw [(le_inv_comm₀ hε (by positivity)).2 h]
    _ = P ^ ((1 - γ) * n) := by
        rw [← Real.rpow_mul_natCast (by positivity), ← Real.rpow_neg (by positivity),
          ← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
        ring_nf
    _ < P ^ (a * n) :=
        Real.rpow_lt_rpow_of_exponent_lt hP (mul_lt_mul_of_pos_right ha (by exact_mod_cast hn))
    _ ≤ m := hm
end ArithmeticTriangleRemovalInVectorSpaces
