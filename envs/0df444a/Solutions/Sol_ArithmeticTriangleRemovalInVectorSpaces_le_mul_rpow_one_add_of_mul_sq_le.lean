-- Prove2me | solution 1 for ArithmeticTriangleRemovalInVectorSpaces.le_mul_rpow_one_add_of_mul_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:15:18.724925+00:00
-- url     : https://prove2.me/submissions/1d0956c1-60cf-460f-a2d0-619b85a04898

module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_Tightness_Exponent

set_option autoImplicit true
@[expose] public section
public section
open ArithmeticTriangleRemovalInVectorSpaces
namespace ArithmeticTriangleRemovalInVectorSpaces
theorem _root_.solution {P N ε δ κ : ℝ} (hP : 0 < P) (hN : 0 < N) (hε0 : 0 < ε)
    (hε₁ : ε ≤ 1) (hκ : 1 ≤ κ) (hNε : N⁻¹ ≤ P * ε ^ κ) (hδ : δ * N ^ 2 ≤ ε * N + 1) :
    δ ≤ (P + P ^ 2) * ε ^ (1 + κ) := by
  have hεκ : ε ^ κ ≤ ε := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hε0 hε₁ hκ
  calc δ ≤ (ε * N + 1) / N ^ 2 := (le_div_iff₀ (by positivity)).2 hδ
    _ = ε * N⁻¹ + N⁻¹ ^ 2 := by field_simp
    _ ≤ ε * (P * ε ^ κ) + (P * ε ^ κ) ^ 2 := by gcongr
    _ ≤ (P + P ^ 2) * (ε * ε ^ κ) := by
        nlinarith [Real.rpow_pos_of_pos hε0 κ, mul_le_mul_of_nonneg_left hεκ
          (by positivity : 0 ≤ P ^ 2 * ε ^ κ)]
    _ = (P + P ^ 2) * ε ^ (1 + κ) := by rw [Real.rpow_add hε0, Real.rpow_one]
end ArithmeticTriangleRemovalInVectorSpaces
