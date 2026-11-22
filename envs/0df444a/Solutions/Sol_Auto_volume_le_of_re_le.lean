-- Prove2me | solution 1 for Auto.volume_le_of_re_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:53:19.407614+00:00
-- url     : https://prove2.me/submissions/0d8f4e3d-d848-4517-9d6b-90c6ad6f4dbd

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution {Q : Set ℝ} (hQ : MeasurableSet Q) (hQf : volume Q ≠ ⊤) {z : ℝ → ℂ}
    (hz : IntegrableOn z Q) {K B lam : ℝ} (hKB : 0 ≤ K * B) (hlam : 0 < lam)
    (hK : ‖∫ x in Q, z x‖ ≤ K * B * (volume Q).toReal ^ (2 / 3 : ℝ)) {u : ℂ} (hu : ‖u‖ = 1)
    (hre : ∀ x ∈ Q, lam ≤ (u * z x).re) : (volume Q).toReal ≤ (K * B / lam) ^ 3 := by
  set v := (volume Q).toReal
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have h₁ : lam * v ≤ K * B * v ^ (2 / 3 : ℝ) := by
    calc lam * v = ∫ x in Q, lam := by rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl
      _ ≤ ∫ x in Q, (u * z x).re :=
          setIntegral_mono_on (integrableOn_const hQf) (hz.const_mul u).re hQ hre
      _ = (u * ∫ x in Q, z x).re := by
          rw [← integral_const_mul]
          exact integral_re (hz.const_mul u)
      _ ≤ ‖u * ∫ x in Q, z x‖ := Complex.re_le_norm _
      _ = ‖∫ x in Q, z x‖ := by rw [norm_mul, hu, one_mul]
      _ ≤ K * B * v ^ (2 / 3 : ℝ) := hK
  rcases hv.eq_or_lt with hv0 | hvpos
  · rw [← hv0]
    positivity
  have hsplit : v = v ^ (1 / 3 : ℝ) * v ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add hvpos]
    norm_num
  have h₂ : lam * v ^ (1 / 3 : ℝ) ≤ K * B := by
    have hpos : 0 < v ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hvpos _
    have h₁' : lam * v ^ (1 / 3 : ℝ) * v ^ (2 / 3 : ℝ) ≤ K * B * v ^ (2 / 3 : ℝ) := by
      rw [mul_assoc, ← hsplit]
      exact h₁
    exact le_of_mul_le_mul_right h₁' hpos
  have h₃ : v ^ (1 / 3 : ℝ) ≤ K * B / lam := by
    rw [le_div_iff₀ hlam, mul_comm]
    exact h₂
  calc v = (v ^ (1 / 3 : ℝ)) ^ 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hv]
        norm_num
    _ ≤ (K * B / lam) ^ 3 := pow_le_pow_left₀ (by positivity) h₃ 3
end Auto
