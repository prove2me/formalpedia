-- Prove2me | solution 1 for Auto.aux_wienerEnvelope_sqrtGaussianDecayKernel_le_hundredSixty_bracket_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:16:19.084397+00:00
-- url     : https://prove2.me/submissions/eba38f6d-e3d0-4127-b881-d146cd61b443

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_Notation
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Definitions.Def_LeanNct_Auto_Preliminaries_Gaussians
public import Theorems.Thm_Auto_aux_sqrtGaussianKernel_continuous
public import Theorems.Thm_Auto_aux_abs_sqrtGaussianDecayKernel_le_forty_bracket_sq

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (x : ℝ) :
    wienerEnvelope aux_sqrtGaussianDecayKernel 1 x ≤
      160 * bracketBump x ^ 2 := by
  have hcont : Continuous aux_sqrtGaussianDecayKernel := by
    exact Complex.continuous_re.comp aux_sqrtGaussianKernel_continuous
  have hlocal (z : ℝ) (hz : z ∈ Metric.closedBall 0 1) :
      bracketBump (x + z) ^ 2 ≤ 4 * bracketBump x ^ 2 := by
    have hzabs : |z| ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hz
    have htri : |x| ≤ |x + z| + |z| := by
      calc
        |x| = |(x + z) + (-z)| := by ring_nf
        _ ≤ |x + z| + |-z| := abs_add_le _ _
        _ = |x + z| + |z| := by rw [abs_neg]
    have hxz_nonneg : 0 ≤ |x + z| := abs_nonneg _
    have hden : 1 + |x| ≤ 2 * (1 + |x + z|) := by linarith
    simp only [bracketBump]
    have hA : 0 < 1 + |x| := by positivity
    have hB : 0 < 1 + |x + z| := by positivity
    have hAsq : 0 < (1 + |x|) ^ 2 := sq_pos_of_pos hA
    have hBsq : 0 < (1 + |x + z|) ^ 2 := sq_pos_of_pos hB
    have hleft : (1 + |x + z|)⁻¹ ^ 2 = 1 / (1 + |x + z|) ^ 2 := by field_simp
    have hright : 4 * (1 + |x|)⁻¹ ^ 2 = 4 / (1 + |x|) ^ 2 := by field_simp
    rw [hleft, hright]
    apply (div_le_div_iff₀ hBsq hAsq).2
    have hsq : (1 + |x|) ^ 2 ≤ (2 * (1 + |x + z|)) ^ 2 :=
      (sq_le_sq₀ hA.le (by positivity)).mpr hden
    nlinarith
  unfold wienerEnvelope
  apply csSup_le
  · exact (Metric.nonempty_closedBall.mpr zero_le_one).image _
  rintro _ ⟨z, hz, rfl⟩
  change ‖aux_sqrtGaussianDecayKernel (x + z)‖ ≤ 160 * bracketBump x ^ 2
  rw [Real.norm_eq_abs]
  calc
    |aux_sqrtGaussianDecayKernel (x + z)| ≤
        40 * bracketBump (x + z) ^ 2 :=
      aux_abs_sqrtGaussianDecayKernel_le_forty_bracket_sq _
    _ ≤ 40 * (4 * bracketBump x ^ 2) :=
      mul_le_mul_of_nonneg_left (hlocal z hz) (by norm_num)
    _ = 160 * bracketBump x ^ 2 := by ring
end Auto
