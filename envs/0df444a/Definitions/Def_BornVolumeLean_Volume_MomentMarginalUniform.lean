-- Prove2me | Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
-- name    : BornVolumeLean_Volume_MomentMarginalUniform
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:51:15.028569+00:00
-- url     : https://prove2.me/theorems/b5c51c58-03c1-41e9-ad5a-94a88ffa6cc9
-- title:
--   Moment Marginal Uniform
-- statement:
--   Definitions and structural lemmas for Moment Marginal Uniform, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentMarginalUniform.lean

module
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory Real Set
open scoped ENNReal
namespace BornVolume
noncomputable def gaussian2 : Measure (ℝ × ℝ) :=
  volume.withDensity
    (fun p => ENNReal.ofReal ((1 / (2 * Real.pi)) * Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2)))
noncomputable def expHalf : Measure ℝ :=
  volume.withDensity
    (fun s => ENNReal.ofReal (if 0 < s then (1 / 2) * Real.exp (-s / 2) else 0))
theorem measurable_gaussian2_density :
    Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((1 / (2 * Real.pi)) * Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2))) := by
  fun_prop
theorem measurable_expHalf_density :
    Measurable (fun s : ℝ =>
      ENNReal.ofReal (if 0 < s then (1 / 2) * Real.exp (-s / 2) else 0)) := by
  apply ENNReal.measurable_ofReal.comp
  refine Measurable.ite (measurableSet_lt measurable_const measurable_id) ?_ measurable_const
  fun_prop
theorem sqNorm_map_gaussian2 :
    Measure.map (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) gaussian2 = expHalf := by
  -- Squared-norm map and its measurability.
  set Lsq : ℝ × ℝ → ℝ := fun p => p.1 ^ 2 + p.2 ^ 2 with hLsq
  have hLsq_meas : Measurable Lsq := by fun_prop
  -- Characterise the measure equality by all measurable test functions `g`.
  refine Measure.ext_of_lintegral _ (fun g hg => ?_)
  -- LHS: push through `Lsq`, then expose the density.
  have hgLsq : Measurable (fun a => g (Lsq a)) := hg.comp hLsq_meas
  rw [lintegral_map hg hLsq_meas, gaussian2,
    lintegral_withDensity_eq_lintegral_mul _ measurable_gaussian2_density hgLsq]
  -- The polar integrand `f`.
  set f : ℝ × ℝ → ℝ≥0∞ :=
    fun p => (fun p : ℝ × ℝ =>
        ENNReal.ofReal ((1 / (2 * Real.pi)) * Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2)))
      p * (fun a => g (Lsq a)) p with hf
  have hf_meas : Measurable f :=
    measurable_gaussian2_density.mul hgLsq
  show ∫⁻ p, f p = _
  -- Polar change of variables.
  rw [← lintegral_comp_polarCoord_symm f]
  -- On the target, `Lsq (polarCoord.symm (r,θ)) = r²` since `(r cosθ)²+(r sinθ)² = r²`,
  -- so the integrand becomes θ-independent.
  have hpolar :
      ∀ p ∈ polarCoord.target,
        ENNReal.ofReal p.1 • f (polarCoord.symm p)
          = ENNReal.ofReal p.1 *
              (ENNReal.ofReal ((1 / (2 * Real.pi)) * Real.exp (-(p.1 ^ 2) / 2))
                * g (p.1 ^ 2)) := by
    intro p _
    have hsymm : polarCoord.symm p = (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := rfl
    have hsq : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
      have := Real.sin_sq_add_cos_sq p.2
      nlinarith [Real.sin_sq_add_cos_sq p.2]
    simp only [hf, hLsq, smul_eq_mul, hsymm, hsq]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hpolar]
  -- Split the product set `Ioi 0 ×ˢ Ioo (-π) π` via Tonelli.
  rw [show (polarCoord.target : Set (ℝ × ℝ)) = Ioi (0 : ℝ) ×ˢ Ioo (-π) π from rfl,
    Measure.volume_eq_prod, setLIntegral_prod]
  · -- The inner (θ) integral is of a θ-constant over `Ioo (-π) π`, length `2π`.
    have hθ :
        ∀ r : ℝ,
          ∫⁻ _θ in Ioo (-π) π,
            ENNReal.ofReal r *
              (ENNReal.ofReal ((1 / (2 * Real.pi)) * Real.exp (-(r ^ 2) / 2))
                * g (r ^ 2)) ∂(volume : Measure ℝ)
          = ENNReal.ofReal (2 * π) *
              (ENNReal.ofReal r *
                (ENNReal.ofReal ((1 / (2 * Real.pi)) * Real.exp (-(r ^ 2) / 2))
                  * g (r ^ 2))) := by
      intro r
      rw [setLIntegral_const, Real.volume_Ioo]
      ring_nf
    simp only [hθ]
    -- Fold the `2π · (1/2π) · r · exp(-r²/2)` factor to `r · exp(-r²/2)`.
    have hfold :
        ∀ r ∈ Ioi (0 : ℝ),
          ENNReal.ofReal (2 * π) *
              (ENNReal.ofReal r *
                (ENNReal.ofReal ((1 / (2 * Real.pi)) * Real.exp (-(r ^ 2) / 2))
                  * g (r ^ 2)))
            = g (r ^ 2) * ENNReal.ofReal (r * Real.exp (-(r ^ 2) / 2)) := by
      intro r hr
      have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
      have hpi : (0 : ℝ) < 2 * π := by positivity
      have hexp : (0 : ℝ) ≤ Real.exp (-(r ^ 2) / 2) := (Real.exp_pos _).le
      have hcollect :
          ENNReal.ofReal (2 * π) *
              (ENNReal.ofReal r *
                (ENNReal.ofReal ((1 / (2 * Real.pi)) * Real.exp (-(r ^ 2) / 2))
                  * g (r ^ 2)))
            = ENNReal.ofReal
                ((2 * π) * (r * ((1 / (2 * Real.pi)) * Real.exp (-(r ^ 2) / 2)))) * g (r ^ 2) := by
        rw [ENNReal.ofReal_mul hpi.le, ENNReal.ofReal_mul hr0]
        ring
      rw [hcollect, mul_comm]
      congr 1
      rw [ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)]
      field_simp
    rw [setLIntegral_congr_fun measurableSet_Ioi hfold]
    -- Substitute `s = r²` on `Ioi 0`: `f r = r²`, `f' r = 2r`, `f '' Ioi 0 = Ioi 0`.
    -- RHS: `∫⁻ s, g s · expHalf-density s = ∫⁻ s in Ioi 0, g s · (1/2)exp(-s/2)`.
    rw [expHalf,
      lintegral_withDensity_eq_lintegral_mul _ measurable_expHalf_density hg]
    -- Push the `expHalf` integrand to the `Ioi 0` restriction (density is 0 off `Ioi 0`).
    have hRHS :
        ∫⁻ s, (fun s : ℝ =>
            ENNReal.ofReal (if 0 < s then (1 / 2) * Real.exp (-s / 2) else 0) * g s) s
          = ∫⁻ s in Ioi (0 : ℝ), g s * ENNReal.ofReal ((1 / 2) * Real.exp (-s / 2)) := by
      rw [← lintegral_indicator measurableSet_Ioi]
      congr 1
      ext s
      simp only [Set.indicator_apply, mem_Ioi]
      by_cases hs : 0 < s
      · simp only [if_pos hs]
        ring
      · simp only [if_neg hs, ENNReal.ofReal_zero, zero_mul]
    rw [show (fun a => ((fun s : ℝ =>
          ENNReal.ofReal (if 0 < s then (1 / 2) * Real.exp (-s / 2) else 0)) * g) a)
          = (fun s : ℝ =>
            ENNReal.ofReal (if 0 < s then (1 / 2) * Real.exp (-s / 2) else 0) * g s) from rfl,
      hRHS]
    -- 1-D change of variables: `∫⁻ s in Ioi 0, h s = ∫⁻ r in Ioi 0, |2r| · h (r²)`.
    have hsqimage : (fun r : ℝ => r ^ 2) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
      ext s
      simp only [mem_image, mem_Ioi]
      constructor
      · rintro ⟨r, hr, rfl⟩; positivity
      · intro hs
        exact ⟨Real.sqrt s, Real.sqrt_pos.mpr hs, Real.sq_sqrt hs.le⟩
    have hderiv : ∀ r ∈ Ioi (0 : ℝ),
        HasDerivWithinAt (fun r : ℝ => r ^ 2) (2 * r) (Ioi (0 : ℝ)) r := by
      intro r _
      simpa using (hasDerivAt_pow 2 r).hasDerivWithinAt
    have hinj : InjOn (fun r : ℝ => r ^ 2) (Ioi (0 : ℝ)) := by
      intro a ha b hb hab
      simp only [mem_Ioi] at ha hb
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
    have hcov :
        ∫⁻ s in Ioi (0 : ℝ), g s * ENNReal.ofReal ((1 / 2) * Real.exp (-s / 2))
          = ∫⁻ r in Ioi (0 : ℝ),
              ENNReal.ofReal |2 * r| *
                (g (r ^ 2) * ENNReal.ofReal ((1 / 2) * Real.exp (-(r ^ 2) / 2))) := by
      conv_lhs => rw [← hsqimage]
      rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderiv hinj
        (fun s => g s * ENNReal.ofReal ((1 / 2) * Real.exp (-s / 2)))]
    rw [hcov]
    -- Match integrands pointwise on `Ioi 0`.
    refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    simp only [mem_Ioi] at hr
    have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * r)]
    rw [mul_left_comm]
    congr 1
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)]
    ring
  · -- AEMeasurability of the product integrand.
    apply Measurable.aemeasurable
    fun_prop
open ProbabilityTheory
theorem gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
theorem gaussian2_eq_prod :
    gaussian2 = (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1),
    ← Measure.volume_eq_prod, gaussian2]
  congr 1
  ext p
  -- Pointwise density identity: `(1/2π)·e^{-(x²+y²)/2} = pdf(x)·pdf(y)`.
  rw [gaussianPDF, gaussianPDF, gaussianPDFReal_zero_one, gaussianPDFReal_zero_one,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hfact : (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹
      = 1 / (2 * Real.pi) := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity), one_div]
  -- Split the joint exponent into the two block exponents, then collapse the two
  -- `(√(2π))⁻¹` factors to `1/(2π)`; `exp` factors stay atomic throughout.
  rw [show (-(p.1 ^ 2 + p.2 ^ 2) / 2 : ℝ) = -p.1 ^ 2 / 2 + -p.2 ^ 2 / 2 by ring,
    Real.exp_add,
    show (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-p.1 ^ 2 / 2) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-p.2 ^ 2 / 2))
      = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ *
          (Real.exp (-p.1 ^ 2 / 2) * Real.exp (-p.2 ^ 2 / 2)) by ring,
    hfact]
instance instProbGaussian2 : IsProbabilityMeasure gaussian2 := by
  rw [gaussian2_eq_prod]; infer_instance
instance instProbExpHalf : IsProbabilityMeasure expHalf := by
  rw [← sqNorm_map_gaussian2]
  exact Measure.isProbabilityMeasure_map ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).aemeasurable
end BornVolume


