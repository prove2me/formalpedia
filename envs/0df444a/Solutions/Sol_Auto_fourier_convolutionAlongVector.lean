-- Prove2me | solution 1 for Auto.fourier_convolutionAlongVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:11:58.761494+00:00
-- url     : https://prove2.me/submissions/b4211bfb-66bd-4f85-904b-2796dd785e10

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_ConvolutionAlongVector
public import Theorems.Thm_Auto_aux_integrable_of_memW0

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric
open scoped FourierTransform RealInnerProductSpace
namespace Auto
theorem _root_.solution {n : ℕ}
    {rho : EuclideanSpace ℝ (Fin n) → ℂ} {phi : ℝ → ℂ}
    (hrho : MemW0 rho) (hphi : MemW0 phi)
    (alpha xi : EuclideanSpace ℝ (Fin n)) :
    FourierTransform.fourier (convolutionAlongVector rho phi alpha) xi =
      FourierTransform.fourier rho xi *
        FourierTransform.fourier phi (inner ℝ alpha xi) := by
  have hrho_integrable : Integrable rho := aux_integrable_of_memW0 hrho
  have hphi_integrable : Integrable phi := aux_integrable_of_memW0 hphi
  let K : EuclideanSpace ℝ (Fin n) × ℝ → ℂ := fun xp ↦
    rho (xp.1 - xp.2 • alpha) * phi xp.2
  have hK_measurable : AEStronglyMeasurable K
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume : Measure ℝ)) := by
    apply Continuous.aestronglyMeasurable
    exact
      (hrho.1.comp (continuous_fst.sub (continuous_snd.smul continuous_const))).mul
        (hphi.1.comp continuous_snd)
  have hK : Integrable K
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume : Measure ℝ)) := by
    rw [integrable_prod_iff' hK_measurable]
    refine ⟨Filter.Eventually.of_forall fun p ↦ ?_, ?_⟩
    · exact (hrho_integrable.comp_sub_right (p • alpha)).mul_const (phi p)
    · have hnorm (p : ℝ) :
          (∫ x : EuclideanSpace ℝ (Fin n), ‖K (x, p)‖) =
            (∫ x : EuclideanSpace ℝ (Fin n), ‖rho x‖) * ‖phi p‖ := by
        simp only [K, norm_mul]
        rw [integral_mul_const]
        congr 1
        exact integral_sub_right_eq_self
          (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖rho x‖) (p • alpha)
      convert hphi_integrable.norm.const_mul
        (∫ x : EuclideanSpace ℝ (Fin n), ‖rho x‖) using 1
      ext p
      rw [hnorm]
  let H : EuclideanSpace ℝ (Fin n) × ℝ → ℂ := fun xp ↦
    𝐞 (-inner ℝ xp.1 xi) • K xp
  have hH : Integrable H
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume : Measure ℝ)) := by
    refine hK.mono ?_ ?_
    · exact
        (Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable.smul
          hK.aestronglyMeasurable
    · filter_upwards with xp
      exact le_of_eq (Circle.norm_smul (𝐞 (-inner ℝ xp.1 xi)) (K xp))
  have htranslate (p : ℝ) :
      (∫ x : EuclideanSpace ℝ (Fin n),
        𝐞 (-inner ℝ x xi) • rho (x - p • alpha)) =
        𝐞 (-(p * inner ℝ alpha xi)) • FourierTransform.fourier rho xi := by
    calc
      (∫ x : EuclideanSpace ℝ (Fin n),
        𝐞 (-inner ℝ x xi) • rho (x - p • alpha)) =
          FourierTransform.fourier
            (rho ∘ fun x : EuclideanSpace ℝ (Fin n) ↦ x + (-p • alpha)) xi := by
            rw [Real.fourier_eq]
            congr 1
            ext x
            simp [sub_eq_add_neg]
      _ = 𝐞 (inner ℝ (-p • alpha) xi) • FourierTransform.fourier rho xi := by
        exact congrFun
          (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
            (innerₗ (EuclideanSpace ℝ (Fin n))) rho (-p • alpha)) xi
      _ = 𝐞 (-(p * inner ℝ alpha xi)) • FourierTransform.fourier rho xi := by
        congr 1
        rw [real_inner_smul_left]
        ring_nf
  calc
    FourierTransform.fourier (convolutionAlongVector rho phi alpha) xi =
        ∫ x : EuclideanSpace ℝ (Fin n), ∫ p : ℝ,
          𝐞 (-inner ℝ x xi) • (rho (x - p • alpha) * phi p) := by
      rw [Real.fourier_eq]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [convolutionAlongVector]
      simp_rw [Circle.smul_def, integral_smul]
    _ = ∫ p : ℝ, ∫ x : EuclideanSpace ℝ (Fin n),
          𝐞 (-inner ℝ x xi) • (rho (x - p • alpha) * phi p) := by
      apply integral_integral_swap
      change Integrable
        (Function.uncurry fun (x : EuclideanSpace ℝ (Fin n)) (p : ℝ) ↦
          𝐞 (-inner ℝ x xi) • (rho (x - p • alpha) * phi p)) _
      convert hH using 1; rfl
    _ = ∫ p : ℝ, ((∫ x : EuclideanSpace ℝ (Fin n),
          𝐞 (-inner ℝ x xi) • rho (x - p • alpha)) * phi p) := by
      congr with p
      rw [← integral_mul_const]
      congr with x
      simp [Circle.smul_def, mul_assoc]
    _ = ∫ p : ℝ, (𝐞 (-(p * inner ℝ alpha xi)) • FourierTransform.fourier rho xi) * phi p := by
      congr with p
      rw [htranslate p]
    _ = (FourierTransform.fourier rho xi) *
        ∫ p : ℝ, 𝐞 (-(p * inner ℝ alpha xi)) • phi p := by
      rw [← integral_const_mul]
      congr with p
      simp [Circle.smul_def]
      ring_nf
    _ = FourierTransform.fourier rho xi *
        FourierTransform.fourier phi (inner ℝ alpha xi) := by
      rw [← Real.fourier_real_eq]
end Auto
