-- Prove2me | solution 1 for Auto.fourierPartialSum_sub_carlesonOp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:55:02.679497+00:00
-- url     : https://prove2.me/submissions/28e9f1d0-9966-48b3-8b6b-390e4e6df412

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_carlesonWeight_eq_mass
public import Theorems.Thm_Auto_carlesonWeight_nonneg
public import Theorems.Thm_Auto_carlesonWeight_le_mass
public import Theorems.Thm_Auto_carlesonWeight_eq_zero
public import Theorems.Thm_Auto_carlesonMass_pos
public import Theorems.Thm_Auto_continuous_dirichletKernel
public import Theorems.Thm_Auto_fourierPartialSum_eq_integral
public import Theorems.Thm_Auto_dirichletKernel_mul_sin
public import Theorems.Thm_Auto_abs_inv_sin_sub_le
public import Theorems.Thm_Auto_integrable_carlesonOp_integrand
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution {g : ℝ → ℂ} (hg : Continuous g)
    (hp : Function.Periodic g 1) {δ : ℝ} (hδ : ∀ x, ‖g x‖ ≤ δ) {R x : ℝ} (hx : |x| ≤ R) (N : ℕ) :
    ‖fourierPartialSum g N x - ((1 / (π * carlesonMass) : ℝ) : ℂ) *
      carlesonOp ((Icc (-(R + 11)) (R + 11)).indicator g) (fun _ => (2 * N + 1) * π) x‖ ≤
        22 * δ := by
  set M : ℝ := (2 * N + 1) * π
  set c : ℝ := 1 / (π * carlesonMass)
  set g' := (Icc (-(R + 11)) (R + 11)).indicator g
  have hm := carlesonMass_pos
  have hπ := Real.pi_pos
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hδ 0)
  have hg' : ∀ s, |s| ≤ 11 → g' (x - s) = g (x - s) := fun s hs => by
    refine indicator_of_mem ?_ _
    rw [mem_Icc, ← abs_le]
    exact (abs_sub _ _).trans (by linarith)
  have hg'B : ∀ y, ‖g' y‖ ≤ δ := fun y => by
    by_cases hy : y ∈ Icc (-(R + 11)) (R + 11)
    · rw [show g' y = g y from indicator_of_mem hy _]; exact hδ y
    · rw [show g' y = 0 from indicator_of_notMem hy _, norm_zero]; exact hδ0
  have hg'm : Measurable g' := hg.measurable.indicator measurableSet_Icc
  set A : ℝ → ℂ := (Ioc (-(1 / 2)) (1 / 2)).indicator fun s => g (x - s) * dirichletKernel N s
  set Bf : ℝ → ℂ := fun s => g' (x - s) * ((carlesonWeight s * Real.sin (M * s) / s : ℝ) : ℂ)
  have hA : fourierPartialSum g N x = ∫ s, A s := by
    rw [fourierPartialSum_eq_integral hg hp, intervalIntegral.integral_of_le (by norm_num),
      integral_indicator measurableSet_Ioc]
  have hAi : Integrable A := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact ((by fun_prop : Continuous fun s => g (x - s)).mul
      (continuous_dirichletKernel N)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hBi : Integrable Bf := integrable_carlesonOp_integrand hg'm hg'B M x
  have hpt : ∀ s, s ≠ 0 → ‖A s - (c : ℂ) * Bf s‖ ≤
      (Icc (-11 : ℝ) 11).indicator (fun _ => δ) s := by
    intro s hs0
    by_cases hsI : s ∈ Ioc (-(1 / 2) : ℝ) (1 / 2)
    · have hs : |s| ≤ 1 / 2 := abs_le.mpr ⟨hsI.1.le, hsI.2⟩
      have hsin : Real.sin (π * s) ≠ 0 := by
        have h1 := abs_le.mp hs
        rw [Ne, Real.sin_eq_zero_iff_of_lt_of_lt (by nlinarith) (by nlinarith)]
        exact mul_ne_zero hπ.ne' hs0
      have hD : dirichletKernel N s = (Real.sin (M * s) : ℂ) / (Real.sin (π * s) : ℂ) := by
        rw [eq_div_iff (by exact_mod_cast hsin), dirichletKernel_mul_sin]
      rw [indicator_of_mem (show s ∈ Icc (-11 : ℝ) 11 from ⟨by linarith [hsI.1], by
        linarith [hsI.2]⟩), show A s = g (x - s) * dirichletKernel N s from indicator_of_mem hsI _]
      simp only [Bf, hg' s (by linarith), carlesonWeight_eq_mass (by linarith : |s| ≤ 2), hD]
      have he : (g (x - s) * ((Real.sin (M * s) : ℂ) / (Real.sin (π * s) : ℂ)) -
          (c : ℂ) * (g (x - s) * ((carlesonMass * Real.sin (M * s) / s : ℝ) : ℂ))) =
          g (x - s) * (Real.sin (M * s) : ℂ) *
            ((1 / Real.sin (π * s) - 1 / (π * s) : ℝ) : ℂ) := by
        have h1 : (carlesonMass : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
        have h2 : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
        have h3 : ((Real.sin (π * s) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsin
        rw [Complex.ofReal_sin, Complex.ofReal_mul] at h3
        have h3' : Complex.sin (s * π) ≠ 0 := by rwa [mul_comm]
        have h4 : (π : ℂ) ≠ 0 := by exact_mod_cast hπ.ne'
        simp only [c]
        push_cast
        field_simp
      rw [he, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
      calc ‖g (x - s)‖ * |Real.sin (M * s)| * |1 / Real.sin (π * s) - 1 / (π * s)|
          ≤ δ * 1 * 1 := by
            gcongr
            · exact hδ _
            · exact Real.abs_sin_le_one _
            · exact abs_inv_sin_sub_le hs
        _ = δ := by ring
    · rw [show A s = 0 from indicator_of_notMem hsI _, zero_sub, norm_neg]
      have hs : 1 / 2 ≤ |s| := by
        by_contra h
        rw [not_le, abs_lt] at h
        exact hsI ⟨h.1, h.2.le⟩
      by_cases h11 : |s| < 11
      · rw [indicator_of_mem (show s ∈ Icc (-11 : ℝ) 11 from abs_le.mp h11.le), norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < c), norm_mul]
        have hw : ‖((carlesonWeight s * Real.sin (M * s) / s : ℝ) : ℂ)‖ ≤ 2 * carlesonMass := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
            abs_of_nonneg (carlesonWeight_nonneg s), div_le_iff₀ (by linarith)]
          have := Real.abs_sin_le_one (M * s)
          have := carlesonWeight_le_mass s
          have := carlesonWeight_nonneg s
          nlinarith
        calc c * (‖g' (x - s)‖ * ‖((carlesonWeight s * Real.sin (M * s) / s : ℝ) : ℂ)‖)
            ≤ c * (δ * (2 * carlesonMass)) := by
              gcongr
              · exact hg'B _
            _ = δ * (2 / π) := by simp only [c]; field_simp
            _ ≤ δ := by
              have : 2 / π ≤ 1 := by rw [div_le_one hπ]; linarith [Real.pi_gt_three]
              nlinarith
      · have h0 : Bf s = 0 := by simp [Bf, carlesonWeight_eq_zero (not_lt.mp h11)]
        rw [h0, mul_zero, norm_zero]
        exact indicator_nonneg (fun _ _ => hδ0) _
  have hbd : Integrable ((Icc (-11 : ℝ) 11).indicator fun _ => δ) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (C := δ) (by simp))
  calc ‖fourierPartialSum g N x - (c : ℂ) * carlesonOp g' (fun _ => M) x‖
      = ‖∫ s, (A s - (c : ℂ) * Bf s)‖ := by
        rw [hA, integral_sub hAi (hBi.const_mul _), integral_const_mul]
        rfl
    _ ≤ ∫ s, (Icc (-11 : ℝ) 11).indicator (fun _ => δ) s :=
        norm_integral_le_of_norm_le hbd (by
          filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with s hs
          exact hpt s hs)
    _ = 22 * δ := by
        rw [integral_indicator_const _ measurableSet_Icc, Measure.real, Real.volume_Icc,
          smul_eq_mul]
        norm_num
end Auto
