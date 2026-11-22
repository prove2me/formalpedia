-- Prove2me | solution 1 for Auto.sourceGaussian_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:56:15.317168+00:00
-- url     : https://prove2.me/submissions/8217b7df-2364-4260-9eb1-16ec29b85bd3

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_heatBoundConstant_nonneg
public import Theorems.Thm_Auto_sourceGaussian_continuous
public import Theorems.Thm_Auto_sourceGaussian_compact_bound
public import Theorems.Thm_Auto_compactCutoff_bounds
public import Theorems.Thm_Auto_compactCutoff_continuous
public import Theorems.Thm_Auto_compactCutoff_support
public import Theorems.Thm_Auto_compactCutoff_tendsto
public import Theorems.Thm_Auto_toReal_eLpNorm_three

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution (F : Fin 3 → ℝ × ℝ → ℂ)
    (hc : ∀ v, Continuous (F v)) (hL : ∀ v, MemLp (F v) 3)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hi : Integrable (sourceGaussianIntegrand F a b)) :
    ‖∫ x, sourceGaussianIntegrand F a b x‖ ≤
      3 * heatBoundConstant * ∏ v, (eLpNorm (F v) 3).toReal := by
  let f (n : ℕ) (v : Fin 3) (p : ℝ × ℝ) : ℂ := compactCutoff n p * F v p
  have hfc (n : ℕ) (v : Fin 3) : Continuous (f n v) :=
    (Complex.continuous_ofReal.comp (compactCutoff_continuous n)).mul (hc v)
  have hfs (n : ℕ) (v : Fin 3) : HasCompactSupport (f n v) :=
    ((compactCutoff_support n).comp_left Complex.ofReal_zero).mul_right
  have hfn (n : ℕ) (v : Fin 3) (p : ℝ × ℝ) : ‖f n v p‖ ≤ ‖F v p‖ := by
    dsimp [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (compactCutoff_bounds n p).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (compactCutoff_bounds n p).2
  have hLp (n : ℕ) (v : Fin 3) :
      (eLpNorm (f n v) 3).toReal ≤ (eLpNorm (F v) 3).toReal :=
    ENNReal.toReal_mono (hL v).eLpNorm_ne_top (eLpNorm_mono (hfn n v))
  have hfbound (n : ℕ) : ‖∫ x, sourceGaussianIntegrand (f n) a b x‖ ≤
      3 * heatBoundConstant * ∏ v, (eLpNorm (F v) 3).toReal := by
    have h := sourceGaussian_compact_bound (f n) (hfc n) (hfs n) ha hab
    simp_rw [← toReal_eLpNorm_three ((hfc n _).memLp_of_hasCompactSupport (hfs n _))] at h
    refine h.trans (mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun _ _ => ENNReal.toReal_nonneg) (fun v _ => hLp n v)) ?_)
    positivity [heatBoundConstant_nonneg]
  have hlim : Tendsto (fun n => ∫ x, sourceGaussianIntegrand (f n) a b x)
      atTop (𝓝 (∫ x, sourceGaussianIntegrand F a b x)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => ‖sourceGaussianIntegrand F a b x‖)
    · intro n
      exact (sourceGaussian_continuous (f n) (hfc n) ha hab).aestronglyMeasurable
    · exact hi.norm
    · intro n
      filter_upwards [] with x
      simp only [sourceGaussianIntegrand, norm_mul]
      gcongr <;> apply hfn
    · filter_upwards [] with x
      have hf (v : Fin 3) (p : ℝ × ℝ) :
          Tendsto (fun n => f n v p) atTop (𝓝 (F v p)) := by
        simpa [f] using
          ((Complex.continuous_ofReal.tendsto 1).comp (compactCutoff_tendsto p)).mul_const (F v p)
      exact (((hf 0 _).mul (hf 1 _)).mul (hf 2 _)).mul_const _
  exact le_of_tendsto' hlim.norm hfbound
end Auto
