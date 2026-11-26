-- Prove2me | solution 1 for Arxivcond_mat_0004049.gaussVec_map_sum_mul
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T15:16:53.381242+00:00
-- url     : https://prove2.me/submissions/5a9c1843-c474-4d90-b28d-1fccd697e38b

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory ProbabilityTheory Complex

open scoped ComplexConjugate RealInnerProductSpace

theorem solution (N : ℕ) (u : Fin N → ℂ) (hu : ∑ i, Complex.normSq (u i) = 1) :
    (Arxivcond_mat_0004049.gaussVec N).map (fun v => ∑ i, u i * v i) =
      ((gaussianReal 0 ((N : NNReal)⁻¹ / 2)).prod (gaussianReal 0 ((N : NNReal)⁻¹ / 2))).map
        Complex.measurableEquivRealProd.symm := by
  set s : NNReal := (N : NNReal)⁻¹ / 2 with hs
  set ν : Measure ℂ := ((gaussianReal 0 s).prod (gaussianReal 0 s)).map
    Complex.measurableEquivRealProd.symm with hν
  have hνP : IsProbabilityMeasure ν := by
    rw [hν]; exact Measure.isProbabilityMeasure_map (by fun_prop)
  -- characteristic function of the circular Gaussian
  have hcf : ∀ w : ℂ, charFun ν w = cexp (-((s : ℝ) * ‖w‖ ^ 2 / 2 : ℝ)) := by
    intro w
    rw [charFun_apply, hν, integral_map_equiv]
    have hin : ∀ p : ℝ × ℝ, cexp (((⟪Complex.measurableEquivRealProd.symm p, w⟫ : ℝ) : ℂ) * I)
        = cexp ((w.re : ℂ) * p.1 * I) * cexp ((w.im : ℂ) * p.2 * I) := by
      intro p
      rw [← Complex.exp_add, Complex.inner]
      congr 1
      simp [Complex.measurableEquivRealProd]
      ring
    simp_rw [hin]
    rw [integral_prod_mul (fun x : ℝ => cexp ((w.re : ℂ) * x * I))
      (fun y : ℝ => cexp ((w.im : ℂ) * y * I))]
    rw [← charFun_apply_real, ← charFun_apply_real, charFun_gaussianReal, charFun_gaussianReal,
      ← Complex.exp_add]
    congr 1
    rw [Complex.sq_norm, Complex.normSq_apply]
    push_cast
    ring
  -- gaussVec is the product of copies of ν
  have hpi : Arxivcond_mat_0004049.gaussVec N = Measure.pi (fun _ : Fin N => ν) := by
    rw [Arxivcond_mat_0004049.gaussVec, Measure.pi_map_pi (fun _ => by fun_prop)]
  -- the pushforward is the law of a sum of independent coordinates
  have hmap : (Measure.pi (fun _ : Fin N => ν)).map (fun v => ∑ i, u i * v i) =
      (Measure.pi (fun i : Fin N => ν.map (fun z => u i * z))).map (fun p => ∑ i, p i) := by
    rw [← Measure.pi_map_pi (f := fun i z => u i * z) (fun _ => by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hcfu : ∀ (i : Fin N) (t : ℂ), charFun (ν.map (fun z => u i * z)) t
      = cexp (-((s : ℝ) * Complex.normSq (u i) * ‖t‖ ^ 2 / 2 : ℝ)) := by
    intro i t
    have h1 : charFun (ν.map (fun z => u i * z)) t = charFun ν (conj (u i) * t) := by
      rw [charFun_apply, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
      congr 1
      ext z
      rw [Complex.inner, Complex.inner]
      congr 3
      simp only [map_mul]
      ring
    rw [h1, hcf]
    congr 3
    rw [norm_mul, mul_pow, Complex.norm_conj, Complex.sq_norm]
    ring
  have : IsProbabilityMeasure ((Arxivcond_mat_0004049.gaussVec N).map
      (fun v => ∑ i, u i * v i)) := by
    rw [hpi]
    exact Measure.isProbabilityMeasure_map
      (Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)).aemeasurable
  have hPu : ∀ i : Fin N, IsProbabilityMeasure (ν.map (fun z => u i * z)) := fun i =>
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply Measure.ext_of_charFun
  ext t
  rw [hpi, hmap, charFun_map_sum_pi_eq_prod, hcf, Finset.prod_apply]
  simp_rw [hcfu]
  rw [← Complex.exp_sum]
  congr 1
  have key : ∑ i, -((s : ℝ) * Complex.normSq (u i) * ‖t‖ ^ 2 / 2) = -((s : ℝ) * ‖t‖ ^ 2 / 2) := by
    rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.sum_mul, ← Finset.mul_sum, hu, mul_one]
  exact_mod_cast key
