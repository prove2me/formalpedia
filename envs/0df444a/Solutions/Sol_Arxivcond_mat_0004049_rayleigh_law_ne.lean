-- Prove2me | solution 1 for Arxivcond_mat_0004049.rayleigh_law_ne
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T15:18:23.760206+00:00
-- url     : https://prove2.me/submissions/d5b0ebbc-1040-489a-8216-4dc57db38ee8

import Theorems.Thm_MathlibGap_gaussianReal_prod_map_sq_add_sq
import Theorems.Thm_Arxivcond_mat_0004049_gaussVec_map_sum_mul
import Theorems.Thm_Arxivcond_mat_0004049_gaussVec_isProbabilityMeasure
import Theorems.Thm_Arxivcond_mat_0004049_gaussVec_ae_ne_zero
import Theorems.Thm_Arxivcond_mat_0004049_laguerreEnsemble_isProbabilityMeasure

open MeasureTheory ProbabilityTheory Set

namespace Arxivcond_mat_0004049

/-- `I = |A₀|²` depends only on `(g, v)`: `A₀ = ∑ u_i v_i` with `u = g/‖g‖₂`. -/
private lemma intensityNe_eq {N : ℕ} (ω : Sample N) :
    intensityNe ω = Complex.normSq (∑ i, (ω.1 i / ((Real.sqrt (∑ j, Complex.normSq (ω.1 j)) : ℝ) : ℂ)) * ω.2.1 i) := by
  simp only [intensityNe, ampA, pow_zero, one_mul, uVec, vVec]

private lemma unit_of_ne_zero {N : ℕ} (g : Fin N → ℂ) (hg : g ≠ 0) :
    ∑ i, Complex.normSq (g i / ((Real.sqrt (∑ j, Complex.normSq (g j)) : ℝ) : ℂ)) = 1 := by
  have hS : (∑ j, Complex.normSq (g j)) ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, g i ≠ 0 := by
      by_contra h; push Not at h; exact hg (funext h)
    exact (lt_of_lt_of_le (Complex.normSq_pos.2 hi) (Finset.single_le_sum
      (f := fun j => Complex.normSq (g j)) (fun j _ => Complex.normSq_nonneg _)
      (Finset.mem_univ i))).ne'
  simp_rw [map_div₀, Complex.normSq_ofReal,
    Real.mul_self_sqrt (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (g j))]
  rw [← Finset.sum_div, div_self hS]

private theorem rayleigh_law_ne_aux (γ : ℝ) (hγ : 0 < γ) (N : ℕ) (hN : 1 ≤ N) :
    (localizedModel N γ).map intensityNe =
      (volume : Measure ℝ).withDensity
        (fun I => ENNReal.ofReal (if 0 < I then (N : ℝ) * Real.exp (-(N : ℝ) * I) else 0)) := by
  have hG := gaussVec_isProbabilityMeasure N
  have hL := laguerreEnsemble_isProbabilityMeasure N γ hγ
  have hv : ((N : NNReal)⁻¹ / 2) ≠ 0 :=
    div_ne_zero (inv_ne_zero (by exact_mod_cast (show N ≠ 0 by omega))) two_ne_zero
  have hI : Measurable (intensityNe : Sample N → ℝ) := by
    unfold intensityNe ampA uVec vVec tau; fun_prop
  -- step 1: the law of `I` is the law of `|Z|²` for the circular Gaussian `Z`
  have h1 : (localizedModel N γ).map intensityNe =
      (((gaussianReal 0 ((N : NNReal)⁻¹ / 2)).prod (gaussianReal 0 ((N : NNReal)⁻¹ / 2))).map Complex.measurableEquivRealProd.symm).map Complex.normSq := by
    ext S hS
    have hSn : MeasurableSet (Complex.normSq ⁻¹' S) := Complex.continuous_normSq.measurable hS
    rw [Measure.map_apply hI hS, Measure.map_apply Complex.continuous_normSq.measurable hS]
    unfold localizedModel
    rw [Measure.prod_apply (hI hS)]
    have hae : ∀ᵐ g ∂(gaussVec N), ((gaussVec N).prod (laguerreEnsemble N γ))
        (Prod.mk g ⁻¹' (intensityNe ⁻¹' S)) =
        (((gaussianReal 0 ((N : NNReal)⁻¹ / 2)).prod (gaussianReal 0 ((N : NNReal)⁻¹ / 2))).map
          Complex.measurableEquivRealProd.symm) (Complex.normSq ⁻¹' S) := by
      filter_upwards [gaussVec_ae_ne_zero N hN] with g hg
      have hset : Prod.mk g ⁻¹' (intensityNe ⁻¹' S) =
          ((fun v : Fin N → ℂ => ∑ i, (g i / ((Real.sqrt (∑ j, Complex.normSq (g j)) : ℝ) : ℂ)) * v i)
            ⁻¹' (Complex.normSq ⁻¹' S)) ×ˢ (univ : Set (Fin N → ℝ)) := by
        ext ⟨v, μ⟩; simp [intensityNe_eq]
      rw [hset, Measure.prod_prod, measure_univ, mul_one, ← Measure.map_apply (by fun_prop) hSn,
        gaussVec_map_sum_mul N _ (unit_of_ne_zero g hg)]
    rw [lintegral_congr_ae hae, lintegral_const, measure_univ, mul_one]
  -- step 2: `|x + iy|² = x² + y²`
  have h2 : (((gaussianReal 0 ((N : NNReal)⁻¹ / 2)).prod (gaussianReal 0 ((N : NNReal)⁻¹ / 2))).map Complex.measurableEquivRealProd.symm).map Complex.normSq =
      ((gaussianReal 0 ((N : NNReal)⁻¹ / 2)).prod (gaussianReal 0 ((N : NNReal)⁻¹ / 2))).map (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) := by
    rw [Measure.map_map Complex.continuous_normSq.measurable
      Complex.measurableEquivRealProd.symm.measurable]
    congr 1
    funext p
    simp [Complex.normSq_apply, Complex.measurableEquivRealProd_symm_apply, sq]
  rw [h1, h2, MathlibGap.gaussianReal_prod_map_sq_add_sq _ hv]
  -- step 3: the rate `1/(2v)` is `N`
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hrate : (2 * (((N : NNReal)⁻¹ / 2 : NNReal) : ℝ))⁻¹ = N := by
    push_cast; field_simp
  congr 1
  funext x
  rw [hrate]

end Arxivcond_mat_0004049

open Arxivcond_mat_0004049 in
theorem solution (γ : ℝ) (hγ : 0 < γ) :
    ∀ N : ℕ, 1 ≤ N → (localizedModel N γ).map intensityNe =
      (volume : Measure ℝ).withDensity
        (fun I => ENNReal.ofReal (if 0 < I then (N : ℝ) * Real.exp (-(N : ℝ) * I) else 0)) :=
  fun N hN => rayleigh_law_ne_aux γ hγ N hN
