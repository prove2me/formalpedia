-- Prove2me | solution 1 for Arxivcond_mat_0004049.gaussVec_box_pos
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T14:38:33.860718+00:00
-- url     : https://prove2.me/submissions/55d6e754-d086-48e6-8aa2-f1143887f79d

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology ProbabilityTheory Set

namespace Arxivcond_mat_0004049

private lemma gaussVec_measurable_map (N : ℕ) :
    Measurable (fun (x : Fin N → ℝ × ℝ) (i : Fin N) => Complex.measurableEquivRealProd.symm (x i)) :=
  measurable_pi_lambda _ fun i => Complex.measurableEquivRealProd.symm.measurable.comp
    (measurable_pi_apply i)

/-- The box of detected columns near `conj(u)` has positive Gaussian measure. -/
private lemma gaussVec_box_ne_zero (N : ℕ) (hN : 1 ≤ N) (c : Fin N → ℂ) (δ : ℝ) (hδ : 0 < δ) :
    gaussVec N {v | ∀ j, |(v j - c j).re| < δ ∧ |(v j - c j).im| < δ} ≠ 0 := by
  have hv : ((N : NNReal)⁻¹ / 2) ≠ 0 :=
    div_ne_zero (inv_ne_zero (by exact_mod_cast (show N ≠ 0 by omega))) two_ne_zero
  set box : Set (Fin N → ℝ × ℝ) := Set.pi univ fun j =>
    Ioo ((c j).re - δ) ((c j).re + δ) ×ˢ Ioo ((c j).im - δ) ((c j).im + δ)
  intro h0
  have hle : (Measure.pi fun _ : Fin N =>
      (gaussianReal 0 ((N : NNReal)⁻¹ / 2)).prod (gaussianReal 0 ((N : NNReal)⁻¹ / 2))) box = 0 := by
    refine measure_mono_null ?_ (le_antisymm ((Measure.le_map_apply
      (gaussVec_measurable_map N).aemeasurable _).trans (le_of_eq h0)) bot_le)
    intro x hx j
    have := Set.mem_univ_pi.1 hx j
    simp only [mem_prod, mem_Ioo] at this
    simp only [Complex.measurableEquivRealProd_symm_apply, Complex.sub_re,
      Complex.sub_im]
    constructor <;> rw [abs_lt] <;> constructor <;> linarith [this.1.1, this.1.2, this.2.1, this.2.2]
  rw [Measure.pi_pi, Finset.prod_eq_zero_iff] at hle
  obtain ⟨j, _, hj⟩ := hle
  rw [Measure.prod_prod, mul_eq_zero] at hj
  have hIoo : ∀ a : ℝ, gaussianReal 0 ((N : NNReal)⁻¹ / 2) (Ioo (a - δ) (a + δ)) ≠ 0 := by
    intro a ha
    have := gaussianReal_absolutelyContinuous' 0 hv ha
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at this
    linarith
  rcases hj with hj | hj
  · exact hIoo _ hj
  · exact hIoo _ hj

end Arxivcond_mat_0004049

open Arxivcond_mat_0004049 in
theorem solution (N : ℕ) (hN : 1 ≤ N) (c : Fin N → ℂ) (δ : ℝ) (hδ : 0 < δ) :
    gaussVec N {v | ∀ j, |(v j - c j).re| < δ ∧ |(v j - c j).im| < δ} ≠ 0 :=
  gaussVec_box_ne_zero N hN c δ hδ
