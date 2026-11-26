-- Prove2me | solution 1 for Arxivcond_mat_0004049.gaussVec_ae_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T14:38:33.813024+00:00
-- url     : https://prove2.me/submissions/7729c7da-341a-438a-875e-9c46e65f22bc

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory ProbabilityTheory Set

namespace Arxivcond_mat_0004049

private lemma gaussVec_measurable_map (N : ℕ) :
    Measurable (fun (x : Fin N → ℝ × ℝ) (i : Fin N) => Complex.measurableEquivRealProd.symm (x i)) :=
  measurable_pi_lambda _ fun i => Complex.measurableEquivRealProd.symm.measurable.comp
    (measurable_pi_apply i)

/-- The Gaussian vector has no atom at `0`: one coordinate already lands on `(0, 0)` with
probability zero. -/
private lemma gaussVec_zero (N : ℕ) (hN : 1 ≤ N) : gaussVec N {0} = 0 := by
  rw [gaussVec, Measure.map_apply (gaussVec_measurable_map N) (measurableSet_singleton 0)]
  refine measure_mono_null (t := Set.pi univ fun _ => {((0 : ℝ), (0 : ℝ))}) ?_ ?_
  · intro x hx i _
    have := congrFun hx i
    simp only [Pi.zero_apply] at this
    have h2 := congrArg Complex.measurableEquivRealProd this
    simpa using h2
  · rw [Measure.pi_pi]
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨0, by omega⟩) ?_
    have hv : ((N : NNReal)⁻¹ / 2) ≠ 0 :=
      div_ne_zero (inv_ne_zero (by exact_mod_cast (show N ≠ 0 by omega))) two_ne_zero
    rw [← Set.singleton_prod_singleton, Measure.prod_prod,
      gaussianReal_absolutelyContinuous 0 hv Real.volume_singleton, zero_mul]

end Arxivcond_mat_0004049

theorem solution (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ g ∂(Arxivcond_mat_0004049.gaussVec N), g ≠ 0 :=
  measure_eq_zero_iff_ae_notMem.1 (Arxivcond_mat_0004049.gaussVec_zero N hN) |>.mono
    fun _ h => h
