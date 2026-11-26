-- Prove2me | solution 1 for Arxiv2210_03613.ssvgd_noise_coordinate_variance
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T04:19:08.878362+00:00
-- url     : https://prove2.me/submissions/8e87341b-5efc-43a9-b0d9-1445d132bdc2

import Mathlib
import Definitions.Def_Arxiv2210_03613_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory InformationTheory

namespace S77SV
open Arxiv2210_03613 Matrix

lemma psd {n d : ℕ} (k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (m : Fin n → Fin d → ℝ)
    (hK : (gramMat k m).PosDef) : (svgdK k m).PosSemidef := by
  have hG := hK.posSemidef
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hG ⊢
  obtain ⟨hH, hG⟩ := hG
  refine ⟨?_, fun x => ?_⟩
  · ext ⟨i, a⟩ ⟨j, b⟩
    have := congrFun (congrFun hH i) j
    simp only [Matrix.conjTranspose_apply, gramMat, star_trivial] at this
    simp only [Matrix.conjTranspose_apply, svgdK, star_trivial]
    by_cases hab : a = b
    · subst hab; simp [this]
    · simp [hab, Ne.symm hab]
  · have key : ∀ a : Fin d, 0 ≤ ∑ i, x (i, a) * ∑ j, k (m i) (m j) * x (j, a) := by
      intro a
      have := hG (fun i => x (i, a))
      simpa [dotProduct, Matrix.mulVec, gramMat] using this
    have e : star x ⬝ᵥ (svgdK k m *ᵥ x) =
        (1 / (n : ℝ)) * ∑ a, ∑ i, x (i, a) * ∑ j, k (m i) (m j) * x (j, a) := by
      simp only [dotProduct, Matrix.mulVec, svgdK, Fintype.sum_prod_type, star_trivial]
      simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.sum_comm (f := fun i a => x (i, a) * ∑ j, 1 / (n:ℝ) * k (m i) (m j) * x (j, a)),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => key a)

end S77SV

open Arxiv2210_03613 S77SV in
theorem solution {n d : ℕ} (hn : 0 < n)
    (k : (Fin d → ℝ) → (Fin d → ℝ) → ℝ) (m : Fin n → Fin d → ℝ) (hK : (gramMat k m).PosDef)
    (ε : ℝ) (hε : 0 < ε) :
    (∀ (i : Fin n) (a : Fin d),
      variance (fun η : EuclideanSpace ℝ (Fin n × Fin d) => η (i, a)) (ssvgdNoise ε k m) =
        2 * ε * k (m i) (m i) / n) ∧
    (∀ C : ℝ, (∀ x, k x x ≤ C) → ∀ (i : Fin n) (a : Fin d),
      variance (fun η : EuclideanSpace ℝ (Fin n × Fin d) => η (i, a)) (ssvgdNoise ε k m) ≤
        2 * ε * C / n) := by
  have hS : ((2 * ε) • svgdK k m).PosSemidef := (psd k m hK).smul (by positivity)
  have hv : ∀ (i : Fin n) (a : Fin d),
      variance (fun η : EuclideanSpace ℝ (Fin n × Fin d) => η (i, a)) (ssvgdNoise ε k m) =
        2 * ε * k (m i) (m i) / n := by
    intro i a
    unfold ssvgdNoise
    rw [variance_eval_multivariateGaussian hS]
    simp [svgdK]
    ring
  refine ⟨hv, fun C hC i a => ?_⟩
  rw [hv]
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  apply div_le_div_of_nonneg_right _ hn'.le
  have := hC (m i)
  nlinarith
