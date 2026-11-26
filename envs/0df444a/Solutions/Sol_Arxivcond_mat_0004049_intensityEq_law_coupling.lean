-- Prove2me | solution 1 for Arxivcond_mat_0004049.intensityEq_law_coupling
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T15:32:56.172851+00:00
-- url     : https://prove2.me/submissions/7bf02120-8548-4415-bd21-cd914e2ee8e0

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic
import Theorems.Thm_Arxivcond_mat_0004049_laguerreEnsemble_isProbabilityMeasure

open MeasureTheory ProbabilityTheory

namespace Arxivcond_mat_0004049

/-- `|∑ (g_i/‖g‖)²|² = |∑ g_i²|² / ‖g‖⁴` (both sides `0` when `g = 0`). -/
private lemma normSq_sum_sq_unit {N : ℕ} (g : Fin N → ℂ) :
    Complex.normSq (∑ i, (g i / ((Real.sqrt (∑ j, Complex.normSq (g j)) : ℝ) : ℂ)) ^ 2) =
      Complex.normSq (∑ i, g i ^ 2) / (∑ j, Complex.normSq (g j)) ^ 2 := by
  have hS : 0 ≤ ∑ j, Complex.normSq (g j) := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  simp_rw [div_pow, ← Complex.ofReal_pow, Real.sq_sqrt hS, ← Finset.sum_div, Complex.normSq_div,
    Complex.normSq_ofReal]
  ring

private theorem coupling_aux (γ : ℝ) (hγ : 0 < γ) (N : ℕ) (hN : 1 ≤ N) :
    (localizedModel N γ).map (fun ω => (N : ℝ) * intensityEq ω) =
      (Measure.infinitePi fun _ : ℕ => ((gaussianReal 0 (1 / 2)).prod
          (gaussianReal 0 (1 / 2))).map Complex.measurableEquivRealProd.symm).map
        (fun z => Complex.normSq (((Real.sqrt N)⁻¹ : ℂ) * ∑ k ∈ Finset.range N, z k ^ 2) /
          ((∑ k ∈ Finset.range N, Complex.normSq (z k)) / N) ^ 2) := by
  set ν₁ : Measure ℂ := ((gaussianReal 0 (1 / 2)).prod
    (gaussianReal 0 (1 / 2))).map Complex.measurableEquivRealProd.symm with hν₁
  have hν₁P : IsProbabilityMeasure ν₁ := Measure.isProbabilityMeasure_map (by fun_prop)
  set c : ℝ := (Real.sqrt N)⁻¹ with hc
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hc2 : c ^ 2 = (N : ℝ)⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  set Φ : (Fin N → ℂ) → ℝ := fun g =>
    (N : ℝ) * (Complex.normSq (∑ i, g i ^ 2) / (∑ j, Complex.normSq (g j)) ^ 2) with hΦ
  have hΦm : Measurable Φ := by fun_prop
  -- step 2: gaussVec is a scaled product of standard circular Gaussians
  have hscale : ν₁.map (fun z : ℂ => (c : ℂ) * z) =
      ((gaussianReal 0 ((N : NNReal)⁻¹ / 2)).prod (gaussianReal 0 ((N : NNReal)⁻¹ / 2))).map
        Complex.measurableEquivRealProd.symm := by
    rw [hν₁, Measure.map_map (by fun_prop) (by fun_prop)]
    have hcomp : (fun z : ℂ => (c : ℂ) * z) ∘ Complex.measurableEquivRealProd.symm =
        Complex.measurableEquivRealProd.symm ∘ Prod.map (fun x => c * x) (fun x => c * x) := by
      funext p
      apply Complex.ext <;> simp [Complex.measurableEquivRealProd]
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      mul_zero]
    have hv : ∀ h : 0 ≤ c ^ 2, NNReal.mk (c ^ 2) h * (1 / 2 : NNReal) =
        ((N : NNReal)⁻¹ / 2 : NNReal) := by
      intro h; ext; push_cast; rw [hc2]; ring
    simp only [hv]
  have hgv : gaussVec N = (Measure.pi fun _ : Fin N => ν₁).map (fun z i => (c : ℂ) * z i) := by
    rw [gaussVec, Measure.pi_map_pi (fun _ => by fun_prop),
      Measure.pi_map_pi (f := fun _ z => (c : ℂ) * z) (fun _ => by fun_prop), hscale]
  -- step 1: only `g` matters
  have hG : IsProbabilityMeasure (gaussVec N) := by
    rw [hgv]
    exact Measure.isProbabilityMeasure_map
      (measurable_pi_lambda _ fun i => measurable_const.mul (measurable_pi_apply i)).aemeasurable
  have hL := laguerreEnsemble_isProbabilityMeasure N γ hγ
  have h1 : (localizedModel N γ).map (fun ω => (N : ℝ) * intensityEq ω) =
      (gaussVec N).map Φ := by
    have hf : (fun ω : Sample N => (N : ℝ) * intensityEq ω) = Φ ∘ Prod.fst := by
      funext ω
      simp only [Function.comp_apply, hΦ, intensityEq, ampC, uVec, pow_zero, one_mul,
        normSq_sum_sq_unit]
    rw [hf, ← Measure.map_map hΦm measurable_fst, localizedModel, Measure.map_fst_prod,
      measure_univ, one_smul]
  -- step 3: the first `N` coordinates of the infinite product
  have hrestr : (Measure.infinitePi fun _ : ℕ => ν₁).map (fun z (i : Fin N) => z i) =
      Measure.pi fun _ : Fin N => ν₁ := by
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
  -- step 4: pointwise algebra
  have hpt : ∀ z : ℕ → ℂ, Φ (fun i : Fin N => (c : ℂ) * z i) =
      Complex.normSq (((Real.sqrt N)⁻¹ : ℂ) * ∑ k ∈ Finset.range N, z k ^ 2) /
          ((∑ k ∈ Finset.range N, Complex.normSq (z k)) / N) ^ 2 := by
    intro z
    simp only [hΦ]
    rw [Fin.sum_univ_eq_sum_range (fun k => ((c : ℂ) * z k) ^ 2),
      Fin.sum_univ_eq_sum_range (fun k => Complex.normSq ((c : ℂ) * z k))]
    simp_rw [mul_pow, ← Finset.mul_sum, Complex.normSq_mul, ← Finset.mul_sum, map_pow]
    have hnc : Complex.normSq (c : ℂ) = (N : ℝ)⁻¹ := by
      rw [Complex.normSq_ofReal, ← sq, hc2]
    have hns : Complex.normSq ((Real.sqrt N : ℂ))⁻¹ = (N : ℝ)⁻¹ := by
      rw [map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    rw [hnc, hns]
    field_simp
  rw [h1, hgv, ← hrestr, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (hΦm.comp (by fun_prop)) (by fun_prop)]
  congr 1
  funext z
  exact hpt z

end Arxivcond_mat_0004049

open Arxivcond_mat_0004049 in
theorem solution (γ : ℝ) (hγ : 0 < γ) (N : ℕ) (hN : 1 ≤ N) :
    (localizedModel N γ).map (fun ω => (N : ℝ) * intensityEq ω) =
      (Measure.infinitePi fun _ : ℕ => ((gaussianReal 0 (1 / 2)).prod
          (gaussianReal 0 (1 / 2))).map Complex.measurableEquivRealProd.symm).map
        (fun z => Complex.normSq (((Real.sqrt N)⁻¹ : ℂ) * ∑ k ∈ Finset.range N, z k ^ 2) /
          ((∑ k ∈ Finset.range N, Complex.normSq (z k)) / N) ^ 2) :=
  coupling_aux γ hγ N hN
