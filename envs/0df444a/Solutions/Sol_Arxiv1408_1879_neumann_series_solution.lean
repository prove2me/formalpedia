-- Prove2me | solution 1 for Arxiv1408_1879.neumann_series_solution
-- status  : ACCEPTED   (prove)
-- author  : @ytako6706
-- created : 2026-11-25T09:56:55.844243+00:00
-- url     : https://prove2.me/submissions/2743b978-3b84-406b-b3ab-a1dee13cdd29

import Mathlib
import Definitions.Def_Arxiv1408_1879_Basic

open MeasureTheory Filter Topology
open Arxiv1408_1879

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (L : E ≃L[ℂ] E) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (R : E →L[ℂ] E) (ψi : E),
      (∀ n : ℕ, ‖R (seriesTerm L R ψi n)‖ ≤ δ * ‖seriesTerm L R ψi n‖) →
      ∃ u : E, HasSum (fun n : ℕ => (-1 : ℂ) ^ n • seriesTerm L R ψi n) u ∧
        (L : E →L[ℂ] E) u + R u = ψi := by
  set K : ℝ := ‖(L.symm : E →L[ℂ] E)‖ with hK
  have hK0 : 0 ≤ K := norm_nonneg _
  refine ⟨1 / (2 * (K + 1)), by positivity, fun R ψi hR => ?_⟩
  set t := seriesTerm L R ψi with ht
  have hsucc : ∀ n, t (n + 1) = L.symm (R (t n)) := by
    intro n
    simp only [ht, seriesTerm, pow_succ']
    rfl
  have hstep : ∀ n, ‖t (n + 1)‖ ≤ (1 / 2) * ‖t n‖ := by
    intro n
    rw [hsucc]
    calc ‖L.symm (R (t n))‖ = ‖(L.symm : E →L[ℂ] E) (R (t n))‖ := rfl
      _ ≤ K * ‖R (t n)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * (1 / (2 * (K + 1)) * ‖t n‖) := mul_le_mul_of_nonneg_left (hR n) hK0
      _ ≤ (1 / 2) * ‖t n‖ := by
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [mul_one_div, div_le_iff₀ (by positivity)]
          nlinarith
  have hgeom : ∀ n, ‖t n‖ ≤ ‖t 0‖ * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc ‖t (n + 1)‖ ≤ (1 / 2) * ‖t n‖ := hstep n
        _ ≤ (1 / 2) * (‖t 0‖ * (1 / 2) ^ n) := by gcongr
        _ = ‖t 0‖ * (1 / 2) ^ (n + 1) := by ring
  set f : ℕ → E := fun n => (-1 : ℂ) ^ n • t n with hf
  have hfs : Summable f := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (r := 1 / 2) (by norm_num) (by norm_num)).mul_left ‖t 0‖) fun n => ?_
    rw [hf]; simp only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact hgeom n
  set u := ∑' n, f n with hu
  have hus : HasSum f u := hfs.hasSum
  refine ⟨u, hus, ?_⟩
  -- `L⁻¹ R u = ∑ (-1)^n t (n+1)`
  have h1 : HasSum (fun n => (-1 : ℂ) ^ n • t (n + 1))
      (((L.symm : E →L[ℂ] E).comp R) u) := by
    have := hus.mapL ((L.symm : E →L[ℂ] E).comp R)
    convert this using 1
    funext n
    simp only [hf, map_smul, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      hsucc]
  -- tail of the series defining `u`
  have h2 : HasSum (fun n => f (n + 1)) (u - t 0) := by
    have := (hasSum_nat_add_iff' 1).mpr hus
    simpa [hf] using this
  have h3 : HasSum (fun n => (-1 : ℂ) ^ n • t (n + 1)) (t 0 - u) := by
    have := h2.neg
    convert this using 1
    · funext n; simp [hf, pow_succ]
    · abel
  have hkey : L.symm (R u) = t 0 - u := by
    have := h1.unique h3
    simpa using this
  have ht0 : t 0 = L.symm ψi := by simp [ht, seriesTerm]
  have : L.symm (L u + R u) = L.symm ψi := by
    rw [map_add, hkey, ht0]; simp
  have := congrArg L this
  simpa using this
