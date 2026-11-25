-- Prove2me | solution 1 for Arxiv2009_12420.kirchhoff_integral_1d_fourier_form
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T20:48:43.593096+00:00
-- url     : https://prove2.me/submissions/f3a4fd69-cca4-4af9-909f-c8593a539afa

import Mathlib
import Definitions.Def_Arxiv2009_12420_Basic

open Complex MeasureTheory

open Arxiv2009_12420

theorem solution (k0 h dKx : ℝ) (hk0 : 0 < k0) (hh : 0 < h)
    (C : ℝ → ℝ) (hC : IsNormalizedCorrelation C) (η : ℂ)
    (hint : Integrable (fun x : ℝ => cexp (η ^ 2 * (h : ℂ) ^ 2 * (C x : ℂ)) - 1)) :
    kirchhoffIntegral1D k0 h dKx C η =
      (k0 : ℂ) * ∫ x : ℝ, cexp (-(I * (dKx : ℂ) * (x : ℂ))) *
        (cexp (-(η ^ 2 * (h : ℂ) ^ 2)) * (cexp (η ^ 2 * (h : ℂ) ^ 2 * (C x : ℂ)) - 1)) := by
  set G : ℝ → ℂ := fun x => cexp (η ^ 2 * (h : ℂ) ^ 2 * (C x : ℂ)) - 1 with hGdef
  set E : ℂ := cexp (-(η ^ 2 * (h : ℂ) ^ 2)) with hEdef
  set f : ℝ → ℂ := fun x => cexp (-(I * (dKx : ℂ) * (x : ℂ))) * G x with hfdef
  have hGeven : ∀ x, G (-x) = G x := by
    intro x
    simp only [hGdef, hC.2.1 x]
  have hf : Integrable f := by
    refine Integrable.mono hint ?_ (ae_of_all _ (fun x => le_of_eq ?_))
    · exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hint.aestronglyMeasurable
    · simp only [hfdef, norm_mul, Complex.norm_exp]
      simp
  -- Fourier integral of the even function over ℝ equals twice the cosine integral on (0, ∞)
  have hsplit : ∫ x, f x = 2 * ∫ x in Set.Ioi (0 : ℝ), (Real.cos (dKx * x) : ℂ) * G x := by
    calc ∫ x, f x = ∫ x in Set.Iic (0 : ℝ) ∪ Set.Ioi 0, f x := by
          rw [Set.Iic_union_Ioi, Measure.restrict_univ]
      _ = (∫ x in Set.Iic (0 : ℝ), f x) + ∫ x in Set.Ioi 0, f x :=
          setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
            hf.integrableOn hf.integrableOn
      _ = (∫ x in Set.Ioi (0 : ℝ), f (-x)) + ∫ x in Set.Ioi 0, f x := by
          rw [integral_comp_neg_Ioi, neg_zero]
      _ = ∫ x in Set.Ioi (0 : ℝ), (f (-x) + f x) :=
          (integral_add hf.comp_neg.integrableOn hf.integrableOn).symm
      _ = ∫ x in Set.Ioi (0 : ℝ), 2 * ((Real.cos (dKx * x) : ℂ) * G x) := by
          refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
          have e1 : cexp (-(I * (dKx : ℂ) * ((-x : ℝ) : ℂ))) = cexp (((dKx * x : ℝ) : ℂ) * I) := by
            congr 1; push_cast; ring
          have e2 : cexp (-(I * (dKx : ℂ) * (x : ℂ))) = cexp (-((dKx * x : ℝ) : ℂ) * I) := by
            congr 1; push_cast; ring
          simp only [hfdef]
          rw [e1, e2, hGeven, Complex.ofReal_cos, Complex.cos]
          ring
      _ = 2 * ∫ x in Set.Ioi (0 : ℝ), (Real.cos (dKx * x) : ℂ) * G x := integral_const_mul _ _
  -- change of variables u = k0 x on (0, ∞)
  have hcv : ∫ u in Set.Ioi (0 : ℝ),
      (Real.cos (dKx * u / k0) : ℂ) * (cexp (η ^ 2 * (h : ℂ) ^ 2 * (C (u / k0) : ℂ)) - 1)
      = (k0 : ℂ) * ∫ x in Set.Ioi (0 : ℝ), (Real.cos (dKx * x) : ℂ) * G x := by
    have key := integral_comp_mul_left_Ioi
      (fun x => (Real.cos (dKx * x) : ℂ) * G x) 0 (inv_pos.mpr hk0)
    simp only [mul_zero, inv_inv] at key
    rw [Complex.real_smul] at key
    rw [← key]
    congr 1
    funext u
    simp only [hGdef]
    rw [show dKx * u / k0 = dKx * (k0⁻¹ * u) by ring, show u / k0 = k0⁻¹ * u by ring]
  have hrhs : ∫ x : ℝ, cexp (-(I * (dKx : ℂ) * (x : ℂ))) * (E * G x) = E * ∫ x, f x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [hfdef]
    ring
  unfold kirchhoffIntegral1D
  rw [hcv, hrhs, hsplit]
  ring
