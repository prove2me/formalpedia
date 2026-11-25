-- Prove2me | solution 1 for Arxiv1809_10262.generator_loss_as_regularized_inversion
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T20:51:41.144374+00:00
-- url     : https://prove2.me/submissions/ed12932e-ea79-48ab-a75c-712be29ca1ca

import Mathlib
import Definitions.Def_Arxiv1809_10262_Basic

open MeasureTheory
open Arxiv1809_10262

lemma sg_eq {Dat : Type*} [MeasurableSpace Dat]
    {w h N : ℕ} (hw : 0 < w) (hh : 0 < h) (hN : 0 < N)
    (lam1 lam2 : ℝ) (μ : Measure Dat) (D : VelocityMap w h → ℝ)
    (m : Fin N → VelocityMap w h) (d : Fin N → Dat) (g : Dat → VelocityMap w h) :
    meanGeneratorLoss lam1 lam2 μ D m d g =
      regularizedInversionObjective (lam1 / ((N : ℝ) * w * h)) (lam2 / ((N : ℝ) * w * h))
        μ D m d g := by
  have h1 : ∀ k, l1Norm (m k - g (d k)) = ∑ i, ∑ j, |g (d k) i j - m k i j| := by
    intro k; simp only [l1Norm, Pi.sub_apply, abs_sub_comm]
  have h2 : ∀ k, sqL2Norm (m k - g (d k)) = ∑ i, ∑ j, (g (d k) i j - m k i j) ^ 2 := by
    intro k; simp only [sqL2Norm, Pi.sub_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [meanGeneratorLoss, generatorLoss, regularizedInversionObjective, h1, h2,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum]
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hw' : (w : ℝ) ≠ 0 := by positivity
  have hh' : (h : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem solution {Dat : Type*} [MeasurableSpace Dat]
    {w h N : ℕ} (hw : 0 < w) (hh : 0 < h) (hN : 0 < N)
    (lam1 lam2 : ℝ) (hlam1 : 0 < lam1) (hlam2 : 0 < lam2)
    (μ : Measure Dat) [IsProbabilityMeasure μ] (D : VelocityMap w h → ℝ)
    (m : Fin N → VelocityMap w h) (d : Fin N → Dat)
    (G : Set (Dat → VelocityMap w h))
    (hG : ∀ g ∈ G, Measurable g ∧ Integrable D (generatedLaw μ g)) :
    (∀ g ∈ G, meanGeneratorLoss lam1 lam2 μ D m d g =
      regularizedInversionObjective (lam1 / ((N : ℝ) * w * h)) (lam2 / ((N : ℝ) * w * h))
        μ D m d g) ∧
    {g | g ∈ G ∧ IsMinOn (meanGeneratorLoss lam1 lam2 μ D m d) G g} =
      {g | g ∈ G ∧ IsMinOn (regularizedInversionObjective (lam1 / ((N : ℝ) * w * h))
        (lam2 / ((N : ℝ) * w * h)) μ D m d) G g} := by
  have hf : meanGeneratorLoss lam1 lam2 μ D m d =
      regularizedInversionObjective (lam1 / ((N : ℝ) * w * h)) (lam2 / ((N : ℝ) * w * h))
        μ D m d := funext fun g => sg_eq hw hh hN lam1 lam2 μ D m d g
  exact ⟨fun g _ => congrFun hf g, by rw [hf]⟩

