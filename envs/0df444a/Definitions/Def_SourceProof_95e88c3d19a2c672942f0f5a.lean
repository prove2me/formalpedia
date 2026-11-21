-- Prove2me | Definitions.Def_SourceProof_95e88c3d19a2c672942f0f5a
-- name    : SourceProof_95e88c3d19a2c672942f0f5a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:15:12.240017+00:00
-- url     : https://prove2.me/theorems/5e97a0da-5de1-44e6-9812-745c0f97d5e7
-- title:
--   LevyStochCalc source module: SourceProof_95e88c3d19a2c672942f0f5a
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.markSumProcess_L2_eq` comes from the `LevyStochCalc.Poisson.CompensatedDensityMarkSum` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkSum_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mark-sum process and its `L²` isometry

The process `∑ᵢ ∑ₖ ξᵢₖ Ñ((tᵢ, tᵢ₊₁] × Bₖ)` attached to adapted bounded coefficients, its second
moment as the `L²(P ⊗ ds ⊗ ν)` energy of the associated integrand, and the isometry for the
difference of two such processes. The energy is computed from the product form of the reference
intensity on time-mark boxes; completeness of `L²(P)` then turns a Cauchy sequence of such
processes into a limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_95e88c3d19a2c672942f0f5a
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {N₀ K : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ : Fin N₀ → Fin K → Ω → ℝ)
    (hξb : ∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) (hξm : ∀ i k, Measurable (ξ i k)) :
    ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, ξ i k ω * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2
        ∂volume ∂ν) ∂P
      = ∑ i : Fin N₀, ∑ k : Fin K, ∑ k' : Fin K,
        (LevyStochCalc.Poisson.referenceIntensity ν
          (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ (B k ∩ B k'))).toReal
        * ∫ ω, ξ i k ω * ξ i k' ω ∂P := by
  have hpnn : ∀ j : Fin (N₀ + 1), 0 ≤ p j := fun j => by
    have := hpmono.monotone (Fin.zero_le j); rwa [hp0] at this
  have hle : ∀ i : Fin N₀, p i.castSucc ≤ p i.succ := fun i => (hpmono Fin.castSucc_lt_succ).le
  have hinterf : ∀ k k', ν (B k ∩ B k') ≠ ⊤ :=
    fun k k' => ne_top_of_le_ne_top (hBf k) (measure_mono Set.inter_subset_left)
  have hξint : ∀ i k, MeasureTheory.Integrable (ξ i k) P := by
    intro i k; obtain ⟨M, hM⟩ := hξb i k
    exact (MeasureTheory.integrable_const M).mono' (hξm i k).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hM ω))
  have hξξint : ∀ i k k', MeasureTheory.Integrable (fun ω => ξ i k ω * ξ i k' ω) P := by
    intro i k k'; obtain ⟨M, hM⟩ := hξb i k
    exact (hξint i k').bdd_mul (hξm i k).aestronglyMeasurable
      (c := M) (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hM ω))
  -- factorisation `ν̂((pᵢ,pᵢ₊₁]×(Bₖ∩Bₖ')) = (pᵢ₊₁−pᵢ)·ν(Bₖ∩Bₖ')` in `toReal`.
  have hfact : ∀ (i : Fin N₀) (k k' : Fin K), (LevyStochCalc.Poisson.referenceIntensity ν
        (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ (B k ∩ B k'))).toReal
      = (p i.succ - p i.castSucc) * (ν (B k ∩ B k')).toReal := by
    intro i k k'
    rw [LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_eq (hpnn _), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith [hle i])]
  -- replace the `ω`-integrand by its `(s,e)` value.
  rw [show (fun ω => ∫ e, ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, ξ i k ω * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2 ∂volume ∂ν)
      = fun ω => ∑ i : Fin N₀, (p i.succ - p i.castSucc)
          * ∑ k : Fin K, ∑ k' : Fin K,
            ξ i k ω * ξ i k' ω * (ν (B k ∩ B k')).toReal from
    funext (fun ω => LevyStochCalc.Poisson.Compensated.eval_sq_integral p hp0 hpmono hpleT B hBm hBf (fun i k => ξ i k ω))]
  -- pull the finite sums and constants through `E[·]`, then refold via `hfact`.
  rw [MeasureTheory.integral_finsetSum _ (fun i _ =>
    (MeasureTheory.integrable_finsetSum _ (fun k _ =>
      MeasureTheory.integrable_finsetSum _ (fun k' _ =>
        (hξξint i k k').mul_const _))).const_mul _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum _ (fun k _ =>
    MeasureTheory.integrable_finsetSum _ (fun k' _ => (hξξint i k k').mul_const _)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun k' _ => (hξξint i k k').mul_const _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  rw [MeasureTheory.integral_mul_const, hfact i k k']
  ring
end LevyStochCalc.Poisson.Compensated


