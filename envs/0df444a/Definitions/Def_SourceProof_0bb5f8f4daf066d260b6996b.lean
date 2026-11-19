-- Prove2me | Definitions.Def_SourceProof_0bb5f8f4daf066d260b6996b
-- name    : SourceProof_0bb5f8f4daf066d260b6996b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:04:43.611165+00:00
-- url     : https://prove2.me/theorems/9ce649c3-a3fa-428b-be02-4ebf294139c4
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.indep_comap_of_tendsto_ae
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_IndepLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Independence survives almost-everywhere limits

If each random variable `X n` is independent of a σ-algebra `m` and `X n → Y` almost
everywhere, then `Y` is independent of `m`: for a set `A ∈ m` the laws of `Y` under `P|_A` and
under `P(A) • P` have the same integrals against bounded continuous functions, by dominated
convergence, hence coincide.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

namespace LevyStochCalc.Probability

variable {Ω 𝓧 : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [TopologicalSpace 𝓧] [MeasurableSpace 𝓧] [BorelSpace 𝓧] [HasOuterApproxClosed 𝓧]


theorem _root_.Prove2MeSourceProof.h_0bb5f8f4daf066d260b6996b (hm : m ≤ mΩ) {X : ℕ → Ω → 𝓧}
    {Y : Ω → 𝓧} (hX : ∀ n, Measurable[mΩ] (X n)) (hY : Measurable[mΩ] Y)
    (hind : ∀ n, Indep m (MeasurableSpace.comap (X n) inferInstance) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Indep m (MeasurableSpace.comap Y inferInstance) P := by
  rw [Indep_iff]
  intro A B hA hB
  obtain ⟨S, hS, rfl⟩ := hB
  have hA' : MeasurableSet[mΩ] A := hm _ hA
  haveI : IsFiniteMeasure ((P A) • P.map Y) :=
    ⟨by simpa [Measure.smul_apply] using
      ENNReal.mul_lt_top (measure_lt_top P A) (measure_lt_top (P.map Y) Set.univ)⟩
  have hbound : ∀ (Z : Ω → 𝓧), Measurable[mΩ] Z → ∀ f : 𝓧 →ᵇ ℝ,
      Integrable (fun ω => f (Z ω)) P := fun Z hZ f =>
    Integrable.of_bound (f.continuous.measurable.comp hZ).aestronglyMeasurable ‖f‖
      (ae_of_all _ fun ω => f.norm_coe_le_norm _)
  have hμ : (P.restrict A).map Y = (P A) • P.map Y := by
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    rw [integral_map hY.aemeasurable f.continuous.aestronglyMeasurable,
      integral_smul_measure, integral_map hY.aemeasurable f.continuous.aestronglyMeasurable,
      smul_eq_mul]
    have hL : Tendsto (fun n => ∫ ω in A, f (X n ω) ∂P) atTop (𝓝 (∫ ω in A, f (Y ω) ∂P)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
        (fun n => (f.continuous.measurable.comp (hX n)).aestronglyMeasurable)
        (integrable_const _) (fun n => ae_of_all _ fun ω => f.norm_coe_le_norm _) ?_
      exact ae_restrict_of_ae (hlim.mono fun ω hω => (f.continuous.tendsto _).comp hω)
    have hR : Tendsto (fun n => (P A).toReal * ∫ ω, f (X n ω) ∂P) atTop
        (𝓝 ((P A).toReal * ∫ ω, f (Y ω) ∂P)) := by
      refine Tendsto.const_mul _ ?_
      refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
        (fun n => (f.continuous.measurable.comp (hX n)).aestronglyMeasurable)
        (integrable_const _) (fun n => ae_of_all _ fun ω => f.norm_coe_le_norm _) ?_
      exact hlim.mono fun ω hω => (f.continuous.tendsto _).comp hω
    have heq : ∀ n, ∫ ω in A, f (X n ω) ∂P = (P A).toReal * ∫ ω, f (X n ω) ∂P := fun n =>
      LevyStochCalc.Probability.setIntegral_eq_measure_mul_of_indep hm (hX n) (hind n) hA f
    simp_rw [heq] at hL
    exact tendsto_nhds_unique hL hR
  have h1 : ((P.restrict A).map Y) S = P (A ∩ Y ⁻¹' S) := by
    rw [Measure.map_apply hY hS, Measure.restrict_apply (hY hS), Set.inter_comm]
  have h2 : ((P A) • P.map Y) S = P A * P (Y ⁻¹' S) := by
    rw [Measure.smul_apply, Measure.map_apply hY hS, smul_eq_mul]
  rw [← h1, hμ, h2]
end LevyStochCalc.Probability


