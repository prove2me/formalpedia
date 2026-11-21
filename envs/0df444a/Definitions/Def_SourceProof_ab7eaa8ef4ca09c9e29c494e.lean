-- Prove2me | Definitions.Def_SourceProof_ab7eaa8ef4ca09c9e29c494e
-- name    : SourceProof_ab7eaa8ef4ca09c9e29c494e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:04:45.576103+00:00
-- url     : https://prove2.me/theorems/c0aaedab-caa2-45d2-95a8-b6c0363ee90c
-- title:
--   LevyStochCalc source module: SourceProof_ab7eaa8ef4ca09c9e29c494e
-- statement:
--   The original source theorem `LevyStochCalc.Probability.exists_predictable_ae_eq` comes from the `LevyStochCalc.Probability.PredictableModification` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F002
import Definitions.Def_LevyStochCalc_Probability_PredictableModification_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Predictable representatives of progressive integrands

The elementary integrands of the `L²` theory — finite sums of a coefficient measurable at the
left endpoint of a cell, carried on that cell — are predictable, and the predictable processes
are closed under pointwise upper limits. Since the elementary integrands are dense in the
progressive integrands of finite energy, a progressive integrand agrees with a predictable one
almost everywhere in time and sample point.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Probability

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}

section Cells

end Cells

section Modification

open Brownian.Ito

variable {P : Measure Ω} [IsProbabilityMeasure P]


theorem _root_.Prove2MeSourceProof.h_ab7eaa8ef4ca09c9e29c494e (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {H : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry H)) (hp : ProgressivelyMeasurable ℱ H)
    {T : ℝ} (hT : 0 < T) (hfin : energy P T H ≠ ⊤) :
    ∃ K : Ω → ℝ → ℝ, Predictable ℱ K ∧
      (fun p : Ω × ℝ => H p.1 p.2) =ᵐ[energyMeasure P T] fun p : Ω × ℝ => K p.1 p.2 := by
  classical
  have hex : ∀ n : ℕ, ∃ G : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T,
      (∀ i : Fin G.N, StronglyMeasurable[ℱ (G.partition i.castSucc)] (G.ξ i)) ∧
      LevyStochCalc.Brownian.Ito.energy P T (fun ω s => H ω s - G.eval s ω) < ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have hpos : (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ :=
      ENNReal.inv_pos.mpr (by simp)
    exact LevyStochCalc.Brownian.Ito.exists_adaptedSimple_within ℱ H hm hp hT (lt_top_iff_ne_top.mpr hfin) hpos
  choose G hGadapt hGerr using hex
  have hHmem : MemLp (fun p : Ω × ℝ => H p.1 p.2) 2 (LevyStochCalc.Brownian.Ito.energyMeasure P T) :=
    LevyStochCalc.Brownian.Ito.memLp_of_energy_ne_top hm hfin
  have hDmem : ∀ n, MemLp (fun p : Ω × ℝ => H p.1 p.2 - (G n).eval p.2 p.1) 2
      (LevyStochCalc.Brownian.Ito.energyMeasure P T) := fun n =>
    LevyStochCalc.Brownian.Ito.memLp_of_energy_ne_top (H := fun ω s => H ω s - (G n).eval s ω)
      (hm.sub (G n).eval_jointly_measurable) (ne_top_of_lt (hGerr n))
  have hGmem : ∀ n, MemLp (fun p : Ω × ℝ => (G n).eval p.2 p.1) 2 (LevyStochCalc.Brownian.Ito.energyMeasure P T) := by
    intro n
    refine (hHmem.sub (hDmem n)).ae_eq (Filter.Eventually.of_forall fun p => ?_)
    simp
  have hsq : ∀ n, eLpNorm ((fun p : Ω × ℝ => (G n).eval p.2 p.1)
      - fun p : Ω × ℝ => H p.1 p.2) 2 (LevyStochCalc.Brownian.Ito.energyMeasure P T) ^ 2 < ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have hcomm : eLpNorm ((fun p : Ω × ℝ => (G n).eval p.2 p.1)
        - fun p : Ω × ℝ => H p.1 p.2) 2 (LevyStochCalc.Brownian.Ito.energyMeasure P T)
        = eLpNorm (fun p : Ω × ℝ => H p.1 p.2 - (G n).eval p.2 p.1) 2 (LevyStochCalc.Brownian.Ito.energyMeasure P T) := by
      rw [← eLpNorm_neg]
      refine eLpNorm_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp
    rw [hcomm, ← LevyStochCalc.Brownian.Ito.energy_eq_eLpNorm_sq (H := fun ω s => H ω s - (G n).eval s ω)
      (hm.sub (G n).eval_jointly_measurable) T]
    exact hGerr n
  have htend : Tendsto (fun n => eLpNorm ((fun p : Ω × ℝ => (G n).eval p.2 p.1)
      - fun p : Ω × ℝ => H p.1 p.2) 2 (LevyStochCalc.Brownian.Ito.energyMeasure P T)) atTop (𝓝 0) := by
    refine ENNReal.tendsto_atTop_zero.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := ENNReal.exists_inv_nat_lt (a := ε ^ 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    by_contra hcon
    have hle : ε ≤ eLpNorm ((fun p : Ω × ℝ => (G n).eval p.2 p.1)
        - fun p : Ω × ℝ => H p.1 p.2) 2 (LevyStochCalc.Brownian.Ito.energyMeasure P T) := le_of_not_ge hcon
    have h1 : ε ^ 2 ≤ eLpNorm ((fun p : Ω × ℝ => (G n).eval p.2 p.1)
        - fun p : Ω × ℝ => H p.1 p.2) 2 (LevyStochCalc.Brownian.Ito.energyMeasure P T) ^ 2 := pow_le_pow_left' hle 2
    have h2 : ((n : ℝ≥0∞) + 1)⁻¹ ≤ ((N : ℝ≥0∞))⁻¹ := by
      refine ENNReal.inv_le_inv.mpr ?_
      have hNn : (N : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hn
      exact hNn.trans le_self_add
    exact absurd (lt_of_le_of_lt h1 ((hsq n).trans_le (h2.trans hN.le))) (lt_irrefl _)
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (μ := LevyStochCalc.Brownian.Ito.energyMeasure P T) (p := 2)
    (by norm_num) (fun n => (hGmem n).aestronglyMeasurable) hHmem.aestronglyMeasurable
    htend).exists_seq_tendsto_ae
  refine ⟨LevyStochCalc.Probability.limsupSimpleEval G ns, LevyStochCalc.Probability.Predictable.limsup fun i =>
    LevyStochCalc.Probability.predictable_simpleEval (G (ns i)) (hGadapt (ns i)), ?_⟩
  filter_upwards [hae] with p hp'
  exact hp'.limsup_eq.symm
end Modification

end LevyStochCalc.Probability


