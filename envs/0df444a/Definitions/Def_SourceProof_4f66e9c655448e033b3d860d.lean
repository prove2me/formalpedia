-- Prove2me | Definitions.Def_SourceProof_4f66e9c655448e033b3d860d
-- name    : SourceProof_4f66e9c655448e033b3d860d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:33:49.123092+00:00
-- url     : https://prove2.me/theorems/3540c0d3-8e0c-4a15-9e7a-36ce40a74593
-- title:
--   LevyStochCalc source module: SourceProof_4f66e9c655448e033b3d860d
-- statement:
--   The original source theorem `LevyStochCalc.Probability.exists_markedPredictable_ae_eq` comes from the `LevyStochCalc.Probability.MarkedPredictableModification` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableModification_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Predictable representatives of marked progressive integrands

A mark-step integrand adapted at the left endpoints of its cells is predictable on the time–mark
space, and the marked predictable processes are closed under pointwise upper limits. The
mark-step integrands are dense in the marked progressive integrands of finite energy, so such an
integrand agrees with a predictable one almost everywhere in time, mark and sample point.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν] {ℱ : Filtration ℝ mΩ}

open LevyStochCalc.Poisson.Compensated

variable {P : Measure Ω} [IsProbabilityMeasure P]


theorem _root_.Prove2MeSourceProof.h_4f66e9c655448e033b3d860d (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : MarkedProgressivelyMeasurable ℱ φ) {T : ℝ} (hT : 0 < T)
    (hfin : markedEnergy P ν T φ ≠ ⊤) :
    ∃ ψ : Ω → ℝ → E → ℝ, MarkedPredictable ℱ ν ψ ∧
      (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
        =ᵐ[markedEnergyMeasure P ν T] fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2 := by
  classical
  have hex : ∀ n : ℕ, ∃ ℓ : ℕ, ∃ G : LevyStochCalc.Poisson.Compensated.MarkStep Ω E ν (LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic T hT ℓ), G.Adapted ℱ ∧
      LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => φ ω s e - G.eval s e ω) < ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    obtain ⟨ℓ, -, G, hGa, hGe⟩ := _root_.Prove2MeSourceProof.h_68bcc04d25dcb303fabb8713 N ℱ φ hm hp hT
      (lt_top_iff_ne_top.mpr hfin) 0 (ε := ((n : ℝ≥0∞) + 1)⁻¹) (ENNReal.inv_pos.mpr (by simp))
    exact ⟨ℓ, G, hGa, hGe⟩
  choose ℓ G hGadapt hGerr using hex
  have hGm : ∀ n, Measurable fun p : Ω × ℝ × E => (G n).eval p.2.1 p.2.2 p.1 := fun n =>
    (G n).eval_measurable
  have hφmem : MemLp (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T) :=
    LevyStochCalc.Poisson.Compensated.memLp_of_markedEnergy_ne_top hm hfin
  have hDmem : ∀ n, MemLp (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2 - (G n).eval p.2.1 p.2.2 p.1) 2
      (LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T) := fun n =>
    LevyStochCalc.Poisson.Compensated.memLp_of_markedEnergy_ne_top (φ := fun ω s e => φ ω s e - (G n).eval s e ω)
      (hm.sub (hGm n)) (ne_top_of_lt (hGerr n))
  have hGmem : ∀ n, MemLp (fun p : Ω × ℝ × E => (G n).eval p.2.1 p.2.2 p.1) 2
      (LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T) := by
    intro n
    refine (hφmem.sub (hDmem n)).ae_eq (Filter.Eventually.of_forall fun p => ?_)
    simp
  have hsq : ∀ n, eLpNorm ((fun p : Ω × ℝ × E => (G n).eval p.2.1 p.2.2 p.1)
      - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T) ^ 2
        < ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have hcomm : eLpNorm ((fun p : Ω × ℝ × E => (G n).eval p.2.1 p.2.2 p.1)
        - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T)
        = eLpNorm (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2 - (G n).eval p.2.1 p.2.2 p.1) 2
          (LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T) := by
      rw [← eLpNorm_neg]
      refine eLpNorm_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp
    rw [hcomm, ← LevyStochCalc.Poisson.Compensated.markedEnergy_eq_eLpNorm_sq (φ := fun ω s e => φ ω s e - (G n).eval s e ω)
      (hm.sub (hGm n)) T]
    exact hGerr n
  have htend : Tendsto (fun n => eLpNorm ((fun p : Ω × ℝ × E => (G n).eval p.2.1 p.2.2 p.1)
      - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T)) atTop (𝓝 0) := by
    refine ENNReal.tendsto_atTop_zero.mpr fun ε hε => ?_
    obtain ⟨M, hM⟩ := ENNReal.exists_inv_nat_lt (a := ε ^ 2) (by positivity)
    refine ⟨M, fun n hn => ?_⟩
    by_contra hcon
    have hle : ε ≤ eLpNorm ((fun p : Ω × ℝ × E => (G n).eval p.2.1 p.2.2 p.1)
        - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T) :=
      le_of_not_ge hcon
    have h1 : ε ^ 2 ≤ eLpNorm ((fun p : Ω × ℝ × E => (G n).eval p.2.1 p.2.2 p.1)
        - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T) ^ 2 :=
      pow_le_pow_left' hle 2
    have h2 : ((n : ℝ≥0∞) + 1)⁻¹ ≤ ((M : ℝ≥0∞))⁻¹ := by
      refine ENNReal.inv_le_inv.mpr ?_
      have hMn : (M : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hn
      exact hMn.trans le_self_add
    exact absurd (lt_of_le_of_lt h1 ((hsq n).trans_le (h2.trans hM.le))) (lt_irrefl _)
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (μ := LevyStochCalc.Poisson.Compensated.markedEnergyMeasure P ν T) (p := 2) (by norm_num)
    (fun n => (hGmem n).aestronglyMeasurable) hφmem.aestronglyMeasurable
    htend).exists_seq_tendsto_ae
  refine ⟨LevyStochCalc.Probability.limsupMarkStepEval G ns, LevyStochCalc.Probability.MarkedPredictable.limsup fun i =>
    LevyStochCalc.Probability.markedPredictable_markStepEval (G (ns i)) (hGadapt (ns i)), ?_⟩
  filter_upwards [hae] with p hp'
  exact hp'.limsup_eq.symm
end LevyStochCalc.Probability


