-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F001
-- name    : LevyStochCalc_Brownian_ItoIntegrandComplete_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T22:15:58.046275+00:00
-- url     : https://prove2.me/theorems/600bd774-fabf-448a-94c5-891c3cfb1ae6
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoIntegrandComplete
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoIntegrandComplete. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoIntegrandComplete_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Completeness of the admissible integrands on a horizon

The energy of an integrand over `[0, T]` is the square of its `L²`-seminorm for the product of
the sample measure with Lebesgue measure on the horizon. A sequence of integrands that is Cauchy
for that energy therefore has an `L²`-limit, and the pointwise `limsup` of an almost everywhere
convergent subsequence is a representative of that limit which is again progressively measurable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Complete

variable {T : ℝ} {H : ℕ → Ω → ℝ → ℝ}

omit [IsProbabilityMeasure P] in
/-- An energy-Cauchy sequence of integrands has an `L²`-limit on the product space. -/
theorem exists_energy_limit (hm : ∀ n, Measurable (Function.uncurry (H n)))
    (hfin : ∀ n, energy P T (H n) ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      energy P T (fun ω s => H m ω s - H n ω s) < ε) :
    ∃ g : Ω × ℝ → ℝ, MemLp g 2 (energyMeasure P T)
      ∧ Tendsto (fun n => eLpNorm ((fun p : Ω × ℝ => H n p.1 p.2) - g) 2 (energyMeasure P T))
          atTop (𝓝 0) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hMem : ∀ n, MemLp (fun p : Ω × ℝ => H n p.1 p.2) 2 (energyMeasure P T) :=
    fun n => memLp_of_energy_ne_top (hm n) (hfin n)
  have hcs : CauchySeq fun n => (hMem n).toLp (fun p : Ω × ℝ => H n p.1 p.2) := by
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcau (ε ^ 2) (by positivity)
    refine ⟨N, fun m hm' n hn' => ?_⟩
    rw [Lp.edist_def]
    have hcongr : eLpNorm
          ((((hMem m).toLp (fun p : Ω × ℝ => H m p.1 p.2)) : Ω × ℝ → ℝ)
            - (((hMem n).toLp (fun p : Ω × ℝ => H n p.1 p.2)) : Ω × ℝ → ℝ))
          2 (energyMeasure P T)
        = eLpNorm (fun p : Ω × ℝ => H m p.1 p.2 - H n p.1 p.2) 2 (energyMeasure P T) := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hMem m).coeFn_toLp, (hMem n).coeFn_toLp] with p h1 h2
      simp only [Pi.sub_apply]
      rw [h1, h2]
    rw [hcongr]
    rcases lt_or_ge (eLpNorm (fun p : Ω × ℝ => H m p.1 p.2 - H n p.1 p.2)
      2 (energyMeasure P T)) ε with hlt' | hge
    · exact hlt'
    · exfalso
      have hsq : ε ^ 2 ≤ eLpNorm (fun p : Ω × ℝ => H m p.1 p.2 - H n p.1 p.2)
          2 (energyMeasure P T) ^ 2 := pow_le_pow_left' hge 2
      have hlt := hN m hm' n hn'
      rw [energy_eq_eLpNorm_sq ((hm m).sub (hm n)) T] at hlt
      exact absurd hlt (not_lt.mpr hsq)
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨(G : Ω × ℝ → ℝ), Lp.memLp G, ?_⟩
  have hlim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ G).mp hG
  refine hlim.congr fun n => ?_
  refine eLpNorm_congr_ae ?_
  filter_upwards [(hMem n).coeFn_toLp] with p h1
  simp only [Pi.sub_apply]
  rw [h1]
/-- The pointwise `limsup` of a subsequence of integrands. -/
noncomputable def limsupIntegrand (H : ℕ → Ω → ℝ → ℝ) (ns : ℕ → ℕ) : Ω → ℝ → ℝ :=
  fun ω s => limsup (fun i => H (ns i) ω s) atTop
end Complete

end LevyStochCalc.Brownian.Ito


