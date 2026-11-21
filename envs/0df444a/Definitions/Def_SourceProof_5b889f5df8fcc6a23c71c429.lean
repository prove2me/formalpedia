-- Prove2me | Definitions.Def_SourceProof_5b889f5df8fcc6a23c71c429
-- name    : SourceProof_5b889f5df8fcc6a23c71c429
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:28:49.258337+00:00
-- url     : https://prove2.me/theorems/d2dd69c2-dffc-4274-9035-a66dd5cffb1e
-- title:
--   LevyStochCalc source module: SourceProof_5b889f5df8fcc6a23c71c429
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.isClosed_compensatedRange` comes from the `LevyStochCalc.Poisson.CompensatedRange` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F002
import Definitions.Def_SourceProof_8597dc90ffad905522400a1d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The range of the compensated Poisson integral on a horizon

A marked integrand supported in `[0, T]`, jointly and progressively measurable and of finite
energy, is admissible for the compensated integral up to `T`. Such integrands are closed under
sums and scalar multiples, and the integral is additive and homogeneous on them, so their
integrals form a submodule of `L²`. The isometry of differences carries an energy-Cauchy sequence
of integrands to an `L²`-Cauchy sequence of integrals, so that submodule is closed.
-/

namespace LevyStochCalc.Poisson.Compensated

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Progressive

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

end Progressive

namespace MarkedHorizonIntegrand

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

section Integral

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Integral

end MarkedHorizonIntegrand

section Range

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)


theorem _root_.Prove2MeSourceProof.h_5b889f5df8fcc6a23c71c429 (hT : 0 < T) :
    IsClosed ((compensatedRange N hℱ hT : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) := by
  refine IsSeqClosed.isClosed ?_
  intro u v hu huv
  choose G hG using hu
  have hCau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N₀, ∀ m, N₀ ≤ m → ∀ n, N₀ ≤ n →
      LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => (G m).toFun ω s e - (G n).toFun ω s e) < ε := by
    intro ε hε
    have hcs : CauchySeq u := huv.cauchySeq
    rw [EMetric.cauchySeq_iff] at hcs
    obtain ⟨N₀, hN₀⟩ := hcs (min ε 1) (lt_min hε one_pos)
    refine ⟨N₀, fun m hm n hn => ?_⟩
    rw [LevyStochCalc.Poisson.Compensated.markedEnergy_eq_edist_sq N hℱ hT (hG m) (hG n)]
    refine lt_of_lt_of_le (ENNReal.pow_lt_pow_left (by norm_num) (hN₀ m hm n hn)) ?_
    calc (min ε 1) ^ 2 = min ε 1 * min ε 1 := sq _
      _ ≤ min ε 1 * 1 := by gcongr; exact min_le_right ε 1
      _ = min ε 1 := mul_one _
      _ ≤ ε := min_le_left ε 1
  obtain ⟨K, hKm, hKp, hKz, hKfin, hKtend⟩ :=
    _root_.Prove2MeSourceProof.h_8597dc90ffad905522400a1d ℱ (fun n => (G n).measurable_uncurry)
      (fun n => (G n).progressive) (fun n => (G n).vanishing)
      (fun n => (G n).energy_ne_top) hCau
  obtain ⟨tgt, htgt⟩ : ∃ t : Lp ℝ 2 P, (t : Ω → ℝ)
      =ᵐ[P] (⟨K, hKm, hKp, hKz, hKfin⟩ : LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T).integral N hℱ :=
    ⟨_, MemLp.coeFn_toLp (LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.memLp N hℱ _)⟩
  have hlim : Tendsto u atTop (𝓝 tgt) := by
    rw [EMetric.tendsto_atTop]
    intro ε hε
    have hpos : (0 : ℝ≥0∞) < (min ε 1) ^ 2 :=
      zero_lt_iff.mpr (pow_ne_zero 2 (ne_of_gt (lt_min hε one_pos)))
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hKtend.eventually_lt_const hpos)
    refine ⟨N₀, fun n hn => ?_⟩
    have hedist : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => (G n).toFun ω s e - K ω s e)
        = edist (u n) tgt ^ 2 := LevyStochCalc.Poisson.Compensated.markedEnergy_eq_edist_sq N hℱ hT (hG n) htgt
    have hlt : edist (u n) tgt ^ 2 < (min ε 1) ^ 2 := hedist ▸ hN₀ n hn
    rcases lt_or_ge (edist (u n) tgt) (min ε 1) with h | h
    · exact lt_of_lt_of_le h (min_le_left ε 1)
    · exact absurd hlt (not_lt.mpr (pow_le_pow_left' h 2))
  refine ⟨⟨K, hKm, hKp, hKz, hKfin⟩, ?_⟩
  rw [tendsto_nhds_unique huv hlim]
  exact htgt
end Range

section Representation

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

end Representation

end LevyStochCalc.Poisson.Compensated


