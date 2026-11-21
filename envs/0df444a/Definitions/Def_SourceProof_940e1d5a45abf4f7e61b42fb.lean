-- Prove2me | Definitions.Def_SourceProof_940e1d5a45abf4f7e61b42fb
-- name    : SourceProof_940e1d5a45abf4f7e61b42fb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:50:16.358375+00:00
-- url     : https://prove2.me/theorems/f7701ca0-0031-4f47-9290-a977216d80ac
-- title:
--   LevyStochCalc source module: SourceProof_940e1d5a45abf4f7e61b42fb
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.isClosed_itoRange` comes from the `LevyStochCalc.Brownian.ItoRange` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F001
import Definitions.Def_SourceProof_27f689978bb8ca67ff7e2231

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The range of the Itô integral on a horizon

An integrand supported in `[0, T]`, jointly and progressively measurable and of finite energy,
is admissible for the Itô integral up to `T`. Such integrands are closed under sums and scalar
multiples, and the integral is additive and homogeneous on them, so their integrals form a
submodule of `L²`. The isometry of differences carries an energy-Cauchy sequence of integrands to
an `L²`-Cauchy sequence of integrals, so that submodule is closed.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Energy

variable {T : ℝ}

end Energy

namespace HorizonIntegrand

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

section Integral

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

end Integral

end HorizonIntegrand

section Range

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)


theorem _root_.Prove2MeSourceProof.h_940e1d5a45abf4f7e61b42fb (hT : 0 < T) :
    IsClosed ((itoRange W hℱ hT : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) := by
  refine IsSeqClosed.isClosed ?_
  intro u v hu huv
  choose G hG using hu
  have hCau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      LevyStochCalc.Brownian.Ito.energy P T (fun ω s => (G m).toFun ω s - (G n).toFun ω s) < ε := by
    intro ε hε
    have hcs : CauchySeq u := huv.cauchySeq
    rw [EMetric.cauchySeq_iff] at hcs
    obtain ⟨N, hN⟩ := hcs (min ε 1) (lt_min hε one_pos)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [LevyStochCalc.Brownian.Ito.energy_eq_edist_sq W hℱ hT (hG m) (hG n)]
    refine lt_of_lt_of_le (ENNReal.pow_lt_pow_left (by norm_num) (hN m hm n hn)) ?_
    calc (min ε 1) ^ 2 = min ε 1 * min ε 1 := sq _
      _ ≤ min ε 1 * 1 := mul_le_mul_right (min_le_right ε 1) _
      _ = min ε 1 := mul_one _
      _ ≤ ε := min_le_left ε 1
  obtain ⟨K, hKm, hKp, hKz, hKfin, hKtend⟩ :=
    _root_.Prove2MeSourceProof.h_27f689978bb8ca67ff7e2231 ℱ (fun n => (G n).measurable_uncurry)
      (fun n => (G n).progressive) (fun n => (G n).vanishing)
      (fun n => (G n).energy_ne_top) hCau
  obtain ⟨tgt, htgt⟩ : ∃ t : Lp ℝ 2 P,
      (t : Ω → ℝ) =ᵐ[P] (⟨K, hKm, hKp, hKz, hKfin⟩ : LevyStochCalc.Brownian.Ito.HorizonIntegrand P ℱ T).integral W hℱ :=
    ⟨_, MemLp.coeFn_toLp (LevyStochCalc.Brownian.Ito.HorizonIntegrand.memLp W hℱ _)⟩
  have hlim : Tendsto u atTop (𝓝 tgt) := by
    rw [EMetric.tendsto_atTop]
    intro ε hε
    have hpos : (0 : ℝ≥0∞) < (min ε 1) ^ 2 :=
      zero_lt_iff.mpr (pow_ne_zero 2 (ne_of_gt (lt_min hε one_pos)))
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hKtend.eventually_lt_const hpos)
    refine ⟨N, fun n hn => ?_⟩
    have hedist : LevyStochCalc.Brownian.Ito.energy P T (fun ω s => (G n).toFun ω s - K ω s) = edist (u n) tgt ^ 2 :=
      LevyStochCalc.Brownian.Ito.energy_eq_edist_sq W hℱ hT (hG n) htgt
    have hlt : edist (u n) tgt ^ 2 < (min ε 1) ^ 2 := hedist ▸ hN n hn
    rcases lt_or_ge (edist (u n) tgt) (min ε 1) with h | h
    · exact lt_of_lt_of_le h (min_le_left ε 1)
    · exact absurd hlt (not_lt.mpr (pow_le_pow_left' h 2))
  refine ⟨⟨K, hKm, hKp, hKz, hKfin⟩, ?_⟩
  rw [tendsto_nhds_unique huv hlim]
  exact htgt
end Range

section Representation

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

end Representation

end LevyStochCalc.Brownian.Ito


