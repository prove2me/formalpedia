-- Prove2me | Definitions.Def_SourceProof_4158bbe01732caa4bdb467b2
-- name    : SourceProof_4158bbe01732caa4bdb467b2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:52:54.187619+00:00
-- url     : https://prove2.me/theorems/fa1f6d1e-3bd5-4bcc-be18-62e9d237df94
-- title:
--   LevyStochCalc source module: SourceProof_4158bbe01732caa4bdb467b2
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.exists_stochasticIntegralBrownian_finsetSum` comes from the `LevyStochCalc.Brownian.ItoFinsetSum` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFinsetSum_F000
import Definitions.Def_SourceProof_0a844334f53895dbf4245fb6
import Definitions.Def_SourceProof_2631a3786acbcf68272d1d52
import Definitions.Def_SourceProof_700488d66fa58fc241f21293

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Linearity of the Itô integral over finite sums

Additivity and scaling give the negation, the difference and the sum over a finite index set.
The finite sum is stated existentially in the admissibility data of the summed integrand, which
the induction produces along with the identity.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_neg`
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sub`
* `LevyStochCalc.Brownian.Ito.exists_stochasticIntegralBrownian_finsetSum`
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_4158bbe01732caa4bdb467b2 {ι : Type*}
    (H : ι → Ω → ℝ → ℝ) (hm : ∀ i, Measurable (Function.uncurry (H i)))
    (hp : ∀ i, Probability.ProgressivelyMeasurable ℱ (H i))
    (hq : ∀ (i : ι) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (J : Finset ι) {T : ℝ} (hT : 0 < T) :
    ∃ (hms : Measurable (Function.uncurry fun ω u => ∑ i ∈ J, H i ω u))
      (hps : Probability.ProgressivelyMeasurable ℱ fun ω u => ∑ i ∈ J, H i ω u)
      (hqs : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T',
        (‖∑ i ∈ J, H i ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      stochasticIntegralBrownian W ℱ hℱ (fun ω u => ∑ i ∈ J, H i ω u) hms hps hqs T
        =ᵐ[P] fun ω => ∑ i ∈ J,
          stochasticIntegralBrownian W ℱ hℱ (H i) (hm i) (hp i) (hq i) T ω := by
  classical
  induction J using Finset.induction with
  | empty =>
    have hfun : (fun (ω : Ω) (u : ℝ) => ∑ i ∈ (∅ : Finset ι), H i ω u)
        = fun (_ : Ω) (_ : ℝ) => (0 : ℝ) := by
      funext ω u
      simp
    have hmz : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) := measurable_const
    have hpz : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (0 : ℝ) :=
      LevyStochCalc.Probability.progressivelyMeasurable_zero ℱ
    have hqz : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ _u in Set.Icc (0 : ℝ) T',
        (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T' _
      simp
    have hqz' := LevyStochCalc.Brownian.Ito.energy_lt_top_congr (P := P) hfun.symm hqz
    refine ⟨hfun ▸ hmz, hfun ▸ hpz, hqz', ?_⟩
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun (hfun ▸ hmz) (hfun ▸ hpz) hqz'
      hmz hpz hqz T]
    filter_upwards [_root_.Prove2MeSourceProof.h_2631a3786acbcf68272d1d52 W ℱ hℱ hmz hpz hqz T] with ω hω
    simpa using hω
  | insert a J ha ih =>
    obtain ⟨hms, hps, hqs, hae⟩ := ih
    have hfun : (fun (ω : Ω) (u : ℝ) => ∑ i ∈ insert a J, H i ω u)
        = fun ω u => H a ω u + ∑ i ∈ J, H i ω u := by
      funext ω u
      exact Finset.sum_insert ha
    have hma : Measurable (Function.uncurry fun ω u => H a ω u + ∑ i ∈ J, H i ω u) :=
      (hm a).add hms
    have hpa : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
        fun ω u => H a ω u + ∑ i ∈ J, H i ω u := (hp a).add hps
    have hqa : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T',
        (‖H a ω u + ∑ i ∈ J, H i ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
      _root_.Prove2MeSourceProof.h_700488d66fa58fc241f21293 (fun ω u => LevyStochCalc.Brownian.Ito.sq_nnnorm_add_le_two_mul _ _) (hm a) hms
        (hq a) hqs
    have hqi := LevyStochCalc.Brownian.Ito.energy_lt_top_congr (P := P) hfun.symm hqa
    refine ⟨hfun ▸ hma, hfun ▸ hpa, hqi, ?_⟩
    rw [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun (hfun ▸ hma) (hfun ▸ hpa) hqi
      hma hpa hqa T]
    filter_upwards [_root_.Prove2MeSourceProof.h_0a844334f53895dbf4245fb6 W ℱ hℱ (hm a) hms (hp a) hps (hq a) hqs
      hma hpa hqa hT, hae] with ω hadd hsum
    rw [hadd, hsum, Finset.sum_insert ha]
end LevyStochCalc.Brownian.Ito


