-- Prove2me | Definitions.Def_SourceProof_6293e0a2c6bb1095b807c809
-- name    : SourceProof_6293e0a2c6bb1095b807c809
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:00:14.431179+00:00
-- url     : https://prove2.me/theorems/432e82b0-541e-47e1-b280-627fd90756f9
-- title:
--   LevyStochCalc source module: SourceProof_6293e0a2c6bb1095b807c809
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_everywhere_cadlag_vectorIntegral` comes from the `LevyStochCalc.Brownian.CadlagVectorIntegral` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CadlagVectorIntegral_F000
import Definitions.Def_SourceProof_1720d71b3049591278c59d6d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# An everywhere-càdlàg version of the multidimensional Brownian integral

The multidimensional `L²` Itô integral `∫_0^t Z_s · dW_s = ∑_i ∫_0^t Z_s^i dW_s^i` is defined
separately at each time, so it carries no path regularity. Each coordinate integral has an
adapted modification with almost surely càdlàg paths; when the null set on which the paths fail
to be càdlàg belongs to `ℱ 0` and the filtration is constant before time `0`, that modification
can be replaced by `0` there, which makes every path càdlàg. Summing the `d` coordinate
modifications gives a version of the vector integral that is adapted to the right-continuous
filtration, jointly measurable, càdlàg at every sample point and a martingale.

## Main statements

* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.martingale_finsetSum` — a finite sum
  of martingales is a martingale.
* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_everywhere_cadlag_vectorIntegral`
  — the multidimensional Brownian integral has an everywhere-càdlàg martingale version.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §3.2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Multidim
namespace MultidimBrownianMotion

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {d : ℕ}


theorem _root_.Prove2MeSourceProof.h_6293e0a2c6bb1095b807c809
    (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ i : Fin d, IsBrownianFiltration (W.W i) ℱ)
    (Z : ℝ → Ω → (Fin d → ℝ))
    (hm : ∀ i : Fin d, Measurable (Function.uncurry (fun ω s => Z s ω i)))
    (hp : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ (fun ω s => Z s ω i))
    (hq : ∀ i : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    ∃ M : ℝ → Ω → ℝ, Adapted ℱ.rightCont M ∧ Measurable (Function.uncurry M) ∧
      (∀ t : ℝ, M t =ᵐ[P] fun ω =>
        MultidimBrownianMotion.stochasticIntegral W ℱ hℱW Z hm hp hq t ω) ∧
      (∀ (ω : Ω) (t : ℝ),
        Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)) ∧
          ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L)) ∧
      Martingale M ℱ.rightCont P := by
  classical
  -- a càdlàg-modulo-null adapted modification of each coordinate integral
  choose Y hYadapt hYae hYcad using fun i : Fin d =>
    LevyStochCalc.Ito.Picard.exists_cadlag_modification_itoIntegral (W.W i) ℱ (hℱW i)
      (fun ω s => Z s ω i) (hm i) (hp i) (hq i)
  -- the exceptional null set is `ℱ 0`-measurable, so it can be zeroed out
  choose M hMadapt hMae hMright hMleft using fun i : Fin d =>
    _root_.Prove2MeSourceProof.h_1720d71b3049591278c59d6d
      (P := P) (ℱ := ℱ.rightCont) hℱ0
      (fun s hs h0 => (ℱ.le_rightCont 0) _ (hnull s hs h0)) (hYadapt i) (hYcad i)
  have hMae' : ∀ (i : Fin d) (t : ℝ), M i t =ᵐ[P]
      LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W i) ℱ (hℱW i)
        (fun ω s => Z s ω i) (hm i) (hp i) (hq i) t :=
    fun i t => (hMae i t).trans (hYae i t)
  refine ⟨fun t ω => ∑ i : Fin d, M i t ω, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun t => Finset.measurable_sum _ fun i _ => hMadapt i t
  · refine LevyStochCalc.Probability.measurable_uncurry_of_rightContinuous
      (fun t => Finset.measurable_sum _ fun i _ => hMadapt i t) fun ω t => ?_
    exact tendsto_finsetSum _ fun i _ => hMright i ω t
  · intro t
    filter_upwards [MeasureTheory.ae_all_iff.mpr fun i : Fin d => hMae' i t] with ω hω
    exact Finset.sum_congr rfl fun i _ => hω i
  · refine fun ω t => ⟨tendsto_finsetSum _ fun i _ => hMright i ω t, ?_⟩
    choose L hL using fun i : Fin d => hMleft i ω t
    exact ⟨∑ i : Fin d, L i, tendsto_finsetSum _ fun i _ => hL i⟩
  · refine LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.martingale_finsetSum Finset.univ M fun i _ => ?_
    exact LevyStochCalc.Martingale.martingale_of_ae_eq
      (_root_.Prove2MeSourceProof.h_08c64b3622d7f10f8c921d88 (W.W i) ℱ
        (hℱW i) (fun ω s => Z s ω i) (hm i) (hp i) (hq i))
      (Adapted.stronglyAdapted (hMadapt i)) (hMae' i)
end MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim


