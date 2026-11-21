-- Prove2me | Definitions.Def_SourceProof_0ac980e224d4498dc611b565
-- name    : SourceProof_0ac980e224d4498dc611b565
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:04:46.409206+00:00
-- url     : https://prove2.me/theorems/9e12d6e2-6daf-481a-a58e-485b7cd98710
-- title:
--   LevyStochCalc source module: SourceProof_0ac980e224d4498dc611b565
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.version_ae_eq_zero` comes from the `LevyStochCalc.Ito.ItoFormulaUnboundedClamp` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F003
import Definitions.Def_LevyStochCalc_Ito_VectorItoProcessDiff_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Coefficients of a vector Itô process clamped at a finite level

Clamping the coefficients of a vector Itô process at level `j` leaves bounded coefficients of
finite energy whose distance in energy to the original coefficients tends to `0`, and the process
they drive stays within that distance of the original one in `L²`, uniformly on a bounded window;
along a suitable subsequence of levels the clamped processes converge to the original one almost
surely.

## Main statements

* `LevyStochCalc.Brownian.Ito.clampCoeff`, `clampDrift` — the clamped coefficients.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_window_clamp` — the mesh of the approximation.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Clamped

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section ClampProcess

variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')


theorem _root_.Prove2MeSourceProof.h_0ac980e224d4498dc611b565
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {b : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (hX : IsVectorItoVersion W ℱ' hcoord H hm hpg hq X₀ b X) :
    X 0 =ᵐ[P] X₀ := by
  have hzero : ∀ (p : Fin n) (k : Fin d),
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k) (H p k) (hm p k) (hpg p k) (hq p k) 0
        =ᵐ[P] 0 :=
    fun p k => _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 (W.W k) ℱ' (hcoord k) (H p k)
      (hm p k) (hpg p k) (hq p k) le_rfl
  have hall : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k) (H p k) (hm p k) (hpg p k) (hq p k) 0 ω
        = 0 := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact hzero p k
  filter_upwards [hX.ae_eq 0 le_rfl, hall] with ω hω hz
  rw [hω]
  funext p
  have hdrift : ∫ s in Set.Icc (0 : ℝ) 0, b p ω s ∂volume = 0 := by
    rw [show Set.Icc (0 : ℝ) 0 = {(0 : ℝ)} from Set.Icc_self 0,
      MeasureTheory.setIntegral_measure_zero _ Real.volume_singleton]
  simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess, vectorItoMartingale, coordItoIntegral, hdrift]
  have : ∑ k : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ' (hcoord k) (H p k)
      (hm p k) (hpg p k) (hq p k) 0 ω = 0 :=
    Finset.sum_eq_zero fun k _ => hz p k
  rw [this]
  ring
end ClampProcess

end Clamped

end LevyStochCalc.Brownian.Ito


