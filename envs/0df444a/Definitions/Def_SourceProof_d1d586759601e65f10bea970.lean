-- Prove2me | Definitions.Def_SourceProof_d1d586759601e65f10bea970
-- name    : SourceProof_d1d586759601e65f10bea970
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:19:48.338714+00:00
-- url     : https://prove2.me/theorems/74dfc5a3-964c-4bc1-8f22-54dfc51bc274
-- title:
--   LevyStochCalc source module: SourceProof_d1d586759601e65f10bea970
-- statement:
--   The original source theorem `LevyStochCalc.Driver.aestronglyMeasurable_cellHalf` comes from the `LevyStochCalc.Driver.CellGronwallPairing` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellGronwallPairing_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairings of a weight with the cell character

The mixed cell lemma runs a Grönwall argument on the pairing of a square-integrable weight and a
bounded factor with the product of the Brownian cell character `e^{i l X_s}` and the Poisson cell
character. That complex pairing is the combination of four real pairings, one for each of the
cosine and sine against the real and imaginary parts of the Poisson character, and equally the
cosine half plus `i` times the sine half, a half being the pairing of a trigonometric function of
the Brownian increment with the Poisson character. This file introduces those pairings together
with their integrability and boundedness, and records the cell identity for a real pairing in the
reduced form that the recombination consumes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Parts

variable (N : PoissonRandomMeasure P ν)

end Parts

section Half

variable (N : PoissonRandomMeasure P ν)

variable {Z V : Ω → ℝ} {Mv l : ℝ} {X : ℝ → Ω → ℝ} {g : ℝ → ℝ}

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.Prove2MeSourceProof.h_d1d586759601e65f10bea970 {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {b T : ℝ} (hT : 0 < T) (hbT : b < T) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A)
    {e₀ : E} (he₀ : e₀ ∈ A) (hZ2 : MemLp Z 2 P) (hVm : Measurable V) (hgc : Continuous g)
    (hXm : Measurable (Function.uncurry fun ω s => X s ω)) (T' : ℝ) :
    AEStronglyMeasurable (fun s => cellHalf N w Bfam Z V l X g s)
      (volume.restrict (Set.Icc (0 : ℝ) T')) := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T') with hμ
  have hZV : AEStronglyMeasurable (fun ω => Z ω * V ω) P :=
    hZ2.aestronglyMeasurable.mul hVm.aestronglyMeasurable
  have hgX : Measurable fun p : Ω × ℝ => g (l * X p.2 p.1) :=
    hgc.measurable.comp (measurable_const.mul hXm)
  have hR : AEStronglyMeasurable
      (fun p : Ω × ℝ => ((Z p.1 * V p.1 * g (l * X p.2 p.1) : ℝ) : ℂ)) (P.prod μ) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hZV.comp_fst.mul hgX.aestronglyMeasurable)
  have hC : Measurable fun p : Ω × ℝ => LevyStochCalc.Poisson.charStrictPred N w Bfam A T e₀ p.2 p.1 :=
    LevyStochCalc.Poisson.measurable_uncurry_charStrictPred N w hℱ hBm hA hAν T e₀
  have hjoint : AEStronglyMeasurable
      (Function.uncurry fun (ω : Ω) (s : ℝ) =>
        ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * LevyStochCalc.Poisson.charStrictPred N w Bfam A T e₀ s ω)
      (P.prod μ) := hR.mul hC.aestronglyMeasurable
  refine (hjoint.prod_swap.integral_prod_right').congr ?_
  have h0 : ∀ᵐ s ∂μ, s ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton, hμ,
      Measure.restrict_apply (measurableSet_singleton (0 : ℝ))]
    exact measure_mono_null Set.inter_subset_left Real.volume_singleton
  have hmem : ∀ᵐ s ∂μ, s ∈ Set.Icc (0 : ℝ) T' := by
    rw [hμ]; exact ae_restrict_mem measurableSet_Icc
  filter_upwards [h0, hmem] with s hs0 hs
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
  refine integral_congr_ae ?_
  filter_upwards [LevyStochCalc.Poisson.ae_charStrictPred_eq_charAt N w hBm hT hbT hBsub he₀ hspos] with ω hω
  change ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * LevyStochCalc.Poisson.charStrictPred N w Bfam A T e₀ s ω
      = ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * LevyStochCalc.Poisson.charAt N w Bfam s ω
  rw [hω]
end Half

section Reduced

variable {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱW : IsBrownianFiltration W ℱ}
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ} {Z V : Ω → ℝ} {Mv l : ℝ}

end Reduced

end LevyStochCalc.Driver


