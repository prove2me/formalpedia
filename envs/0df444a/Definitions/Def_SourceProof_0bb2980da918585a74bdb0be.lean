-- Prove2me | Definitions.Def_SourceProof_0bb2980da918585a74bdb0be
-- name    : SourceProof_0bb2980da918585a74bdb0be
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:17:39.263899+00:00
-- url     : https://prove2.me/theorems/36cceff6-234a-4139-b6fc-f45d4eb7f1d0
-- title:
--   LevyStochCalc source module: SourceProof_0bb2980da918585a74bdb0be
-- statement:
--   The original source theorem `LevyStochCalc.Driver.paired_cell_re` comes from the `LevyStochCalc.Driver.CellIdentity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_01eee1faff568daabb3a0663
import Definitions.Def_SourceProof_2c6d67d089470febbbe666f1
import Definitions.Def_SourceProof_86ad92ff30384feb6bbec8b4
import Definitions.Def_SourceProof_b2f62c96bf5d0e1e1ceca423
import Definitions.Def_SourceProof_eefc39d6cdbb5cb476c0c1c7

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The product rule on a cell, in the shape the pairing consumes

The product rule of a trigonometric function of a Brownian increment with a bounded pure-jump
process, rewritten so that the Itô integrand is a bounded progressive factor times the
indicator of the cell and the jump term is an integral over the window up to the time.
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
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Window

end Window

section Identity

variable (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

end Identity

section Paired

variable (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

end Paired

section Parts

variable (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ} {ι : Type*} [Fintype ι]

include hℱN hℱW in

theorem _root_.Prove2MeSourceProof.h_0bb2980da918585a74bdb0be
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (ha : 0 ≤ a) (hab : a < b)
    (l : ℝ) {g g' : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    (hg'c : Continuous g') (hg'b : ∀ x, |g' x| ≤ |l|)
    (hmg : Measurable (Function.uncurry fun ω s => g' (X s ω) * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => g' (X s ω) * indIoc Ω a b ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖g' (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hito : ∀ T' : ℝ, 0 < T' →
      (fun ω : Ω => g (l * X T' ω) - g (l * X 0 ω)) =ᵐ[P] fun ω =>
        stochasticIntegralBrownian W ℱ hℱW
            (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg T' ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T',
              (-l ^ 2 * g (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ∫ ω, Z ω * V ω * (g (l * X t ω) * (charAt N w Bfam t ω).re) ∂P
      = ∫ ω, Z ω * V ω * (g (l * X 0 ω) * (charAt N w Bfam 0 ω).re) ∂P
        + ∫ ω, Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t,
            (charStrictPred N w Bfam A T e₀ s ω).re
              * trigDriftCell l (fun x => g (l * x)) X a b ω s ∂volume) ∂P
        + ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            g (l * X q.1 ω) * charRe N w Bfam A T ω q.1 q.2 ∂(referenceIntensity ν)) ∂P := by
  have hBsub' : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha hbT.le) le_rfl)
  have hBsub0 : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha le_rfl) le_rfl)
  have haT : a ≤ T := le_trans hab.le hbT.le
  refine _root_.Prove2MeSourceProof.h_eefc39d6cdbb5cb476c0c1c7 N hℱN W hℱW hXbase hX0 ha hab l hgc hgb hg'c hg'b hmg hpg hqg hito
    hT hA hAν (LevyStochCalc.Poisson.charReIntegrand N hℱN w hBm hA hAν hBsub')
    (LevyStochCalc.Poisson.markedPredictable_charRe N hℱN w hBm hA hAν hBsub')
    (fun ω s e hs => LevyStochCalc.Poisson.charRe_eq_zero_of_le N w hBsub T ω hs e)
    (LevyStochCalc.Poisson.abs_charRe_le N w Bfam A T)
    (fun s ω => LevyStochCalc.Poisson.abs_charAt_re_le N w s ω)
    (fun s => Complex.measurable_re.comp (LevyStochCalc.Poisson.measurable_charAt N w hBm s))
    (fun s => Complex.continuous_re.comp_stronglyMeasurable
      (LevyStochCalc.Poisson.stronglyMeasurable_charAt N hℱN w hBm s))
    ?_ (fun s ω => LevyStochCalc.Poisson.abs_charStrictPred_re_le N w Bfam A T e₀ s ω) ?_
    (Complex.measurable_re.comp (LevyStochCalc.Poisson.measurable_uncurry_charStrictPred N w hℱN hBm hA hAν T e₀))
    (_root_.Prove2MeSourceProof.h_01eee1faff568daabb3a0663 N w hℱN hBm hA hAν T e₀)
    hZ2 hZito hZcomp hVa hMv0 hVb ht htT haT
  · filter_upwards [_root_.Prove2MeSourceProof.h_86ad92ff30384feb6bbec8b4 N w hBm hA hAν hBsub' hℱN] with ω hω s
    exact (hω s).1
  · filter_upwards [_root_.Prove2MeSourceProof.h_b2f62c96bf5d0e1e1ceca423 N w hBm hA hAν hBsub' hℱN] with ω hω s
    rw [_root_.Prove2MeSourceProof.h_2c6d67d089470febbbe666f1 N w hT hbT hBsub0 he₀ s ω]
    exact (hω s).1
end Parts

end LevyStochCalc.Driver


