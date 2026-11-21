-- Prove2me | Definitions.Def_SourceProof_8e93ea357455e3e54fbc2c2e
-- name    : SourceProof_8e93ea357455e3e54fbc2c2e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:27:51.518917+00:00
-- url     : https://prove2.me/theorems/a8222b37-350a-4b66-a1b7-b42f2eb0d1b6
-- title:
--   LevyStochCalc source module: SourceProof_8e93ea357455e3e54fbc2c2e
-- statement:
--   The original source theorem `LevyStochCalc.Driver.cellPart_of_paired` comes from the `LevyStochCalc.Driver.CellGronwallPairing` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellGronwallPairing_F001
import Definitions.Def_SourceProof_96c6857824b08f108587924a

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

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.Prove2MeSourceProof.h_8e93ea357455e3e54fbc2c2e
    (hX : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    {g : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    {A : Set E} (hAν : ν A ≠ ⊤)
    {Y Ym : ℝ → Ω → ℝ} (hYmm : Measurable (Function.uncurry fun ω s => Ym s ω))
    (hYmb : ∀ s ω, |Ym s ω| ≤ 1)
    (hYY : ∀ s, 0 < s → ∀ᵐ ω ∂P, Ym s ω = Y s ω)
    {K : Ω → ℝ → E → ℝ} (hKm : Measurable fun p : Ω × ℝ × E => K p.1 p.2.1 p.2.2)
    {MK : ℝ} (hKb : ∀ ω s e, |K ω s e| ≤ MK)
    (hZ1 : Integrable Z P) (hVm : Measurable V) (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, |V ω| ≤ Mv)
    {t : ℝ}
    (hbase : ∫ ω, Z ω * V ω * (g (l * X t ω) * Y t ω) ∂P
      = ∫ ω, Z ω * V ω * (g (l * X 0 ω) * Y 0 ω) ∂P
        + ∫ ω, Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t,
            Ym s ω * trigDriftCell l (fun x => g (l * x)) X a b ω s ∂volume) ∂P
        + ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            g (l * X q.1 ω) * K ω q.1 q.2 ∂(referenceIntensity ν)) ∂P) :
    cellPart P Z V l X g Y t
      = cellPart P Z V l X g Y 0
        + ∫ s in Set.Ioc (0 : ℝ) t, cellDrift l a b s * cellPart P Z V l X g Y s ∂volume
        + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            (∫ ω, Z ω * V ω * (g (l * X q.1 ω) * K ω q.1 q.2) ∂P)
            ∂(referenceIntensity ν) := by
  have hdrift := LevyStochCalc.Driver.integral_mul_setIntegral_drift hX l hgc hgb hYmm hYmb hZ1
    hVm.aestronglyMeasurable hMv0 hVb t
  have hjump := _root_.Prove2MeSourceProof.h_96c6857824b08f108587924a (X := X) hX.measurable_uncurry l hgc hgb hAν
    hKm hKb hZ1 hVm.aestronglyMeasurable hMv0 hVb t
  have hswap : ∫ s in Set.Ioc (0 : ℝ) t, ∫ ω, Z ω * V ω *
        (Ym s ω * LevyStochCalc.Brownian.Ito.trigDriftCell l (fun x => g (l * x)) X a b ω s) ∂P ∂volume
      = ∫ s in Set.Ioc (0 : ℝ) t,
          LevyStochCalc.Driver.cellDrift l a b s * LevyStochCalc.Driver.cellPart P Z V l X g Y s ∂volume := by
    refine setIntegral_congr_ae measurableSet_Ioc (Filter.Eventually.of_forall fun s hs => ?_)
    have hcongr : ∫ ω, Z ω * V ω *
          (Ym s ω * LevyStochCalc.Brownian.Ito.trigDriftCell l (fun x => g (l * x)) X a b ω s) ∂P
        = ∫ ω, Z ω * V ω *
          (Y s ω * LevyStochCalc.Brownian.Ito.trigDriftCell l (fun x => g (l * x)) X a b ω s) ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hYY s hs.1] with ω hω
      rw [hω]
    rw [hcongr, LevyStochCalc.Driver.integral_mul_trigDriftCell (Z := Z) (V := V) l g Y s]
    rfl
  rw [LevyStochCalc.Driver.cellPart, hbase, hdrift, hjump, hswap]
  rfl
end Reduced

end LevyStochCalc.Driver


