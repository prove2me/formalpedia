-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CellIdentity_F000
-- name    : LevyStochCalc_Driver_CellIdentity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:06:24.238497+00:00
-- url     : https://prove2.me/theorems/b4c96559-57b8-4a47-b430-4e015143f7da
-- title:
--   Source declarations: LevyStochCalc.Driver.CellIdentity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CellIdentity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CellCharacter_F001
import Definitions.Def_LevyStochCalc_Driver_CellPairing_F000
import Definitions.Def_LevyStochCalc_Driver_CellPairing_F001
import Definitions.Def_LevyStochCalc_Driver_ProductRule_F000
import Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F000
import Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F002
import Definitions.Def_LevyStochCalc_Poisson_CharacterStrictProcess_F003
import Definitions.Def_SourceProof_062bf24d9942f2f625b4c411
import Definitions.Def_SourceProof_607e96fa91c679c474a24409
import Definitions.Def_SourceProof_943c9ef24e577f5c6b238b25

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

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] [MeasurableSpace E]
  [IsProbabilityMeasure P] [SigmaFinite ν] [MeasurableSpace Ω] in
/-- The window of the horizon met with the times up to `t` is the window up to `t`. -/
theorem window_inter_Ioc {T t : ℝ} (htT : t ≤ T) (A : Set E) :
    (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioc (0 : ℝ) t ×ˢ (Set.univ : Set E)
      = Set.Ioc (0 : ℝ) t ×ˢ A := by
  rw [Set.prod_inter_prod, Set.inter_univ, Set.Ioc_inter_Ioc, max_self,
    min_eq_right htT]
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

include hℱW in
/-- **The cell identity.** The product rule for `g (l X)` and a bounded pure-jump process, with
the Itô integrand written as a bounded factor times the cell's indicator and the jump term over
the window up to the time. -/
theorem hid_cell
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (l : ℝ) {g g' : ℝ → ℝ} (hgc : Continuous g)
    (hgb : ∀ x, |g x| ≤ 1)
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
    {T : ℝ} {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (G : MarkedHorizonIntegrand P ν ℱ T)
    {Y Yminus : ℝ → Ω → ℝ} (hYb : ∀ s ω, |Y s ω| ≤ 1) (hYm : ∀ s, Measurable (Y s))
    (hYad : ∀ s, StronglyMeasurable[ℱ s] (Y s))
    (hY : ∀ᵐ ω ∂P, ∀ s : ℝ, Y s ω = Y 0 ω
      + ∫ p in (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ,
          G.toFun ω p.1 p.2 ∂(N.N ω))
    (hYmb : ∀ s ω, |Yminus s ω| ≤ 1)
    (hYminus : ∀ᵐ ω ∂P, ∀ s : ℝ, Yminus s ω = Y 0 ω
      + ∫ p in (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ,
          G.toFun ω p.1 p.2 ∂(N.N ω))
    (hmm2 : Measurable (Function.uncurry fun ω s =>
      (Yminus s ω * g' (X s ω)) * indIoc Ω a b ω s))
    (hpm2 : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (Yminus s ω * g' (X s ω)) * indIoc Ω a b ω s)
    (hqm2 : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖(Yminus s ω * g' (X s ω)) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ∀ᵐ ω ∂P, g (l * X t ω) * Y t ω - g (l * X 0 ω) * Y 0 ω
      = stochasticIntegralBrownian W ℱ hℱW
          (fun ω s => (Yminus s ω * g' (X s ω)) * indIoc Ω a b ω s) hmm2 hpm2 hqm2 t ω
        + (∫ s in Set.Ioc (0 : ℝ) t,
            Yminus s ω * trigDriftCell l (fun x => g (l * x)) X a b ω s ∂volume)
        + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            g (l * X q.1 ω) * G.toFun ω q.1 q.2 ∂(N.N ω) := by
  classical
  have hglc : Continuous fun x : ℝ => g (l * x) :=
    hgc.comp (continuous_const.mul continuous_id)
  have hbm := measurable_trigDriftCell hXbase l (g := fun x : ℝ => g (l * x)) hglc
  have hXtrig := _root_.Prove2MeSourceProof.h_062bf24d9942f2f625b4c411 hXbase l hgc hmg hpg hqg hito hX0
  have hRm : MeasurableSet (Set.Ioc (0 : ℝ) T ×ˢ A) := measurableSet_Ioc.prod hA
  have hRfin : referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hAν T
  -- the two integrand shapes agree
  have hEq : (fun (ω : Ω) (s : ℝ) => Yminus s ω * (g' (X s ω) * indIoc Ω a b ω s))
      = fun ω s => (Yminus s ω * g' (X s ω)) * indIoc Ω a b ω s := by
    funext ω s
    ring
  have hmm1 : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      Yminus s ω * (g' (X s ω) * indIoc Ω a b ω s)) := by rw [hEq]; exact hmm2
  have hpm1 : Probability.ProgressivelyMeasurable ℱ fun (ω : Ω) (s : ℝ) =>
      Yminus s ω * (g' (X s ω) * indIoc Ω a b ω s) := by rw [hEq]; exact hpm2
  have hqm1 : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖Yminus s ω * (g' (X s ω) * indIoc Ω a b ω s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro T' hT'
    have h := hqm2 T' hT'
    simpa only [mul_assoc] using h
  have hSIB := stochasticIntegralBrownian_congr_fun W ℱ hℱW hEq hmm1 hpm1 hqm1 hmm2 hpm2 hqm2 t
  have hpr := _root_.Prove2MeSourceProof.h_607e96fa91c679c474a24409 N W ℱ hℱW
    (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg hXtrig hbm
    (fun ω s => _root_.Prove2MeSourceProof.h_943c9ef24e577f5c6b238b25 l (fun x => hgb (l * x)) zero_le_one X a b ω s) hRm hRfin
    Y hYb hYm hYad hY Yminus hYmb hYminus hmm1 hpm1 hqm1 ht
  filter_upwards [hpr] with ω hω
  rw [hω, congrFun hSIB ω, window_inter_Ioc htT A]
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

end Parts

end LevyStochCalc.Driver


