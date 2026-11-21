-- Prove2me | Definitions.Def_SourceProof_eefc39d6cdbb5cb476c0c1c7
-- name    : SourceProof_eefc39d6cdbb5cb476c0c1c7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:13:38.181895+00:00
-- url     : https://prove2.me/theorems/b7791908-8422-493c-a385-95f1c368f272
-- title:
--   LevyStochCalc source module: SourceProof_eefc39d6cdbb5cb476c0c1c7
-- statement:
--   The original source theorem `LevyStochCalc.Driver.paired_cell_char` comes from the `LevyStochCalc.Driver.CellIdentity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellIdentity_F000
import Definitions.Def_SourceProof_645d257df9a95d8a5a50a5aa

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

include hℱN hℱW in

theorem _root_.Prove2MeSourceProof.h_eefc39d6cdbb5cb476c0c1c7
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
    {T : ℝ} (hT : 0 < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (G : MarkedHorizonIntegrand P ν ℱ T) (hGpred : Probability.MarkedPredictable ℱ ν G.toFun)
    (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {Cg : ℝ} (hGb : ∀ ω s e, |G.toFun ω s e| ≤ Cg)
    {Y Yminus : ℝ → Ω → ℝ} (hYb : ∀ s ω, |Y s ω| ≤ 1) (hYm : ∀ s, Measurable (Y s))
    (hYad : ∀ s, StronglyMeasurable[ℱ s] (Y s))
    (hY : ∀ᵐ ω ∂P, ∀ s : ℝ, Y s ω = Y 0 ω
      + ∫ p in (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ,
          G.toFun ω p.1 p.2 ∂(N.N ω))
    (hYmb : ∀ s ω, |Yminus s ω| ≤ 1)
    (hYminus : ∀ᵐ ω ∂P, ∀ s : ℝ, Yminus s ω = Y 0 ω
      + ∫ p in (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ,
          G.toFun ω p.1 p.2 ∂(N.N ω))
    (hYmmeas : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Yminus s ω))
    (hYmprog : Probability.ProgressivelyMeasurable ℱ fun (ω : Ω) (s : ℝ) => Yminus s ω)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (haT : a ≤ T) :
    ∫ ω, Z ω * V ω * (g (l * X t ω) * Y t ω) ∂P
      = ∫ ω, Z ω * V ω * (g (l * X 0 ω) * Y 0 ω) ∂P
        + ∫ ω, Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t,
            Yminus s ω * trigDriftCell l (fun x => g (l * x)) X a b ω s ∂volume) ∂P
        + ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            g (l * X q.1 ω) * G.toFun ω q.1 q.2 ∂(referenceIntensity ν)) ∂P := by
  classical
  have hglc : Continuous fun x : ℝ => g (l * x) :=
    hgc.comp (continuous_const.mul continuous_id)
  -- the Brownian factor
  have hXgc : ∀ ω, Continuous fun s => g (l * X s ω) := fun ω =>
    hglc.comp (hXbase.continuous_path ω)
  have hXga : ∀ s : ℝ, StronglyMeasurable[ℱ s] fun ω => g (l * X s ω) := fun s =>
    hglc.comp_stronglyMeasurable (hXbase.adapted s)
  have hXgb : ∀ s ω, |g (l * X s ω)| ≤ 1 := fun s ω => hgb _
  -- the Itô integrand of the paired identity
  have hKm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Yminus s ω * g' (X s ω)) :=
    hYmmeas.mul (hg'c.measurable.comp hXbase.measurable_uncurry)
  have hKp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      fun (ω : Ω) (s : ℝ) => Yminus s ω * g' (X s ω) :=
    hYmprog.mul (hXbase.progressivelyMeasurable_comp hg'c)
  have hKbd : ∀ (ω : Ω) (s : ℝ), |Yminus s ω * g' (X s ω)| ≤ |l| := by
    intro ω s
    rw [abs_mul]
    calc |Yminus s ω| * |g' (X s ω)| ≤ 1 * |l| :=
          mul_le_mul (hYmb s ω) (hg'b _) (abs_nonneg _) zero_le_one
      _ = |l| := one_mul _
  have hmm2 : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      (Yminus s ω * g' (X s ω)) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s) := hKm.mul hm
  have hpm2 : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun (ω : Ω) (s : ℝ) =>
      (Yminus s ω * g' (X s ω)) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s := hKp.mul hp
  have hbd2 : ∀ (ω : Ω) (s : ℝ),
      |(Yminus s ω * g' (X s ω)) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s| ≤ |l| := by
    intro ω s
    rw [abs_mul]
    calc |Yminus s ω * g' (X s ω)| * |LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s| ≤ |l| * 1 :=
          mul_le_mul (hKbd ω s) (LevyStochCalc.Brownian.Ito.indIoc_le_one a b ω s) (abs_nonneg _) (abs_nonneg _)
      _ = |l| := mul_one _
  have hqm2 : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖(Yminus s ω * g' (X s ω)) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun T' hT' => _root_.Prove2MeSourceProof.h_aa77a05410d36d075f77b369 hbd2 T' hT'
  -- the identity, then the pairing
  have hid := LevyStochCalc.Driver.hid_cell N W hℱW hXbase hX0 l hgc hgb hmg hpg hqg hito hA hAν G hYb hYm
    hYad hY hYmb hYminus hmm2 hpm2 hqm2 ht htT
  exact _root_.Prove2MeSourceProof.h_645d257df9a95d8a5a50a5aa N hℱN W hℱW hT ha hab haT hZ2 hZito hZcomp hVa hMv0 hVb
    hXgc hXga zero_le_one hXgb hYm hYb hYmmeas hYmb
    (LevyStochCalc.Brownian.Ito.measurable_trigDriftCell hXbase l hglc)
    (fun ω s => _root_.Prove2MeSourceProof.h_943c9ef24e577f5c6b238b25 l (fun x => hgb (l * x)) zero_le_one X a b ω s)
    G hGpred hGa hGb hA hAν hKm hKp hKbd hmm2 hpm2 hqm2 ht htT hid
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


