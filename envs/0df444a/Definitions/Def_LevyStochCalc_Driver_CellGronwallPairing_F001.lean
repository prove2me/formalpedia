-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CellGronwallPairing_F001
-- name    : LevyStochCalc_Driver_CellGronwallPairing_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:23:50.433568+00:00
-- url     : https://prove2.me/theorems/0caab8ab-c89c-42c2-b644-38909621b665
-- title:
--   Source declarations: LevyStochCalc.Driver.CellGronwallPairing
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CellGronwallPairing. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellGronwallPairing_F000
import Definitions.Def_SourceProof_9d0138fdc01d3cc6c2310f1d
import Definitions.Def_SourceProof_d1d586759601e65f10bea970

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
/-- The pairing is integrable over a window of times. -/
theorem integrableOn_cellHalf {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {b T : ℝ} (hT : 0 < T) (hbT : b < T) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A)
    {e₀ : E} (he₀ : e₀ ∈ A) (hZ2 : MemLp Z 2 P) (hVm : Measurable V) (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv) (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    (hXm : Measurable (Function.uncurry fun ω s => X s ω)) (T' : ℝ) :
    IntegrableOn (fun s => cellHalf N w Bfam Z V l X g s) (Set.Icc (0 : ℝ) T') volume := by
  refine Integrable.mono' (integrable_const (Mv * ∫ ω, ‖Z ω‖ ∂P))
    (_root_.Prove2MeSourceProof.h_d1d586759601e65f10bea970 N hℱ w hBm hA hAν hT hbT hBsub he₀ hZ2 hVm hgc hXm T')
    (Filter.Eventually.of_forall fun s => ?_)
  exact _root_.Prove2MeSourceProof.h_9d0138fdc01d3cc6c2310f1d N w Bfam (hZ2.integrable one_le_two) hMv0 hVb hgb s
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- A function of the time alone is integrable over a window against the reference intensity. -/
theorem integrableOn_prod_of_time_complex {f : ℝ → ℂ} {t : ℝ}
    (hf : IntegrableOn f (Set.Ioc 0 t) volume) {A : Set E} (hAν : ν A ≠ ⊤) :
    IntegrableOn (fun q : ℝ × E => f q.1) (Set.Ioc (0 : ℝ) t ×ˢ A) (referenceIntensity ν) := by
  haveI : IsFiniteMeasure (ν.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hAν⟩
  have hI : Set.Ioc (0 : ℝ) t ∩ Set.Ici 0 = Set.Ioc 0 t :=
    Set.inter_eq_left.mpr fun x hx => le_of_lt hx.1
  rw [IntegrableOn, referenceIntensity, ← Measure.prod_restrict,
    Measure.restrict_restrict measurableSet_Ioc, hI]
  exact hf.comp_fst _
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

/-- The deterministic drift factor of the cell identity. -/
noncomputable def cellDrift (l : ℝ) (a b : ℝ) (s : ℝ) : ℝ :=
  -(l ^ 2) / 2 * ((Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s) ^ 2
end Reduced

end LevyStochCalc.Driver


