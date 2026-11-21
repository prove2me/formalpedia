-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CellGronwallPairing_F000
-- name    : LevyStochCalc_Driver_CellGronwallPairing_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:15:18.971802+00:00
-- url     : https://prove2.me/theorems/d60a471e-80e7-448c-a865-51a3b0fbc56a
-- title:
--   Source declarations: LevyStochCalc.Driver.CellGronwallPairing
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CellGronwallPairing. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellFubini_F000
import Definitions.Def_LevyStochCalc_Driver_CellFubini_F001
import Definitions.Def_LevyStochCalc_Poisson_CharacterGronwall_F000
import Definitions.Def_LevyStochCalc_Poisson_CharacterMarkFactor_F001

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

/-- A bounded measurable function on a probability space is square integrable. -/
theorem memLp_two_of_bound {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) {C : ℝ}
    (hb : ∀ ω, |f ω| ≤ C) : MemLp f 2 P :=
  MemLp.of_bound hf C (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hb ω)
/-- The pairing of the weight and the bounded factor with a trigonometric function of the
Brownian increment against a real component of the Poisson character. -/
noncomputable def cellPart (P : Measure Ω) (Z V : Ω → ℝ) (l : ℝ) (X : ℝ → Ω → ℝ)
    (g : ℝ → ℝ) (Y : ℝ → Ω → ℝ) (s : ℝ) : ℝ :=
  ∫ ω, Z ω * V ω * (g (l * X s ω) * Y s ω) ∂P
/-- The integrand of a real cell pairing is integrable. -/
theorem integrable_cellPart {Z V : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hVm : Measurable V)
    {Mv : ℝ} (hVb : ∀ ω, |V ω| ≤ Mv) {l : ℝ} {X : ℝ → Ω → ℝ} {g : ℝ → ℝ}
    (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1) {Y : ℝ → Ω → ℝ} {s : ℝ}
    (hXs : Measurable (X s)) (hYs : Measurable (Y s)) (hYb : ∀ ω, |Y s ω| ≤ 1) :
    Integrable (fun ω => Z ω * V ω * (g (l * X s ω) * Y s ω)) P := by
  refine integrable_mul_bdd_mul hZ2 (memLp_two_of_bound (C := 1 * 1) ?_ ?_) hVm hVb
  · exact ((hgc.measurable.comp (measurable_const.mul hXs)).mul hYs).aestronglyMeasurable
  · intro ω
    rw [abs_mul]
    exact mul_le_mul (hgb _) (hYb ω) (abs_nonneg _) zero_le_one
variable (N : PoissonRandomMeasure P ν)

/-- The pairing of the weight and the bounded factor with the product of the Brownian and Poisson
cell characters. -/
noncomputable def cellPairing (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (Z V : Ω → ℝ)
    (l : ℝ) (X : ℝ → Ω → ℝ) (s : ℝ) : ℂ :=
  ∫ ω, ((Z ω * V ω : ℝ) : ℂ)
    * (Complex.exp (Complex.I * ((l * X s ω : ℝ) : ℂ)) * charAt N w Bfam s ω) ∂P
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The complex pairing is the combination of the four real pairings. -/
theorem cellPairing_eq_parts (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {Z V : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hVm : Measurable V) {Mv : ℝ} (hVb : ∀ ω, |V ω| ≤ Mv) {l : ℝ} {X : ℝ → Ω → ℝ}
    {s : ℝ} (hXs : Measurable (X s)) :
    cellPairing N w Bfam Z V l X s
      = ((cellPart P Z V l X Real.cos (fun s ω => (charAt N w Bfam s ω).re) s
            - cellPart P Z V l X Real.sin (fun s ω => (charAt N w Bfam s ω).im) s : ℝ) : ℂ)
        + Complex.I * ((cellPart P Z V l X Real.cos (fun s ω => (charAt N w Bfam s ω).im) s
            + cellPart P Z V l X Real.sin (fun s ω => (charAt N w Bfam s ω).re) s : ℝ)
          : ℂ) := by
  have hcm : Measurable fun ω => (charAt N w Bfam s ω).re :=
    Complex.measurable_re.comp (measurable_charAt N w hBm s)
  have him : Measurable fun ω => (charAt N w Bfam s ω).im :=
    Complex.measurable_im.comp (measurable_charAt N w hBm s)
  have hcb : ∀ ω, |(charAt N w Bfam s ω).re| ≤ 1 := fun ω => abs_charAt_re_le N w s ω
  have hib : ∀ ω, |(charAt N w Bfam s ω).im| ≤ 1 := fun ω => abs_charAt_im_le N w s ω
  have h1 := integrable_cellPart hZ2 hVm hVb (l := l) (X := X) Real.continuous_cos
    Real.abs_cos_le_one (Y := fun s ω => (charAt N w Bfam s ω).re) hXs hcm hcb
  have h2 := integrable_cellPart hZ2 hVm hVb (l := l) (X := X) Real.continuous_sin
    Real.abs_sin_le_one (Y := fun s ω => (charAt N w Bfam s ω).im) hXs him hib
  have h3 := integrable_cellPart hZ2 hVm hVb (l := l) (X := X) Real.continuous_cos
    Real.abs_cos_le_one (Y := fun s ω => (charAt N w Bfam s ω).im) hXs him hib
  have h4 := integrable_cellPart hZ2 hVm hVb (l := l) (X := X) Real.continuous_sin
    Real.abs_sin_le_one (Y := fun s ω => (charAt N w Bfam s ω).re) hXs hcm hcb
  have hpt : ∀ ω, ((Z ω * V ω : ℝ) : ℂ)
      * (Complex.exp (Complex.I * ((l * X s ω : ℝ) : ℂ)) * charAt N w Bfam s ω)
      = ((Z ω * V ω * (Real.cos (l * X s ω) * (charAt N w Bfam s ω).re)
            - Z ω * V ω * (Real.sin (l * X s ω) * (charAt N w Bfam s ω).im) : ℝ) : ℂ)
        + Complex.I * ((Z ω * V ω * (Real.cos (l * X s ω) * (charAt N w Bfam s ω).im)
            + Z ω * V ω * (Real.sin (l * X s ω) * (charAt N w Bfam s ω).re) : ℝ) : ℂ) := by
    intro ω
    have hre : (Complex.exp (Complex.I * ((l * X s ω : ℝ) : ℂ))).re = Real.cos (l * X s ω) :=
      exp_I_mul_ofReal_re _
    have hiim : (Complex.exp (Complex.I * ((l * X s ω : ℝ) : ℂ))).im = Real.sin (l * X s ω) :=
      exp_I_mul_ofReal_im _
    refine Complex.ext ?_ ?_ <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hre, hiim,
        zero_mul, mul_zero, zero_add, add_zero, sub_zero, one_mul] <;>
      ring
  have hofReal : ∀ f : Ω → ℝ,
      ∫ ω, ((f ω : ℝ) : ℂ) ∂P = ((∫ ω, f ω ∂P : ℝ) : ℂ) :=
    fun _ => integral_ofReal
  rw [cellPairing]
  simp_rw [hpt]
  rw [integral_add (h1.sub h2).ofReal ((h3.add h4).ofReal.const_mul _),
    MeasureTheory.integral_const_mul, hofReal, hofReal, integral_sub h1 h2, integral_add h3 h4]
  rfl
end Parts

section Half

variable (N : PoissonRandomMeasure P ν)

/-- The pairing of the weight, the bounded factor and a trigonometric function of the Brownian
increment with the Poisson cell character. -/
noncomputable def cellHalf (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (Z V : Ω → ℝ) (l : ℝ)
    (X : ℝ → Ω → ℝ) (g : ℝ → ℝ) (s : ℝ) : ℂ :=
  ∫ ω, ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charAt N w Bfam s ω ∂P
variable {Z V : Ω → ℝ} {Mv l : ℝ} {X : ℝ → Ω → ℝ} {g : ℝ → ℝ}

/-- The weight, the bounded factor and a trigonometric function of the Brownian increment are
jointly integrable. -/
theorem integrable_weight (hZ2 : MemLp Z 2 P) (hVm : Measurable V) (hVb : ∀ ω, |V ω| ≤ Mv)
    (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1) {s : ℝ} (hXs : Measurable (X s)) :
    Integrable (fun ω => Z ω * V ω * g (l * X s ω)) P :=
  integrable_mul_bdd_mul hZ2
    (memLp_two_of_bound (C := 1)
      (hgc.measurable.comp (measurable_const.mul hXs)).aestronglyMeasurable
      (fun _ => hgb _)) hVm hVb
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The real cell pairings are the real and imaginary parts of the complex half. -/
theorem cellPart_eq_cellHalf_re (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) (hZ2 : MemLp Z 2 P) (hVm : Measurable V)
    (hVb : ∀ ω, |V ω| ≤ Mv) (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1) {s : ℝ}
    (hXs : Measurable (X s)) :
    cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).re) s
      = (cellHalf N w Bfam Z V l X g s).re := by
  have hint := integrable_mul_charAt N w hBm
    (integrable_weight (l := l) (X := X) hZ2 hVm hVb hgc hgb hXs) s
  have hre : ∫ ω, (((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charAt N w Bfam s ω).re ∂P
      = (∫ ω, ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charAt N w Bfam s ω ∂P).re :=
    integral_re hint
  rw [cellPart, cellHalf, ← hre]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The real cell pairings are the real and imaginary parts of the complex half. -/
theorem cellPart_eq_cellHalf_im (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) (hZ2 : MemLp Z 2 P) (hVm : Measurable V)
    (hVb : ∀ ω, |V ω| ≤ Mv) (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1) {s : ℝ}
    (hXs : Measurable (X s)) :
    cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).im) s
      = (cellHalf N w Bfam Z V l X g s).im := by
  have hint := integrable_mul_charAt N w hBm
    (integrable_weight (l := l) (X := X) hZ2 hVm hVb hgc hgb hXs) s
  have him : ∫ ω, (((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charAt N w Bfam s ω).im ∂P
      = (∫ ω, ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charAt N w Bfam s ω ∂P).im :=
    integral_im hint
  rw [cellPart, cellHalf, ← him]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  ring
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

end Reduced

end LevyStochCalc.Driver


