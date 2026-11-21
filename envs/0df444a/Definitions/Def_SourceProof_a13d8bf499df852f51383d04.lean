-- Prove2me | Definitions.Def_SourceProof_a13d8bf499df852f51383d04
-- name    : SourceProof_a13d8bf499df852f51383d04
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:39:02.894382+00:00
-- url     : https://prove2.me/theorems/d6118d5f-b3ca-4ba7-af76-27f7a7f22078
-- title:
--   LevyStochCalc source module: SourceProof_a13d8bf499df852f51383d04
-- statement:
--   The original source theorem `LevyStochCalc.Driver.cellHalf_identity` comes from the `LevyStochCalc.Driver.CellGronwallIdentity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_CellGronwallIdentity_F000
import Definitions.Def_SourceProof_36517bdd7fab28ddf5fce6bc
import Definitions.Def_SourceProof_50f5f4bad7c1b77cae226627
import Definitions.Def_SourceProof_dc278d467d0d24865b42c6df
import Definitions.Def_SourceProof_fd4cb731b719ac626f4a8f6e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cell identity and the Grönwall bound for the cell pairing

The real and the imaginary cell identities recombine into an integral equation for the pairing of
a square-integrable weight and a bounded factor with the product of the Brownian cell character
`e^{i l X_s}` and the Poisson cell character: the pairing at a time in the cell is its value at
the origin plus a deterministic drift term over the elapsed times and a mark-factor term over the
window. The Grönwall estimate that follows forces the pairing to vanish throughout the cell when
the weight is orthogonal to every Itô integral and every compensated integral and has mean zero
against the bounded factor.
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

section Identity

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ} {ι : Type*} [Fintype ι]

include hℱN hℱW in

theorem _root_.Prove2MeSourceProof.h_a13d8bf499df852f51383d04
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
    cellHalf N w Bfam Z V l X g t
      = cellHalf N w Bfam Z V l X g 0
        + ∫ s in Set.Ioc (0 : ℝ) t,
            (cellDrift l a b s : ℂ) * cellHalf N w Bfam Z V l X g s ∂volume
        + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            markFactor w Bfam q * cellHalf N w Bfam Z V l X g q.1
            ∂(referenceIntensity ν) := by
  have hVm : Measurable V := (hVa.mono (ℱ.le a)).measurable
  have hXm : Measurable (Function.uncurry fun ω s => X s ω) := hXbase.measurable_uncurry
  have hBsub0 : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha le_rfl) le_rfl)
  have hBsub' : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha hbT.le) le_rfl)
  have hWm : MeasurableSet (Set.Ioc (0 : ℝ) t ×ˢ A) := measurableSet_Ioc.prod hA
  have hKI : IntegrableOn (fun s => LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g s) (Set.Icc (0 : ℝ) T) volume :=
    LevyStochCalc.Driver.integrableOn_cellHalf N hℱN w hBm hA hAν hT hbT hBsub0 he₀ hZ2 hVm hMv0 hVb hgc hgb hXm T
  have hKt : IntegrableOn (fun s => LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g s) (Set.Ioc (0 : ℝ) t) volume :=
    hKI.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl htT))
  have hcm : Measurable fun s : ℝ => ((LevyStochCalc.Driver.cellDrift l a b s : ℝ) : ℂ) := by
    refine Complex.measurable_ofReal.comp ?_
    exact measurable_const.mul ((measurable_const.indicator measurableSet_Ioc).pow_const 2)
  have hdI : IntegrableOn
      (fun s => (LevyStochCalc.Driver.cellDrift l a b s : ℂ) * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g s)
      (Set.Ioc (0 : ℝ) t) volume :=
    hKt.bdd_mul (c := l ^ 2 / 2) hcm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact _root_.Prove2MeSourceProof.h_fd4cb731b719ac626f4a8f6e l a b s)
  have hWI : IntegrableOn
      (fun q : ℝ × E => LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g q.1)
      (Set.Ioc (0 : ℝ) t ×ˢ A) (LevyStochCalc.Poisson.referenceIntensity ν) :=
    (LevyStochCalc.Driver.integrableOn_prod_of_time_complex hKt hAν).bdd_mul (c := 2)
      (LevyStochCalc.Poisson.measurable_markFactor w hBm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => _root_.Prove2MeSourceProof.h_36517bdd7fab28ddf5fce6bc w Bfam q)
  have hPre : ∀ s, LevyStochCalc.Driver.cellPart P Z V l X g (fun s ω => (LevyStochCalc.Poisson.charAt N w Bfam s ω).re) s
      = (LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g s).re := fun s =>
    LevyStochCalc.Driver.cellPart_eq_cellHalf_re N w hBm hZ2 hVm hVb hgc hgb (hXbase.measurable s)
  have hPim : ∀ s, LevyStochCalc.Driver.cellPart P Z V l X g (fun s ω => (LevyStochCalc.Poisson.charAt N w Bfam s ω).im) s
      = (LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g s).im := fun s =>
    LevyStochCalc.Driver.cellPart_eq_cellHalf_im N w hBm hZ2 hVm hVb hgc hgb (hXbase.measurable s)
  have hJre : Set.EqOn
      (fun q : ℝ × E => ∫ ω, Z ω * V ω * (g (l * X q.1 ω) * LevyStochCalc.Poisson.charRe N w Bfam A T ω q.1 q.2) ∂P)
      (fun q : ℝ × E => (LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g q.1).re)
      (Set.Ioc (0 : ℝ) t ×ˢ A) := by
    rintro ⟨s, e⟩ ⟨hs, he⟩
    exact _root_.Prove2MeSourceProof.h_50f5f4bad7c1b77cae226627 N hℱN w hBm hA hAν hBsub' hZ2 hVm hVb hgc hgb hs.1
      (hs.2.trans htT) he (hXbase.measurable s)
  have hJim : Set.EqOn
      (fun q : ℝ × E => ∫ ω, Z ω * V ω * (g (l * X q.1 ω) * LevyStochCalc.Poisson.charIm N w Bfam A T ω q.1 q.2) ∂P)
      (fun q : ℝ × E => (LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g q.1).im)
      (Set.Ioc (0 : ℝ) t ×ˢ A) := by
    rintro ⟨s, e⟩ ⟨hs, he⟩
    exact _root_.Prove2MeSourceProof.h_dc278d467d0d24865b42c6df N hℱN w hBm hA hAν hBsub' hZ2 hVm hVb hgc hgb hs.1
      (hs.2.trans htT) he (hXbase.measurable s)
  have hre := LevyStochCalc.Driver.cellPart_identity_re N hℱN W hℱW hXbase hX0 ha hab l hgc hgb hg'c hg'b
    hmg hpg hqg hito hT hbT hA hAν w hBm hBsub he₀ hZ2 hZito hZcomp hVa hMv0 hVb ht htT
  have him := LevyStochCalc.Driver.cellPart_identity_im N hℱN W hℱW hXbase hX0 ha hab l hgc hgb hg'c hg'b
    hmg hpg hqg hito hT hbT hA hAν w hBm hBsub he₀ hZ2 hZito hZcomp hVa hMv0 hVb ht htT
  rw [setIntegral_congr_fun hWm hJre] at hre
  rw [setIntegral_congr_fun hWm hJim] at him
  simp only [hPre] at hre
  simp only [hPim] at him
  have hdre : (∫ s in Set.Ioc (0 : ℝ) t,
        (LevyStochCalc.Driver.cellDrift l a b s : ℂ) * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g s ∂volume).re
      = ∫ s in Set.Ioc (0 : ℝ) t,
          LevyStochCalc.Driver.cellDrift l a b s * (LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g s).re ∂volume := by
    have h : ∫ s in Set.Ioc (0 : ℝ) t,
          ((LevyStochCalc.Driver.cellDrift l a b s : ℂ) * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g s).re ∂volume
        = (∫ s in Set.Ioc (0 : ℝ) t,
          (LevyStochCalc.Driver.cellDrift l a b s : ℂ) * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g s ∂volume).re := integral_re hdI
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hdim : (∫ s in Set.Ioc (0 : ℝ) t,
        (LevyStochCalc.Driver.cellDrift l a b s : ℂ) * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g s ∂volume).im
      = ∫ s in Set.Ioc (0 : ℝ) t,
          LevyStochCalc.Driver.cellDrift l a b s * (LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g s).im ∂volume := by
    have h : ∫ s in Set.Ioc (0 : ℝ) t,
          ((LevyStochCalc.Driver.cellDrift l a b s : ℂ) * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g s).im ∂volume
        = (∫ s in Set.Ioc (0 : ℝ) t,
          (LevyStochCalc.Driver.cellDrift l a b s : ℂ) * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g s ∂volume).im := integral_im hdI
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hWre : (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
        LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g q.1 ∂(LevyStochCalc.Poisson.referenceIntensity ν)).re
      = ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          (LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g q.1).re
          ∂(LevyStochCalc.Poisson.referenceIntensity ν) := (integral_re hWI).symm
  have hWim : (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
        LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g q.1 ∂(LevyStochCalc.Poisson.referenceIntensity ν)).im
      = ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          (LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X g q.1).im
          ∂(LevyStochCalc.Poisson.referenceIntensity ν) := (integral_im hWI).symm
  refine Complex.ext ?_ ?_
  · rw [Complex.add_re, Complex.add_re, hdre, hWre]
    exact hre
  · rw [Complex.add_im, Complex.add_im, hdim, hWim]
    exact him
end Identity

end LevyStochCalc.Driver


