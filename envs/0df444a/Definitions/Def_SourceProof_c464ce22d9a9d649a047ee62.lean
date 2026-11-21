-- Prove2me | Definitions.Def_SourceProof_c464ce22d9a9d649a047ee62
-- name    : SourceProof_c464ce22d9a9d649a047ee62
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:25:40.35996+00:00
-- url     : https://prove2.me/theorems/5bf3a2ad-1132-4ede-86a1-342dd4d328a4
-- title:
--   LevyStochCalc source module: SourceProof_c464ce22d9a9d649a047ee62
-- statement:
--   The original source theorem `LevyStochCalc.Driver.norm_cellPairing_le` comes from the `LevyStochCalc.Driver.CellGronwallIdentity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_c735598be5ed9055ba0fae6b

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

theorem _root_.Prove2MeSourceProof.h_c464ce22d9a9d649a047ee62
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (ha : 0 ≤ a) (hab : a < b) (l : ℝ)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ‖cellPairing N w Bfam Z V l X t‖
      ≤ ‖cellPairing N w Bfam Z V l X 0‖
        + (l ^ 2 / 2 + 2 * (ν A).toReal)
          * ∫ s in Set.Ioc (0 : ℝ) t, ‖cellPairing N w Bfam Z V l X s‖ ∂volume := by
  have hVm : Measurable V := (hVa.mono (ℱ.le a)).measurable
  have hXm : Measurable (Function.uncurry fun ω s => X s ω) := hXbase.measurable_uncurry
  have hBsub0 : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha le_rfl) le_rfl)
  have hcm : Measurable fun s : ℝ => ((LevyStochCalc.Driver.cellDrift l a b s : ℝ) : ℂ) := by
    refine Complex.measurable_ofReal.comp ?_
    exact measurable_const.mul ((measurable_const.indicator measurableSet_Ioc).pow_const 2)
  have hKt : ∀ h : ℝ → ℝ, Continuous h → (∀ x, |h x| ≤ 1) →
      IntegrableOn (fun s => LevyStochCalc.Driver.cellHalf N w Bfam Z V l X h s) (Set.Ioc (0 : ℝ) t) volume := by
    intro h hhc hhb
    exact (LevyStochCalc.Driver.integrableOn_cellHalf N hℱN w hBm hA hAν hT hbT hBsub0 he₀ hZ2 hVm hMv0 hVb
      hhc hhb hXm T).mono_set
      (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl htT))
  have hsplit : ∀ s, LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s
      = LevyStochCalc.Driver.cellHalf N w Bfam Z V l X Real.cos s
        + Complex.I * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X Real.sin s := fun s =>
    _root_.Prove2MeSourceProof.h_d70b081240f0d1c36022214e N w hBm hZ2 hVm hVb (hXbase.measurable s)
  have hUt : IntegrableOn (fun s => LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s)
      (Set.Ioc (0 : ℝ) t) volume := by
    have hc := hKt Real.cos Real.continuous_cos Real.abs_cos_le_one
    have hs := hKt Real.sin Real.continuous_sin Real.abs_sin_le_one
    exact (hc.add (hs.const_mul Complex.I)).congr
      (Filter.Eventually.of_forall fun s => (hsplit s).symm)
  have hUn : IntegrableOn (fun s => ‖LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s‖)
      (Set.Ioc (0 : ℝ) t) volume := hUt.norm
  have hdI : IntegrableOn
      (fun s => (LevyStochCalc.Driver.cellDrift l a b s : ℂ) * LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s)
      (Set.Ioc (0 : ℝ) t) volume :=
    hUt.bdd_mul (c := l ^ 2 / 2) hcm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact _root_.Prove2MeSourceProof.h_fd4cb731b719ac626f4a8f6e l a b s)
  have hWn : IntegrableOn (fun q : ℝ × E => ‖LevyStochCalc.Driver.cellPairing N w Bfam Z V l X q.1‖)
      (Set.Ioc (0 : ℝ) t ×ˢ A) (LevyStochCalc.Poisson.referenceIntensity ν) :=
    LevyStochCalc.Poisson.integrableOn_prod_of_time (ν := ν) hUn hAν
  have hWI : IntegrableOn
      (fun q : ℝ × E => LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellPairing N w Bfam Z V l X q.1)
      (Set.Ioc (0 : ℝ) t ×ˢ A) (LevyStochCalc.Poisson.referenceIntensity ν) :=
    (LevyStochCalc.Driver.integrableOn_prod_of_time_complex hUt hAν).bdd_mul (c := 2)
      (LevyStochCalc.Poisson.measurable_markFactor w hBm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => _root_.Prove2MeSourceProof.h_36517bdd7fab28ddf5fce6bc w Bfam q)
  have hDbound : ‖∫ s in Set.Ioc (0 : ℝ) t,
        (LevyStochCalc.Driver.cellDrift l a b s : ℂ) * LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s ∂volume‖
      ≤ l ^ 2 / 2 * ∫ s in Set.Ioc (0 : ℝ) t,
          ‖LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s‖ ∂volume := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    rw [← MeasureTheory.integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => norm_nonneg _)
      (hUn.const_mul _) (Filter.Eventually.of_forall fun s => ?_)
    change ‖(LevyStochCalc.Driver.cellDrift l a b s : ℂ) * LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s‖
        ≤ l ^ 2 / 2 * ‖LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (_root_.Prove2MeSourceProof.h_fd4cb731b719ac626f4a8f6e l a b s) (norm_nonneg _)
  have hWbound : ‖∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
        LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellPairing N w Bfam Z V l X q.1 ∂(LevyStochCalc.Poisson.referenceIntensity ν)‖
      ≤ 2 * (ν A).toReal * ∫ s in Set.Ioc (0 : ℝ) t,
          ‖LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s‖ ∂volume := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    have hstep : ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          ‖LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellPairing N w Bfam Z V l X q.1‖ ∂(LevyStochCalc.Poisson.referenceIntensity ν)
        ≤ ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          2 * ‖LevyStochCalc.Driver.cellPairing N w Bfam Z V l X q.1‖ ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => norm_nonneg _)
        (hWn.const_mul 2) (Filter.Eventually.of_forall fun q => ?_)
      change ‖LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellPairing N w Bfam Z V l X q.1‖
          ≤ 2 * ‖LevyStochCalc.Driver.cellPairing N w Bfam Z V l X q.1‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (_root_.Prove2MeSourceProof.h_36517bdd7fab28ddf5fce6bc w Bfam q) (norm_nonneg _)
    refine hstep.trans ?_
    rw [MeasureTheory.integral_const_mul, LevyStochCalc.Poisson.setIntegral_prod_of_time (ν := ν) hUn hAν, mul_assoc]
  calc ‖LevyStochCalc.Driver.cellPairing N w Bfam Z V l X t‖
      = ‖LevyStochCalc.Driver.cellPairing N w Bfam Z V l X 0
          + (∫ s in Set.Ioc (0 : ℝ) t,
              (LevyStochCalc.Driver.cellDrift l a b s : ℂ) * LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s ∂volume)
          + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
              LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellPairing N w Bfam Z V l X q.1
              ∂(LevyStochCalc.Poisson.referenceIntensity ν)‖ := by
        rw [← _root_.Prove2MeSourceProof.h_c735598be5ed9055ba0fae6b N hℱN W hℱW hXbase hX0 ha hab l hT hbT hA hAν w hBm
          hBsub he₀ hZ2 hZito hZcomp hVa hMv0 hVb ht htT]
    _ ≤ ‖LevyStochCalc.Driver.cellPairing N w Bfam Z V l X 0‖
          + ‖∫ s in Set.Ioc (0 : ℝ) t,
              (LevyStochCalc.Driver.cellDrift l a b s : ℂ) * LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s ∂volume‖
          + ‖∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
              LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellPairing N w Bfam Z V l X q.1
              ∂(LevyStochCalc.Poisson.referenceIntensity ν)‖ := norm_add₃_le
    _ ≤ ‖LevyStochCalc.Driver.cellPairing N w Bfam Z V l X 0‖
          + l ^ 2 / 2 * (∫ s in Set.Ioc (0 : ℝ) t,
              ‖LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s‖ ∂volume)
          + 2 * (ν A).toReal * ∫ s in Set.Ioc (0 : ℝ) t,
              ‖LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s‖ ∂volume := by
        gcongr
    _ = ‖LevyStochCalc.Driver.cellPairing N w Bfam Z V l X 0‖
          + (l ^ 2 / 2 + 2 * (ν A).toReal)
            * ∫ s in Set.Ioc (0 : ℝ) t,
              ‖LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s‖ ∂volume := by ring
end Identity

end LevyStochCalc.Driver


