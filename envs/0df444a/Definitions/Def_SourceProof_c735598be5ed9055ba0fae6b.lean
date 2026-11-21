-- Prove2me | Definitions.Def_SourceProof_c735598be5ed9055ba0fae6b
-- name    : SourceProof_c735598be5ed9055ba0fae6b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:17:01.083053+00:00
-- url     : https://prove2.me/theorems/2951a82a-d6b9-410a-9a36-d00c71f0a674
-- title:
--   LevyStochCalc source module: SourceProof_c735598be5ed9055ba0fae6b
-- statement:
--   The original source theorem `LevyStochCalc.Driver.cellPairing_identity` comes from the `LevyStochCalc.Driver.CellGronwallIdentity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_6f82a8f1a241e4a2ebbba77b
import Definitions.Def_SourceProof_a13d8bf499df852f51383d04
import Definitions.Def_SourceProof_d70b081240f0d1c36022214e
import Definitions.Def_SourceProof_fb131f2d05ee8dfbbc8425e0

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

theorem _root_.Prove2MeSourceProof.h_c735598be5ed9055ba0fae6b
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
    cellPairing N w Bfam Z V l X t
      = cellPairing N w Bfam Z V l X 0
        + ∫ s in Set.Ioc (0 : ℝ) t,
            (cellDrift l a b s : ℂ) * cellPairing N w Bfam Z V l X s ∂volume
        + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            markFactor w Bfam q * cellPairing N w Bfam Z V l X q.1
            ∂(referenceIntensity ν) := by
  have hVm : Measurable V := (hVa.mono (ℱ.le a)).measurable
  have hXm : Measurable (Function.uncurry fun ω s => X s ω) := hXbase.measurable_uncurry
  have hBsub0 : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha le_rfl) le_rfl)
  have hgc' : Continuous fun x : ℝ => -l * Real.sin (l * x) :=
    continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hgs' : Continuous fun x : ℝ => l * Real.cos (l * x) :=
    continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hmgc := LevyStochCalc.Brownian.Ito.measurable_trig_integrand hXbase hgc'
  have hpgc := LevyStochCalc.Brownian.Ito.progressivelyMeasurable_trig_integrand hXbase hgc'
  have hqgc : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖(-l * Real.sin (l * X s ω)) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun T' hT' => LevyStochCalc.Brownian.Ito.lintegral_sq_trig_integrand_lt_top (P := P) (X := X) (a := a) (b := b)
      (LevyStochCalc.Analysis.abs_neg_mul_sin_scaled_le l) (abs_nonneg l) T' hT'
  have hmgs := LevyStochCalc.Brownian.Ito.measurable_trig_integrand hXbase hgs'
  have hpgs := LevyStochCalc.Brownian.Ito.progressivelyMeasurable_trig_integrand hXbase hgs'
  have hqgs : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖(l * Real.cos (l * X s ω)) * LevyStochCalc.Brownian.Ito.indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun T' hT' => LevyStochCalc.Brownian.Ito.lintegral_sq_trig_integrand_lt_top (P := P) (X := X) (a := a) (b := b)
      (LevyStochCalc.Analysis.abs_mul_cos_scaled_le l) (abs_nonneg l) T' hT'
  have hC := _root_.Prove2MeSourceProof.h_a13d8bf499df852f51383d04 N hℱN W hℱW hXbase hX0 ha hab l Real.continuous_cos
    Real.abs_cos_le_one hgc' (LevyStochCalc.Analysis.abs_neg_mul_sin_scaled_le l)
    hmgc hpgc hqgc
    (fun T' hT' => _root_.Prove2MeSourceProof.h_6f82a8f1a241e4a2ebbba77b zero_le_one (LevyStochCalc.Brownian.Ito.indIoc_le_one a b) hXbase l
      hmgc hpgc hqgc hT')
    hT hbT hA hAν w hBm hBsub he₀ hZ2 hZito hZcomp hVa hMv0 hVb ht htT
  have hS := _root_.Prove2MeSourceProof.h_a13d8bf499df852f51383d04 N hℱN W hℱW hXbase hX0 ha hab l Real.continuous_sin
    Real.abs_sin_le_one hgs' (LevyStochCalc.Analysis.abs_mul_cos_scaled_le l)
    hmgs hpgs hqgs
    (fun T' hT' => _root_.Prove2MeSourceProof.h_fb131f2d05ee8dfbbc8425e0 zero_le_one (LevyStochCalc.Brownian.Ito.indIoc_le_one a b) hXbase l
      hmgs hpgs hqgs hT')
    hT hbT hA hAν w hBm hBsub he₀ hZ2 hZito hZcomp hVa hMv0 hVb ht htT
  have hcm : Measurable fun s : ℝ => ((LevyStochCalc.Driver.cellDrift l a b s : ℝ) : ℂ) := by
    refine Complex.measurable_ofReal.comp ?_
    exact measurable_const.mul ((measurable_const.indicator measurableSet_Ioc).pow_const 2)
  have hKt : ∀ h : ℝ → ℝ, Continuous h → (∀ x, |h x| ≤ 1) →
      IntegrableOn (fun s => LevyStochCalc.Driver.cellHalf N w Bfam Z V l X h s) (Set.Ioc (0 : ℝ) t) volume := by
    intro h hhc hhb
    exact (LevyStochCalc.Driver.integrableOn_cellHalf N hℱN w hBm hA hAν hT hbT hBsub0 he₀ hZ2 hVm hMv0 hVb
      hhc hhb hXm T).mono_set
      (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl htT))
  have hdI : ∀ h : ℝ → ℝ, Continuous h → (∀ x, |h x| ≤ 1) →
      IntegrableOn (fun s => (LevyStochCalc.Driver.cellDrift l a b s : ℂ) * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X h s)
        (Set.Ioc (0 : ℝ) t) volume := fun h hhc hhb =>
    (hKt h hhc hhb).bdd_mul (c := l ^ 2 / 2) hcm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact _root_.Prove2MeSourceProof.h_fd4cb731b719ac626f4a8f6e l a b s)
  have hWI : ∀ h : ℝ → ℝ, Continuous h → (∀ x, |h x| ≤ 1) →
      IntegrableOn (fun q : ℝ × E => LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X h q.1)
        (Set.Ioc (0 : ℝ) t ×ˢ A) (LevyStochCalc.Poisson.referenceIntensity ν) := fun h hhc hhb =>
    (LevyStochCalc.Driver.integrableOn_prod_of_time_complex (hKt h hhc hhb) hAν).bdd_mul (c := 2)
      (LevyStochCalc.Poisson.measurable_markFactor w hBm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => _root_.Prove2MeSourceProof.h_36517bdd7fab28ddf5fce6bc w Bfam q)
  have hsplit : ∀ s, LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s
      = LevyStochCalc.Driver.cellHalf N w Bfam Z V l X Real.cos s
        + Complex.I * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X Real.sin s := fun s =>
    _root_.Prove2MeSourceProof.h_d70b081240f0d1c36022214e N w hBm hZ2 hVm hVb (hXbase.measurable s)
  have hD : ∫ s in Set.Ioc (0 : ℝ) t,
        (LevyStochCalc.Driver.cellDrift l a b s : ℂ) * LevyStochCalc.Driver.cellPairing N w Bfam Z V l X s ∂volume
      = (∫ s in Set.Ioc (0 : ℝ) t,
          (LevyStochCalc.Driver.cellDrift l a b s : ℂ) * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X Real.cos s ∂volume)
        + Complex.I * ∫ s in Set.Ioc (0 : ℝ) t,
          (LevyStochCalc.Driver.cellDrift l a b s : ℂ) * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X Real.sin s ∂volume := by
    simp_rw [hsplit, mul_add, ← mul_assoc, mul_comm (LevyStochCalc.Driver.cellDrift l a b _ : ℂ) Complex.I,
      mul_assoc]
    rw [integral_add (hdI Real.cos Real.continuous_cos Real.abs_cos_le_one)
      ((hdI Real.sin Real.continuous_sin Real.abs_sin_le_one).const_mul Complex.I),
      MeasureTheory.integral_const_mul]
  have hW : ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
        LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellPairing N w Bfam Z V l X q.1 ∂(LevyStochCalc.Poisson.referenceIntensity ν)
      = (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X Real.cos q.1
          ∂(LevyStochCalc.Poisson.referenceIntensity ν))
        + Complex.I * ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          LevyStochCalc.Poisson.markFactor w Bfam q * LevyStochCalc.Driver.cellHalf N w Bfam Z V l X Real.sin q.1
          ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
    simp_rw [hsplit, mul_add, ← mul_assoc, mul_comm (LevyStochCalc.Poisson.markFactor w Bfam _) Complex.I, mul_assoc]
    rw [integral_add (hWI Real.cos Real.continuous_cos Real.abs_cos_le_one)
      ((hWI Real.sin Real.continuous_sin Real.abs_sin_le_one).const_mul Complex.I),
      MeasureTheory.integral_const_mul]
  rw [hsplit t, hsplit 0, hC, hS, hD, hW]
  ring
end Identity

end LevyStochCalc.Driver


