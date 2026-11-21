-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CellComplex_F000
-- name    : LevyStochCalc_Driver_CellComplex_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:33:57.689529+00:00
-- url     : https://prove2.me/theorems/925403db-9329-4da6-a90e-82e80622bba4
-- title:
--   Source declarations: LevyStochCalc.Driver.CellComplex
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CellComplex. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPCell_F000
import Definitions.Def_LevyStochCalc_Driver_CellGronwallIdentity_F000
import Definitions.Def_LevyStochCalc_Driver_CellGronwallIdentity_F001
import Definitions.Def_SourceProof_486c6c984ea8e12bbaaf74ce

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The cell lemma for a complex bounded factor

The grid induction carries the joint character of the earlier cells as the bounded factor, and
that character is complex. Since the weight stays real, the pairing splits into the real and
imaginary parts of the factor, and the vanishing of the mean against the complex factor is the
vanishing of both real means.
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

section Complex

variable (N : PoissonRandomMeasure P ν)

/-- The pairing of a real weight and a complex bounded factor with the product of the Brownian
and Poisson cell characters. -/
noncomputable def cellPairingC (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (Z : Ω → ℝ) (V : Ω → ℂ)
    (l : ℝ) (X : ℝ → Ω → ℝ) (s : ℝ) : ℂ :=
  ∫ ω, ((Z ω : ℝ) : ℂ) * V ω
    * (Complex.exp (Complex.I * ((l * X s ω : ℝ) : ℂ)) * charAt N w Bfam s ω) ∂P
variable {Z : Ω → ℝ} {V : Ω → ℂ} {Mv l : ℝ} {X : ℝ → Ω → ℝ}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The character factor of the cell pairing is unimodular. -/
theorem norm_cellFactor (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (l : ℝ) (X : ℝ → Ω → ℝ) (s : ℝ)
    (ω : Ω) :
    ‖Complex.exp (Complex.I * ((l * X s ω : ℝ) : ℂ)) * charAt N w Bfam s ω‖ = 1 := by
  rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, charAt,
    Complex.norm_exp_I_mul_ofReal, one_mul]
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The integrand of the cell pairing against a bounded real factor is integrable. -/
theorem integrable_cellFactor (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) (hZ1 : Integrable Z P) {U : Ω → ℝ}
    (hUm : Measurable U) (hUb : ∀ ω, |U ω| ≤ Mv) {s : ℝ} (hXs : Measurable (X s)) :
    Integrable (fun ω => ((Z ω * U ω : ℝ) : ℂ)
      * (Complex.exp (Complex.I * ((l * X s ω : ℝ) : ℂ)) * charAt N w Bfam s ω)) P := by
  have hZU : Integrable (fun ω => Z ω * U ω) P :=
    (hZ1.bdd_mul (c := Mv) hUm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hUb ω)).congr
      (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  have hm : AEStronglyMeasurable
      (fun ω => Complex.exp (Complex.I * ((l * X s ω : ℝ) : ℂ)) * charAt N w Bfam s ω) P :=
    ((Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (measurable_const.mul hXs)))).mul
      (measurable_charAt N w hBm s)).aestronglyMeasurable
  exact (hZU.ofReal.bdd_mul (c := 1) hm
    (Filter.Eventually.of_forall fun ω =>
      le_of_eq (norm_cellFactor N w Bfam l X s ω))).congr
    (Filter.Eventually.of_forall fun ω => mul_comm _ _)
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The complex pairing is the pairing against the real part plus `i` times the pairing against
the imaginary part. -/
theorem cellPairingC_eq_parts (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) (hZ1 : Integrable Z P) (hVm : Measurable V)
    (hVb : ∀ ω, ‖V ω‖ ≤ Mv) {s : ℝ} (hXs : Measurable (X s)) :
    cellPairingC N w Bfam Z V l X s
      = cellPairing N w Bfam Z (fun ω => (V ω).re) l X s
        + Complex.I * cellPairing N w Bfam Z (fun ω => (V ω).im) l X s := by
  have hre := integrable_cellFactor (l := l) (X := X) N w hBm hZ1
    (U := fun ω => (V ω).re) (Complex.measurable_re.comp hVm)
    (fun ω => (Complex.abs_re_le_norm _).trans (hVb ω)) hXs
  have him := integrable_cellFactor (l := l) (X := X) N w hBm hZ1
    (U := fun ω => (V ω).im) (Complex.measurable_im.comp hVm)
    (fun ω => (Complex.abs_im_le_norm _).trans (hVb ω)) hXs
  have hpt : ∀ ω, ((Z ω : ℝ) : ℂ) * V ω
      * (Complex.exp (Complex.I * ((l * X s ω : ℝ) : ℂ)) * charAt N w Bfam s ω)
      = ((Z ω * (V ω).re : ℝ) : ℂ)
          * (Complex.exp (Complex.I * ((l * X s ω : ℝ) : ℂ)) * charAt N w Bfam s ω)
        + Complex.I * (((Z ω * (V ω).im : ℝ) : ℂ)
          * (Complex.exp (Complex.I * ((l * X s ω : ℝ) : ℂ)) * charAt N w Bfam s ω)) := by
    intro ω
    have hV : V ω = ((V ω).re : ℂ) + ((V ω).im : ℂ) * Complex.I :=
      (Complex.re_add_im (V ω)).symm
    conv_lhs => rw [hV]
    push_cast
    ring
  rw [cellPairingC]
  simp_rw [hpt]
  rw [integral_add hre (him.const_mul Complex.I), MeasureTheory.integral_const_mul]
  rfl
omit [IsProbabilityMeasure P] in
/-- A real weight has mean zero against a complex factor exactly when it has mean zero against
both of its real parts. -/
theorem integral_re_im_eq_zero (hZ1 : Integrable Z P) (hVm : Measurable V)
    (hVb : ∀ ω, ‖V ω‖ ≤ Mv) (hZV : ∫ ω, ((Z ω : ℝ) : ℂ) * V ω ∂P = 0) :
    (∫ ω, Z ω * (V ω).re ∂P = 0) ∧ (∫ ω, Z ω * (V ω).im ∂P = 0) := by
  have hbd : ∀ (U : Ω → ℝ), Measurable U → (∀ ω, |U ω| ≤ Mv) →
      Integrable (fun ω => Z ω * U ω) P := fun U hUm hUb =>
    (hZ1.bdd_mul (c := Mv) hUm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hUb ω)).congr
      (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  have hre := hbd _ (Complex.measurable_re.comp hVm)
    (fun ω => (Complex.abs_re_le_norm _).trans (hVb ω))
  have him := hbd _ (Complex.measurable_im.comp hVm)
    (fun ω => (Complex.abs_im_le_norm _).trans (hVb ω))
  have hofReal : ∀ f : Ω → ℝ,
      ∫ ω, ((f ω : ℝ) : ℂ) ∂P = ((∫ ω, f ω ∂P : ℝ) : ℂ) := fun _ => integral_ofReal
  have hpt : ∀ ω, ((Z ω : ℝ) : ℂ) * V ω
      = ((Z ω * (V ω).re : ℝ) : ℂ) + Complex.I * ((Z ω * (V ω).im : ℝ) : ℂ) := by
    intro ω
    conv_lhs => rw [(Complex.re_add_im (V ω)).symm]
    push_cast
    ring
  rw [funext hpt, integral_add hre.ofReal (him.ofReal.const_mul _),
    MeasureTheory.integral_const_mul, hofReal, hofReal] at hZV
  constructor
  · simpa using congrArg Complex.re hZV
  · simpa using congrArg Complex.im hZV
end Complex

section Cell

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

include hℱN hℱW in
/-- **The mixed cell lemma for a complex factor.** With a real square-integrable weight
orthogonal to every Itô integral and every compensated integral, and of mean zero against a
bounded complex factor measurable before the cell, the pairing with the product of the Brownian
and Poisson cell characters vanishes throughout the cell. -/
theorem cellPairingC_eq_zero
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (ha : 0 ≤ a) (hab : a < b) (l : ℝ)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℂ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, ‖V ω‖ ≤ Mv) (hZV : ∫ ω, ((Z ω : ℝ) : ℂ) * V ω ∂P = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) b, cellPairingC N w Bfam Z V l X t = 0 := by
  have hVm : Measurable V := (hVa.mono (ℱ.le a)).measurable
  obtain ⟨hre0, him0⟩ := integral_re_im_eq_zero (hZ2.integrable one_le_two) hVm hVb hZV
  intro t ht
  rw [cellPairingC_eq_parts N w hBm (hZ2.integrable one_le_two) hVm hVb (hXbase.measurable t),
    _root_.Prove2MeSourceProof.h_486c6c984ea8e12bbaaf74ce N hℱN W hℱW hXbase hX0 ha hab l hT hbT hA hAν w hBm hBsub he₀
      hZ2 hZito hZcomp (Complex.continuous_re.comp_stronglyMeasurable hVa) hMv0
      (fun ω => (Complex.abs_re_le_norm _).trans (hVb ω)) hre0 t ht,
    _root_.Prove2MeSourceProof.h_486c6c984ea8e12bbaaf74ce N hℱN W hℱW hXbase hX0 ha hab l hT hbT hA hAν w hBm hBsub he₀
      hZ2 hZito hZcomp (Complex.continuous_im.comp_stronglyMeasurable hVa) hMv0
      (fun ω => (Complex.abs_im_le_norm _).trans (hVb ω)) him0 t ht]
  simp
end Cell

end LevyStochCalc.Driver


