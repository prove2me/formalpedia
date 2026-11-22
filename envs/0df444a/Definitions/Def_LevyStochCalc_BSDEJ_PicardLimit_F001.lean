-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_PicardLimit_F001
-- name    : LevyStochCalc_BSDEJ_PicardLimit_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:10:40.011999+00:00
-- url     : https://prove2.me/theorems/4f69cb94-39d1-42b8-a71c-953b66244c54
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.PicardLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.PicardLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_DriftModification_F001
import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionBounds_F000
import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionContraction_F000
import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionNorm_F000
import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionNorm_F001
import Definitions.Def_LevyStochCalc_BSDEJ_PicardIteratesCauchy_F000
import Definitions.Def_LevyStochCalc_BSDEJ_PicardIteratesCauchy_F001
import Definitions.Def_LevyStochCalc_BSDEJ_PicardIteratesStep_F000
import Definitions.Def_SourceProof_869b93343dd8836d1387ab78
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.MonotoneConvergence

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The limit of the Picard iterates and existence of a solution

The Picard iterates of a backward equation with jumps are Cauchy for the energy of the value
process, for the energies of the diffusion coordinates and for the marked energy of the jump
integrand, so completeness of the admissible integrands produces an admissible limit triple
which the iterates approach in the exponentially weighted norm at the Young weight
`max 2 (24 L²)`. A further Picard step along the limit triple contracts that distance by `1/4`
against every iterate, so its output is at zero weighted distance from the limit triple; a
Lipschitz generator takes the same value along two triples agreeing almost everywhere on
`Ω × [0, T]`, so the output is its own Picard output and solves the equation.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.PicardOutput.congr_inputs` — a Picard output along one input
  triple is a Picard output along any input triple agreeing with it almost everywhere on the
  horizon.
* `LevyStochCalc.BSDEJ.Solves.exists_admissible_wNorm_limit` — an energy-Cauchy sequence of
  admissible triples converges in the weighted norm to an admissible triple.
* `LevyStochCalc.BSDEJ.Solves.exists_solvesBSDEJ` — a backward equation with jumps whose
  generator is Lipschitz and square integrable at the origin and whose terminal datum is square
  integrable has a solution.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Barles–Buckdahn–Pardoux, *BSDEs and integral-partial differential equations*, Stochastics 60
  (1997), §2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Truncation to the horizon -/

/-- The zero marked process is marked progressively measurable. -/
theorem markedProgressivelyMeasurable_zero (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    Probability.MarkedProgressivelyMeasurable ℱ
      fun (_ : Ω) (_ : ℝ) (_ : E) => (0 : ℝ) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have h : (fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun _ => (0 : ℝ)) p.2.1)
      = fun _ : Ω × ℝ × E => (0 : ℝ) := by
    funext p
    simp [Set.indicator_apply]
  rw [h]
  exact stronglyMeasurable_const
/-! ### Changing the input triple of a Picard step on a null set -/

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- A Lipschitz generator takes the same value on two jump arguments differing on a null set of
marks. -/
theorem generator_congr_of_lintegral_eq_zero {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s y : ℝ) (z : Fin d → ℝ) (u₁ u₂ : E → ℝ)
    (hu : ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν = 0) :
    f s y z u₁ = f s y z u₂ := by
  have h := hlip s y y z z u₁ u₂
  rw [hu, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
  simp only [sub_self, nnnorm_zero, ENNReal.coe_zero, add_zero, mul_zero,
    nonpos_iff_eq_zero, ENNReal.coe_eq_zero, nnnorm_eq_zero, sub_eq_zero] at h
  exact h
/-- The output of a Picard step along an input triple is the output of a Picard step along any
input triple agreeing with it almost everywhere on the horizon. -/
theorem PicardOutput.congr_inputs {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    {ξ : Ω → ℝ} {T : ℝ} {Y'₁ Y'₂ Y : ℝ → Ω → ℝ} {Z'₁ Z'₂ Z : ℝ → Ω → (Fin d → ℝ)}
    {U'₁ U'₂ U : ℝ → Ω → E → ℝ}
    (hY : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), Y'₁ p.2 p.1 = Y'₂ p.2 p.1)
    (hZ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), Z'₁ p.2 p.1 = Z'₂ p.2 p.1)
    (hU : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      ∫⁻ e, (‖U'₁ p.2 p.1 e - U'₂ p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν = 0)
    (h : PicardOutput D f ξ T Y'₁ Z'₁ U'₁ Y Z U) :
    PicardOutput D f ξ T Y'₂ Z'₂ U'₂ Y Z U := by
  have hfeq : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      f p.2 (Y'₁ p.2 p.1) (Z'₁ p.2 p.1) (U'₁ p.2 p.1)
        = f p.2 (Y'₂ p.2 p.1) (Z'₂ p.2 p.1) (U'₂ p.2 p.1) := by
    filter_upwards [hY, hZ, hU] with p h1 h2 h3
    rw [h1, h2]
    exact generator_congr_of_lintegral_eq_zero hlip _ _ _ _ _ h3
  refine
    { Z_meas := h.Z_meas, Z_prog := h.Z_prog, Z_vanish := h.Z_vanish, Z_sq := h.Z_sq,
      U_meas := h.U_meas, U_prog := h.U_prog, U_vanish := h.U_vanish, U_sq := h.U_sq,
      Y_meas := h.Y_meas, Y_adapted := h.Y_adapted, Y_cadlag := h.Y_cadlag,
      Y_terminal := h.Y_terminal, Y_sup := h.Y_sup, eqn := ?_ }
  intro t ht
  filter_upwards [h.eqn t ht, Measure.ae_ae_of_ae_prod hfeq] with ω h1 h2
  have hint : (∫ s in Set.Icc t T, f s (Y'₁ s ω) (Z'₁ s ω) (U'₁ s ω))
      = ∫ s in Set.Icc t T, f s (Y'₂ s ω) (Z'₂ s ω) (U'₂ s ω) :=
    integral_congr_ae
      (ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc ht.1 le_rfl) h2)
  rw [h1, hint]
/-! ### Triples at zero weighted distance -/

omit [IsProbabilityMeasure P] in
/-- The energy density of a triple of vanishing weighted norm vanishes almost everywhere on the
horizon. -/
theorem ae_density_eq_zero_of_wNorm_eq_zero {β T : ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (h : wNorm P ν β T Y Z U = 0) :
    ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      density ν Y Z U p.1 p.2 = 0 := by
  have hm : Measurable fun p : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (β * p.2)) * density ν Y Z U p.1 p.2 := by
    refine Measurable.mul ?_ (measurable_uncurry_density hYm hZm hUm)
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul measurable_snd))
  have hprod : ∫⁻ p, ENNReal.ofReal (Real.exp (β * p.2)) * density ν Y Z U p.1 p.2
      ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) = 0 := by
    rw [lintegral_prod _ hm.aemeasurable]
    exact h
  filter_upwards [(lintegral_eq_zero_iff' hm.aemeasurable).mp hprod] with p hp
  have hw : ENNReal.ofReal (Real.exp (β * p.2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  exact (mul_eq_zero.mp hp).resolve_left hw
omit [IsProbabilityMeasure P] in
/-- Two triples at zero weighted distance agree almost everywhere on the horizon, the jump
integrands up to a null set of marks. -/
theorem ae_eq_of_wNorm_sub_eq_zero {β T : ℝ} {Y₁ Y₂ : ℝ → Ω → ℝ}
    {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)} {U₁ U₂ : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y₁ s ω - Y₂ s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z₁ s ω j - Z₂ s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U₁ p.2.1 p.1 p.2.2 - U₂ p.2.1 p.1 p.2.2)
    (h : wNorm P ν β T (fun t ω => Y₁ t ω - Y₂ t ω) (fun t ω => Z₁ t ω - Z₂ t ω)
      (fun t ω e => U₁ t ω e - U₂ t ω e) = 0) :
    (∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), Y₁ p.2 p.1 = Y₂ p.2 p.1)
      ∧ (∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), Z₁ p.2 p.1 = Z₂ p.2 p.1)
      ∧ ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
          ∫⁻ e, (‖U₁ p.2 p.1 e - U₂ p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν = 0 := by
  classical
  have hd := ae_density_eq_zero_of_wNorm_eq_zero hYm hZm hUm h
  refine ⟨?_, ?_, ?_⟩ <;> filter_upwards [hd] with p hp <;> rw [density] at hp <;>
    obtain ⟨hab, hc⟩ := add_eq_zero.mp hp
  · obtain ⟨ha, -⟩ := add_eq_zero.mp hab
    have h0 : (‖Y₁ p.2 p.1 - Y₂ p.2 p.1‖₊ : ℝ≥0∞) = 0 :=
      (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp ha
    simpa [sub_eq_zero] using h0
  · obtain ⟨-, hb⟩ := add_eq_zero.mp hab
    funext j
    have hj := Finset.sum_eq_zero_iff.mp hb j (Finset.mem_univ j)
    have h0 : (‖Z₁ p.2 p.1 j - Z₂ p.2 p.1 j‖₊ : ℝ≥0∞) = 0 :=
      (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hj
    simpa [sub_eq_zero] using h0
  · exact hc
/-- A quantity dominated along a null sequence by the factor-two triangle bound vanishes. -/
theorem eq_zero_of_le_two_mul_of_tendsto (x : ℝ≥0∞) {W : ℕ → ℝ≥0∞}
    (hW : Tendsto W atTop (𝓝 0))
    (h : ∀ n, x ≤ 2 * (4⁻¹ * W n) + 2 * W (n + 1)) : x = 0 := by
  have h1 : Tendsto (fun n => (4 : ℝ≥0∞)⁻¹ * W n) atTop (𝓝 ((4 : ℝ≥0∞)⁻¹ * 0)) :=
    ENNReal.Tendsto.const_mul hW (Or.inr (by simp))
  rw [mul_zero] at h1
  have h2 : Tendsto (fun n => (2 : ℝ≥0∞) * ((4 : ℝ≥0∞)⁻¹ * W n)) atTop
      (𝓝 ((2 : ℝ≥0∞) * 0)) := ENNReal.Tendsto.const_mul h1 (Or.inr (by simp))
  rw [mul_zero] at h2
  have h3 : Tendsto (fun n => W (n + 1)) atTop (𝓝 0) := hW.comp (tendsto_add_atTop_nat 1)
  have h4 : Tendsto (fun n => (2 : ℝ≥0∞) * W (n + 1)) atTop (𝓝 ((2 : ℝ≥0∞) * 0)) :=
    ENNReal.Tendsto.const_mul h3 (Or.inr (by simp))
  rw [mul_zero] at h4
  have h5 : Tendsto (fun n => 2 * (4⁻¹ * W n) + 2 * W (n + 1)) atTop (𝓝 0) := by
    simpa using h2.add h4
  exact nonpos_iff_eq_zero.mp (ge_of_tendsto' h5 h)
/-! ### The weighted norm against the energies -/

omit [SigmaFinite ν] in
/-- The weighted norm of a triple on the horizon is at most `e^{βT}` times the sum of the
energy of the value, of the energies of the diffusion coordinates and of the marked energy of
the jump integrand. -/
theorem wNorm_le_energies {β T : ℝ} (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j)) :
    wNorm P ν β T Y Z U ≤ ENNReal.ofReal (Real.exp (β * T)) *
      (Brownian.Ito.energy P T (fun ω s => Y s ω)
        + (∑ j, Brownian.Ito.energy P T (fun ω s => Z s ω j))
        + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e)) := by
  rw [wNorm_eq_lintegral_density, ← _root_.Prove2MeSourceProof.h_869b93343dd8836d1387ab78 hYm hZm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left hs.2 hβ))) le_rfl
/-! ### The limit of an energy-Cauchy sequence of admissible triples -/

section Limit

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {T : ℝ}

end Limit

/-! ### The fixed point of the Picard step -/

section FixedPoint

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ}

end FixedPoint

/-! ### Existence of a solution -/

end LevyStochCalc.BSDEJ.Solves


