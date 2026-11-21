-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_SmallJump_F000
-- name    : LevyStochCalc_Poisson_SmallJump_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:12:23.831171+00:00
-- url     : https://prove2.me/theorems/72d81899-223e-4990-8e08-d6d72474e89e
-- title:
--   Source declarations: LevyStochCalc.Poisson.SmallJump
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.SmallJump. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Compensated_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The compensated integral over a shrinking family of marks

Restricting an admissible integrand to a measurable set of marks keeps it admissible, and by the
Itô–Lévy isometry the `L²` size of its compensated integral is the energy carried by that set.
Along an antitone family of mark sets whose intersection is null, that energy vanishes by
dominated convergence on the intensity, so the compensated integrals tend to `0` in `L²`.

## Main statements

* `LevyStochCalc.Poisson.Compensated.markCut` — an integrand restricted to a set of marks.
* `LevyStochCalc.Poisson.Compensated.tendsto_lintegral_sq_stochasticIntegral_markCut` — the
  compensated integrals over a shrinking family of marks tend to `0` in `L²`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Cut

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- An integrand restricted to a measurable set of marks. -/
noncomputable def markCut (A : Set E) (φ : Ω → ℝ → E → ℝ) : Ω → ℝ → E → ℝ :=
  fun ω s e => A.indicator (fun _ => φ ω s e) e
omit [MeasurableSpace Ω] [MeasurableSpace E] in
@[simp] theorem markCut_apply (A : Set E) (φ : Ω → ℝ → E → ℝ) (ω : Ω) (s : ℝ) (e : E) :
    markCut A φ ω s e = A.indicator (fun _ => φ ω s e) e := rfl
theorem measurable_markCut {φ : Ω → ℝ → E → ℝ}
    (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) {A : Set E}
    (hA : MeasurableSet A) :
    Measurable fun p : Ω × ℝ × E => markCut A φ p.1 p.2.1 p.2.2 := by
  have hset : MeasurableSet {p : Ω × ℝ × E | p.2.2 ∈ A} := measurable_snd.snd hA
  have : (fun p : Ω × ℝ × E => markCut A φ p.1 p.2.1 p.2.2)
      = {p : Ω × ℝ × E | p.2.2 ∈ A}.indicator (fun p => φ p.1 p.2.1 p.2.2) := by
    funext p
    by_cases hp : p.2.2 ∈ A <;> simp [markCut, hp]
  rw [this]
  exact h_meas.indicator hset
omit [MeasurableSpace Ω] [MeasurableSpace E] in
theorem enorm_sq_markCut (A : Set E) (φ : Ω → ℝ → E → ℝ) (ω : Ω) (s : ℝ) (e : E) :
    (‖markCut A φ ω s e‖₊ : ℝ≥0∞) ^ 2
      = A.indicator (fun _ => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2) e := by
  by_cases hp : e ∈ A <;> simp [markCut, hp]
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
theorem sq_markCut {φ : Ω → ℝ → E → ℝ}
    (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) (A : Set E) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖markCut A φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  refine lt_of_le_of_lt ?_ (h_sq T hT)
  refine lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => ?_
  rw [enorm_sq_markCut]
  exact Set.indicator_le_self' (fun _ _ => zero_le) e
/-- The energy of a jointly measurable nonnegative kernel is measurable in the sample point. -/
theorem measurable_markEnergy {f : Ω → ℝ → E → ℝ≥0∞}
    (hf : Measurable fun p : Ω × ℝ × E => f p.1 p.2.1 p.2.2) (T : ℝ) :
    Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, f ω s e ∂ν ∂volume := by
  have hcurry : Measurable fun q : (Ω × ℝ) × E => f q.1.1 q.1.2 q.2 :=
    hf.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have h1 : Measurable fun p : Ω × ℝ => ∫⁻ e, f p.1 p.2 e ∂ν :=
    Measurable.lintegral_prod_right' (f := fun q : (Ω × ℝ) × E => f q.1.1 q.1.2 q.2) hcurry
  exact Measurable.lintegral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) T)) (f := fun q : Ω × ℝ => ∫⁻ e, f q.1 q.2 e ∂ν) h1
end Cut

section Tendsto

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

omit [IsProbabilityMeasure P] in
/-- The energy carried by a set of marks, with the mark integral outermost. -/
theorem lintegral_markCut_eq_setLIntegral {A : Set E} (hA : MeasurableSet A)
    (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) (T : ℝ) (ω : Ω) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖markCut A φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume
      = ∫⁻ e in A, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν := by
  have hcut : Measurable fun q : ℝ × E => (‖markCut A φ ω q.1 q.2‖₊ : ℝ≥0∞) ^ 2 := by
    have := (measurable_markCut h_meas hA).comp
      (measurable_const.prodMk (measurable_fst.prodMk measurable_snd) :
        Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))
    exact (this.nnnorm.coe_nnreal_ennreal).pow_const 2
  rw [lintegral_lintegral_swap hcut.aemeasurable, ← lintegral_indicator hA]
  refine lintegral_congr fun e => ?_
  by_cases he : e ∈ A
  · simp only [Set.indicator_of_mem he]
    exact lintegral_congr fun s => by simp [markCut, he]
  · simp only [Set.indicator_of_notMem he]
    exact (lintegral_congr fun s => by simp [markCut, he]).trans lintegral_zero
end Tendsto

end LevyStochCalc.Poisson.Compensated


