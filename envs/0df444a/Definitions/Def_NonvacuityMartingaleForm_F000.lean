-- Prove2me | Definitions.Def_NonvacuityMartingaleForm_F000
-- name    : NonvacuityMartingaleForm_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:54:44.429823+00:00
-- url     : https://prove2.me/theorems/150bef56-841a-4683-9ce6-c1e8169b9761
-- title:
--   Source declarations: NonvacuityMartingaleForm
-- statement:
--   Source-preserving extracted declarations from NonvacuityMartingaleForm. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_MartingaleRepresentation_F000
import Definitions.Def_NonvacuityPRP_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The martingale form of the representation for a Brownian value

The value at time `1` of the single Brownian coordinate of a Lévy driver with unit mark
intensity `δ_1` is square integrable and measurable for the right-continuous joint filtration
at time `1`, hence the terminal value of a càdlàg square-integrable martingale for that
filtration starting from its mean `0`. That martingale differs at the two endpoints of the
horizon: its terminal second moment is `1` while its initial value vanishes.

## Main statements

* `stronglyMeasurable_brownian_one_jointRightCont` — the Brownian value `W_1` is strongly
  measurable for the right-continuous joint filtration at time `1`.
* `lintegral_sq_brownian_one_lt_top` — `W_1` has finite second moment.
* `exists_cadlagMartingale_brownian_one` — over a Lévy driver with one Brownian coordinate
  and unit mark intensity there is a càdlàg martingale `M` for the right-continuous joint
  filtration with `M_0 = 0`, `M_1 = W_1`, `M_1 ≠ M_0` almost surely and `𝔼‖M_1‖² = 1`.
* `exists_martingale_form_brownian_one` — the same statements on a probability space carrying
  such a driver.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Springer 1991, Theorem I.3.13.
* Jacod–Shiryaev, *Limit Theorems for Stochastic Processes*, 2nd ed., Springer 2003,
  Theorem III.4.34.
-/

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.Driver (LevyDriver)
open LevyStochCalc.BSDEJ.MartingaleRepresentation (jointFiltration)

universe u

section Inputs

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The value at time `1` of the Brownian coordinate of a Lévy driver with one Brownian
coordinate and unit mark intensity is strongly measurable for the right-continuous joint
filtration at time `1`. -/
theorem stronglyMeasurable_brownian_one_jointRightCont (D : LevyDriver P 1 markIntensity) :
    StronglyMeasurable[(jointFiltration D).seq 1] fun ω => (D.W.W 0).W 1 ω := by
  have hnat : StronglyMeasurable[Brownian.Martingale.naturalFiltration (D.W.W 0) 1]
      ((D.W.W 0).W 1) :=
    MeasureTheory.Filtration.stronglyAdapted_natural
      (u := (D.W.W 0).W) (fun t => ((D.W.W 0).measurable_eval t).stronglyMeasurable) 1
  have hle : Brownian.Martingale.naturalFiltration (D.W.W 0) 1 ≤ (jointFiltration D).seq 1 :=
    ((D.W.naturalFiltration_coord_le 0 1).trans (D.naturalFiltration_brownian_le 1)).trans
      (D.filtration.le_rightCont 1)
  exact hnat.mono hle
/-- The value at time `1` of a Brownian motion has finite second moment. -/
theorem lintegral_sq_brownian_one_lt_top (W : Brownian.BrownianMotion P) :
    ∫⁻ ω, (‖W.W 1 ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤ := by
  rw [_root_.Prove2MeSourceProof.h_bfc6836a0f0c399780ee75a6 W one_pos]
  exact ENNReal.ofReal_lt_top
end Inputs

section MartingaleForm

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Over a Lévy driver with one Brownian coordinate and unit mark intensity the Brownian value
at time `1` is the terminal value of a càdlàg martingale for the right-continuous joint
filtration which vanishes at time `0`, differs almost surely from its initial value and has
terminal second moment `1`. -/
theorem exists_cadlagMartingale_brownian_one (D : LevyDriver P 1 markIntensity) :
    ∃ M : ℝ → Ω → ℝ,
      Martingale M (jointFiltration D) P
        ∧ (∀ᵐ ω ∂P, ∀ t : ℝ,
            Filter.Tendsto (fun s => M s ω) (nhdsWithin t (Set.Ioi t)) (nhds (M t ω))
              ∧ ∃ L : ℝ,
                  Filter.Tendsto (fun s => M s ω) (nhdsWithin t (Set.Iio t)) (nhds L))
        ∧ (∀ᵐ ω ∂P, M 0 ω = 0)
        ∧ (∀ᵐ ω ∂P, M 1 ω = (D.W.W 0).W 1 ω)
        ∧ ¬ (M 1 =ᵐ[P] M 0)
        ∧ ∫⁻ ω, (‖M 1 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 := by
  obtain ⟨M, hmart, -, hcadlag, hinit, hterm⟩ :=
    LevyStochCalc.BSDEJ.MartingaleRepresentation.condExp_to_PRP_martingale_form D 1
      (fun ω => (D.W.W 0).W 1 ω) (stronglyMeasurable_brownian_one_jointRightCont D)
      (lintegral_sq_brownian_one_lt_top (D.W.W 0))
  have hzero : ∀ᵐ ω ∂P, M 0 ω = 0 := by
    filter_upwards [hinit] with ω hω
    rw [hω, integral_brownian_value_one_eq_zero (D.W.W 0)]
  refine ⟨M, hmart, hcadlag, hzero, hterm, ?_, ?_⟩
  · intro hcst
    refine brownian_not_ae_zero (D.W.W 0) one_pos ?_
    filter_upwards [hterm, hzero, hcst] with ω h1 h2 h3
    rw [← h1, h3, h2]
  · rw [lintegral_congr_ae (hterm.mono fun ω hω => by rw [hω]),
      _root_.Prove2MeSourceProof.h_bfc6836a0f0c399780ee75a6 (D.W.W 0) one_pos, ENNReal.ofReal_one]
end MartingaleForm

section Capstone

/-- Some probability space carries a Lévy driver with one Brownian coordinate and unit mark
intensity together with a càdlàg martingale for the right-continuous joint filtration that
vanishes at time `0`, equals the Brownian value at time `1`, differs almost surely from its
initial value and has terminal second moment `1`. -/
theorem exists_martingale_form_brownian_one :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 markIntensity) (M : ℝ → Ω → ℝ),
      Martingale M (jointFiltration D) P
        ∧ (∀ᵐ ω ∂P, ∀ t : ℝ,
            Filter.Tendsto (fun s => M s ω) (nhdsWithin t (Set.Ioi t)) (nhds (M t ω))
              ∧ ∃ L : ℝ,
                  Filter.Tendsto (fun s => M s ω) (nhdsWithin t (Set.Iio t)) (nhds L))
        ∧ (∀ᵐ ω ∂P, M 0 ω = 0)
        ∧ (∀ᵐ ω ∂P, M 1 ω = (D.W.W 0).W 1 ω)
        ∧ ¬ (M 1 =ᵐ[P] M 0)
        ∧ ∫⁻ ω, (‖M 1 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := Driver.LevyDriver.exists 1 ℝ markIntensity
  obtain ⟨M, hmart, hcadlag, hzero, hterm, hne, hsq⟩ := exists_cadlagMartingale_brownian_one D
  exact ⟨Ω, inferInstance, P, inferInstance, D, M, hmart, hcadlag, hzero, hterm, hne, hsq⟩
end Capstone

end LevyStochCalc.Examples.Nonvacuity


