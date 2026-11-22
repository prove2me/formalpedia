-- Prove2me | Definitions.Def_NonvacuityBSDEJZ_F001
-- name    : NonvacuityBSDEJZ_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:44:42.563619+00:00
-- url     : https://prove2.me/theorems/babd1d29-59c4-49e4-a5c1-935e5f494be4
-- title:
--   Source declarations: NonvacuityBSDEJZ
-- statement:
--   Source-preserving extracted declarations from NonvacuityBSDEJZ. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F000
import Definitions.Def_LevyStochCalc_Driver_Existence_F000
import Definitions.Def_NonvacuityBSDEJZ_F000
import Definitions.Def_SourceProof_01c878d1e4a6afef88ed0c78
import Definitions.Def_SourceProof_520dd8b482424f67cc040622
import Definitions.Def_SourceProof_650b7098f620aa4310e44016

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A backward equation with jumps whose Brownian integrand carries positive energy

The scalar backward equation

  `Y_t = W_1 − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

driven by a Lévy driver with one Brownian coordinate and a Poisson random measure of intensity
`dt ⊗ δ_1` on `[0, ∞) × ℝ`. The generator vanishes, the horizon is `T = 1` and the terminal
datum is the Brownian value `W_1`, so the value process is the Brownian motion itself, the
Brownian integrand is the indicator `1_{(0, 1]}` of the horizon and the jump integrand is `0`.

## Main statements

* `exists_solvesBSDEJ_windowZ` — the equation is solved by a continuous modification of the
  Brownian motion together with the integrand pair `(1_{(0, 1]}, 0)`.
* `energy_windowZ` — the energy of `1_{(0, 1]}` on `[0, 1]` is `1`.
* `energy_eq_one_of_solvesBSDEJ` — every solution triple of the equation has Brownian integrand
  of energy `1` on `[0, 1]`.
* `exists_solvesBSDEJ_energy_ne_zero` — on a probability space carrying such a driver the
  equation has a solution triple and every solution triple has Brownian integrand of nonzero
  energy.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Delong, *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer 2013,
  §4.1.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.BSDEJ.Solves
open LevyStochCalc.Driver (LevyDriver)

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The integrands of the equation -/

section Fields

variable (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))

end Fields

/-! ### A solution triple with the indicator integrand -/

/-! ### The energy of the Brownian integrand -/

/-- The energy of `windowZ` on the horizon `[0, 1]` is `1`. -/
theorem energy_windowZ (i : Fin 1) :
    Brownian.Ito.energy P 1 (fun ω s => windowZ Ω s ω i) = 1 := by
  have hpt : ∀ (ω : Ω) (s : ℝ), (‖windowZ Ω s ω i‖₊ : ℝ≥0∞) ^ 2
      = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ≥0∞)) s := by
    intro ω s
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1 <;> simp [windowZ, Brownian.Ito.indIoc, hs]
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) 1,
      (‖windowZ Ω s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume = 1 := by
    intro ω
    simp only [hpt]
    rw [lintegral_indicator measurableSet_Ioc, lintegral_one,
      Measure.restrict_apply_univ, Measure.restrict_apply' measurableSet_Icc]
    rw [Set.inter_eq_left.mpr Set.Ioc_subset_Icc_self, Real.volume_Ioc]
    simp
  rw [Brownian.Ito.energy]
  simp [hinner]
/-- The vanishing generator is measurable in `(s, y, z)` at each fixed jump variable. -/
theorem measurable_generator_zero (_u : ℝ → ℝ) :
    Measurable fun _r : ℝ × ℝ × (Fin 1 → ℝ) => (0 : ℝ) := measurable_const
/-- The vanishing generator obeys the `L²(ν)` Lipschitz bound with constant `0`. -/
theorem lipschitz_generator_zero (_s y₁ y₂ : ℝ) (z₁ z₂ : Fin 1 → ℝ) (u₁ u₂ : ℝ → ℝ) :
    (‖(0 : ℝ) - (0 : ℝ)‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal 0 *
      ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
        + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂Measure.dirac (1 : ℝ)) ^ (1 / 2 : ℝ)) := by
  simp
/-- The Brownian integrand of a solution of the backward equation with vanishing generator,
terminal datum `W_1` and horizon `1` has energy `1` on `[0, 1]`. -/
theorem energy_eq_one_of_solvesBSDEJ (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U') :
    Brownian.Ito.energy P 1 (fun ω s => Z' s ω 0) = 1 := by
  obtain ⟨Y, hY, -⟩ := _root_.Prove2MeSourceProof.h_520dd8b482424f67cc040622 D
  have hξ2 : MemLp (fun ω => (D.W.W 0).W 1 ω) 2 P :=
    _root_.Prove2MeSourceProof.h_650b7098f620aa4310e44016 (D.W.W 0) 1
  have hξm : AEStronglyMeasurable[augJoint D 1] (fun ω => (D.W.W 0).W 1 ω) P := by
    have hnat : StronglyMeasurable[Brownian.Martingale.naturalFiltration (D.W.W 0) 1]
        ((D.W.W 0).W 1) :=
      MeasureTheory.Filtration.stronglyAdapted_natural
        (u := (D.W.W 0).W) (fun t => ((D.W.W 0).measurable_eval t).stronglyMeasurable) 1
    have hle : Brownian.Martingale.naturalFiltration (D.W.W 0) 1 ≤ augJoint D 1 :=
      ((D.W.naturalFiltration_coord_le 0 1).trans (D.naturalFiltration_brownian_le 1)).trans
        (Brownian.le_augFiltration D.filtration P 1)
    exact (hnat.mono hle).aestronglyMeasurable
  have hf0 : ∫⁻ _s in Set.Icc (0 : ℝ) 1, (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 < ⊤ := by simp
  obtain ⟨-, huniq⟩ := _root_.Prove2MeSourceProof.h_01c878d1e4a6afef88ed0c78 D (fun _ _ _ _ => (0 : ℝ)) (L := 0) le_rfl
    measurable_generator_zero lipschitz_generator_zero zero_lt_one hf0 hξ2 hξm
  have hzero := (huniq Y' Y Z' (windowZ Ω) U' (fun _ _ _ => (0 : ℝ)) h hY).2.1 0
  have hmZ : Measurable (Function.uncurry fun ω s => Z' s ω 0) := h.Z_meas 0
  have hmW : Measurable (Function.uncurry fun (ω : Ω) s => windowZ Ω s ω 0) := windowZ_meas 0
  have hmd : Measurable (Function.uncurry fun ω s => Z' s ω 0 - windowZ Ω s ω 0) := hmZ.sub hmW
  rw [Brownian.Ito.energy_eq_eLpNorm_sq hmd 1] at hzero
  have h0 : eLpNorm (fun p : Ω × ℝ => Z' p.2 p.1 0 - windowZ Ω p.2 p.1 0) 2
      (Brownian.Ito.energyMeasure P 1) = 0 := (pow_eq_zero_iff two_ne_zero).mp hzero
  have hae := (eLpNorm_eq_zero_iff hmd.aestronglyMeasurable (by norm_num)).mp h0
  have hae2 : (fun p : Ω × ℝ => Z' p.2 p.1 0)
      =ᵐ[Brownian.Ito.energyMeasure P 1] fun p : Ω × ℝ => windowZ Ω p.2 p.1 0 := by
    filter_upwards [hae] with p hp
    have hp' : Z' p.2 p.1 0 - windowZ Ω p.2 p.1 0 = 0 := hp
    linarith
  rw [Brownian.Ito.energy_eq_eLpNorm_sq hmZ 1, eLpNorm_congr_ae hae2,
    ← Brownian.Ito.energy_eq_eLpNorm_sq hmW 1]
  exact energy_windowZ 0
/-! ### The witness -/

/-- On some probability space there are a Lévy driver with one Brownian coordinate and jump
intensity `δ_1`, and a solution triple of the backward equation with vanishing generator,
terminal datum `W_1` and horizon `1` whose Brownian integrand is `1_{(0, 1]}`, of energy `1` on
the horizon; the Brownian integrand of every solution triple of that equation has nonzero energy
on the horizon. -/
theorem exists_solvesBSDEJ_energy_ne_zero :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))),
      (∃ Y : ℝ → Ω → ℝ,
          SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (fun ω => (D.W.W 0).W 1 ω) 1 Y (windowZ Ω)
              (fun _ _ _ => (0 : ℝ)) ∧
            ∀ t, Y t =ᵐ[P] fun ω => (D.W.W 0).W t ω) ∧
        Brownian.Ito.energy P 1 (fun ω s => windowZ Ω s ω 0) = 1 ∧
        ∀ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin 1 → ℝ)) (U' : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U' →
            Brownian.Ito.energy P 1 (fun ω s => Z' s ω 0) ≠ 0 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (1 : ℝ))
  exact ⟨Ω, inferInstance, P, inferInstance, D, _root_.Prove2MeSourceProof.h_520dd8b482424f67cc040622 D, energy_windowZ 0,
    fun _ _ _ h => by rw [energy_eq_one_of_solvesBSDEJ D h]; exact one_ne_zero⟩
end LevyStochCalc.Examples.Nonvacuity


