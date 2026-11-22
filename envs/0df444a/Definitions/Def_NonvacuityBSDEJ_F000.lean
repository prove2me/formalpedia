-- Prove2me | Definitions.Def_NonvacuityBSDEJ_F000
-- name    : NonvacuityBSDEJ_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:44:05.220859+00:00
-- url     : https://prove2.me/theorems/bb4add21-3137-4076-96ad-f57e08baff0d
-- title:
--   Source declarations: NonvacuityBSDEJ
-- statement:
--   Source-preserving extracted declarations from NonvacuityBSDEJ. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Solves_F000
import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F000
import Definitions.Def_LevyStochCalc_Driver_Existence_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIntegrandComplete_F000
import Definitions.Def_NonvacuityDrivers_F002
import Definitions.Def_SourceProof_01c878d1e4a6afef88ed0c78
import Definitions.Def_SourceProof_650b7098f620aa4310e44016
import Definitions.Def_SourceProof_8d3a16d297de60304d079b21

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A backward equation with jumps over a Lévy driver, with an identity generator

The scalar backward equation

  `Y_t = W_1 + ∫_t^1 Y_s ds − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

driven by a Lévy driver with one Brownian coordinate and a Poisson random measure of intensity
`dt ⊗ δ_1` on `[0, ∞) × ℝ`. The generator is `f(s, y, z, u) = y`, Lipschitz with constant `1`
for the `L²(ν)` distance in the jump variable and vanishing at the origin; the horizon is
`T = 1`; the terminal datum is the Brownian value `W_1`, square integrable and measurable for
the augmented joint filtration at time `1`.

## Main statements

* `exists_solvesBSDEJ_generator_id` — the equation has a solution triple over every such
  driver.
* `solvesBSDEJ_generator_id_not_zero` — the value process of a solution of the equation above
  is not almost surely `0` at the horizon, so the solution triple is not the zero triple.
* `exists_unique_solvesBSDEJ_generator_id` — the hypotheses of
  `LevyStochCalc.BSDEJ.Solves.exists_unique_solvesBSDEJ` hold for this equation on a
  probability space carrying such a driver, and its conclusion is not degenerate: existence, the
  value process not almost surely `0` at the horizon, and uniqueness.

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

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The data of the equation -/

/-- The generator `f(s, y, z, u) = y` obeys the `L²(ν)` Lipschitz bound with constant `1`. -/
theorem lipschitz_generator_id (_s y₁ y₂ : ℝ) (z₁ z₂ : Fin 1 → ℝ) (u₁ u₂ : ℝ → ℝ) :
    (‖y₁ - y₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal 1 *
      ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
        + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂Measure.dirac (1 : ℝ)) ^ (1 / 2 : ℝ)) := by
  rw [ENNReal.ofReal_one, one_mul]
  exact le_self_add.trans le_self_add
/-- The generator `f(s, y, z, u) = y` is measurable in `(s, y, z)` at each fixed jump
variable. -/
theorem measurable_generator_id (_u : ℝ → ℝ) :
    Measurable fun r : ℝ × ℝ × (Fin 1 → ℝ) => r.2.1 :=
  measurable_snd.fst
/-- The generator `f(s, y, z, u) = y` vanishes at the origin, so its square has zero integral
on every window. -/
theorem lintegral_generator_id_zero (T : ℝ) :
    ∫⁻ _s in Set.Icc (0 : ℝ) T, (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 = 0 := by
  simp
/-- The value at time `1` of the first coordinate of a one-dimensional Brownian motion is
square integrable. -/
theorem memLp_brownian_one (W : Brownian.Multidim.MultidimBrownianMotion P 1) :
    MemLp (fun ω => (W.W 0).W 1 ω) 2 P :=
  _root_.Prove2MeSourceProof.h_650b7098f620aa4310e44016 (W.W 0) 1
/-- The value at time `1` of the first coordinate of the Brownian motion of a Lévy driver is
strongly measurable for the augmented joint filtration at time `1`. -/
theorem aestronglyMeasurable_brownian_one_augJoint
    (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    AEStronglyMeasurable[augJoint D 1] (fun ω => (D.W.W 0).W 1 ω) P := by
  have hnat : StronglyMeasurable[Brownian.Martingale.naturalFiltration (D.W.W 0) 1]
      ((D.W.W 0).W 1) :=
    MeasureTheory.Filtration.stronglyAdapted_natural
      (u := (D.W.W 0).W) (fun t => ((D.W.W 0).measurable_eval t).stronglyMeasurable) 1
  have hle : Brownian.Martingale.naturalFiltration (D.W.W 0) 1 ≤ augJoint D 1 :=
    ((D.W.naturalFiltration_coord_le 0 1).trans (D.naturalFiltration_brownian_le 1)).trans
      (Brownian.le_augFiltration D.filtration P 1)
  exact (hnat.mono hle).aestronglyMeasurable
/-! ### Existence for the equation -/

/-- The backward equation with generator `f(s, y, z, u) = y`, terminal datum `W_1` and horizon
`1` has a solution triple over every Lévy driver with one Brownian coordinate and jump
intensity `δ_1`. -/
theorem exists_solvesBSDEJ_generator_id (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    ∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin 1 → ℝ)) (U : ℝ → Ω → ℝ → ℝ),
      SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U := by
  have hf0 : ∫⁻ _s in Set.Icc (0 : ℝ) 1, (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 < ⊤ := by
    rw [lintegral_generator_id_zero]
    exact ENNReal.zero_lt_top
  exact _root_.Prove2MeSourceProof.h_8d3a16d297de60304d079b21 D (fun _ y _ _ => y) (L := 1) zero_le_one measurable_generator_id
    lipschitz_generator_id one_pos hf0 (memLp_brownian_one D.W)
    (aestronglyMeasurable_brownian_one_augJoint D)
/-! ### The terminal value of a solution -/

/-- The value process of a solution of the backward equation with generator
`f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1` is not almost surely `0` at the
horizon. -/
theorem solvesBSDEJ_generator_id_not_zero {D : LevyDriver P 1 (Measure.dirac (1 : ℝ))}
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin 1 → ℝ)} {U : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U) :
    ¬ (Y 1 =ᵐ[P] fun _ => (0 : ℝ)) := fun hzero =>
  brownian_not_ae_zero (D.W.W 0) one_pos
    ((h.Y_terminal zero_le_one).symm.trans hzero)
/-! ### The witness -/

/-- **The hypotheses of the existence and uniqueness theorem for backward equations with jumps
are satisfied by an equation with a nonzero generator.** On some probability space there are a
Lévy driver with one Brownian coordinate and jump intensity `δ_1`, and a solution triple of the
backward equation with generator `f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1`;
every solution triple of that equation has a value process that is not almost surely `0` at the
horizon, and any two solution triples agree almost surely at every time of the horizon in the
value process and with vanishing energy of the difference in the two integrands. -/
theorem exists_unique_solvesBSDEJ_generator_id :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))),
      (∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin 1 → ℝ)) (U : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U) ∧
        (∀ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin 1 → ℝ)) (U : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U →
            ¬ (Y 1 =ᵐ[P] fun _ => (0 : ℝ))) ∧
        ∀ (Y₁ Y₂ : ℝ → Ω → ℝ) (Z₁ Z₂ : ℝ → Ω → (Fin 1 → ℝ)) (U₁ U₂ : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y₁ Z₁ U₁ →
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y₂ Z₂ U₂ →
            (∀ t ∈ Set.Icc (0 : ℝ) 1, Y₁ t =ᵐ[P] Y₂ t) ∧
            (∀ j, Brownian.Ito.energy P 1 (fun ω s => Z₁ s ω j - Z₂ s ω j) = 0) ∧
            Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
              (fun ω s e => U₁ s ω e - U₂ s ω e) = 0 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (1 : ℝ))
  have hf0 : ∫⁻ _s in Set.Icc (0 : ℝ) 1, (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 < ⊤ := by
    rw [lintegral_generator_id_zero]
    exact ENNReal.zero_lt_top
  obtain ⟨hex, huniq⟩ := _root_.Prove2MeSourceProof.h_01c878d1e4a6afef88ed0c78 D (fun _ y _ _ => y) (L := 1) zero_le_one
    measurable_generator_id lipschitz_generator_id one_pos hf0 (memLp_brownian_one D.W)
    (aestronglyMeasurable_brownian_one_augJoint D)
  exact ⟨Ω, inferInstance, P, inferInstance, D, hex,
    fun _ _ _ h => solvesBSDEJ_generator_id_not_zero h, huniq⟩
end LevyStochCalc.Examples.Nonvacuity


