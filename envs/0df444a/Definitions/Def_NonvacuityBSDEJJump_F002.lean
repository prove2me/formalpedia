-- Prove2me | Definitions.Def_NonvacuityBSDEJJump_F002
-- name    : NonvacuityBSDEJJump_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:10:48.167495+00:00
-- url     : https://prove2.me/theorems/033fb0f7-64fe-416c-a829-b773bb541724
-- title:
--   Source declarations: NonvacuityBSDEJJump
-- statement:
--   Source-preserving extracted declarations from NonvacuityBSDEJJump. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_NonvacuityBSDEJJump_F001
import Definitions.Def_SourceProof_037e724daadf008d5ad1442c

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A backward equation with jumps whose jump integrand carries positive energy

The scalar backward equation

  `Y_t = ξ − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

driven by a Lévy driver with one Brownian coordinate and a Poisson random measure of intensity
`dt ⊗ δ_1` on `[0, ∞) × ℝ`. The generator vanishes, the horizon is `T = 1`, the jump integrand
is the window indicator `1_{(0, 1]}`, constant in the mark, and the terminal datum is its
compensated integral over the whole horizon, so the value process is that compensated integral
and the Brownian integrand is `0`.

## Main statements

* `exists_solvesBSDEJ_jump` — the equation is solved by a càdlàg version of the compensated
  integral of `1_{(0, 1]}` together with the integrand pair `(0, 1_{(0, 1]})`.
* `markedEnergy_jumpU` — the marked energy of `1_{(0, 1]}` on `[0, 1]` for the intensity `δ_1`
  is `1`.
* `markedEnergy_eq_one_of_solvesBSDEJ` — every solution triple of the equation has jump
  integrand of marked energy `1` on `[0, 1]`.
* `exists_solvesBSDEJ_markedEnergy_ne_zero` — on a probability space carrying such a driver the
  equation has a solution triple and every solution triple has jump integrand of nonzero marked
  energy on the horizon.

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

/-! ### The integrands of the equation -/

section Fields

variable (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))

end Fields

/-! ### A solution triple with a nonzero jump integrand -/

/-! ### The marked energy of the jump integrand -/

/-- The jump integrand of a solution of the backward equation with vanishing generator,
terminal datum the compensated integral of `1_{(0, 1]}` at time `1` and horizon `1` has marked
energy `1` on `[0, 1]`. -/
theorem markedEnergy_eq_one_of_solvesBSDEJ (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (jumpLeg D 1) 1 Y' Z' U') :
    Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
      (fun ω s e => U' s ω e) = 1 := by
  obtain ⟨Y, hY, -⟩ := _root_.Prove2MeSourceProof.h_037e724daadf008d5ad1442c D
  have hf0 : ∫⁻ _s in Set.Icc (0 : ℝ) 1, (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 < ⊤ := by simp
  obtain ⟨-, huniq⟩ := _root_.Prove2MeSourceProof.h_01c878d1e4a6afef88ed0c78 D (fun _ _ _ _ => (0 : ℝ)) (L := 0) le_rfl
    measurable_generator_zero lipschitz_generator_zero zero_lt_one hf0 (memLp_jumpLeg_one D)
    (aestronglyMeasurable_jumpLeg_one D)
  have hzero := (huniq Y' Y Z' (zeroZ Ω) U' (jumpU Ω) h hY).2.2
  have hmU : Measurable fun p : Ω × ℝ × ℝ => U' p.2.1 p.1 p.2.2 := h.U_meas
  have hmJ : Measurable fun p : Ω × ℝ × ℝ => jumpU Ω p.2.1 p.1 p.2.2 := jumpU_meas
  have hmd : Measurable fun p : Ω × ℝ × ℝ =>
      U' p.2.1 p.1 p.2.2 - jumpU Ω p.2.1 p.1 p.2.2 := hmU.sub hmJ
  rw [Poisson.Compensated.markedEnergy_eq_eLpNorm_sq
    (φ := fun ω s e => U' s ω e - jumpU Ω s ω e) hmd 1] at hzero
  have h0 : eLpNorm (fun p : Ω × ℝ × ℝ => U' p.2.1 p.1 p.2.2 - jumpU Ω p.2.1 p.1 p.2.2) 2
      (Poisson.Compensated.markedEnergyMeasure P (Measure.dirac (1 : ℝ)) 1) = 0 :=
    (pow_eq_zero_iff two_ne_zero).mp hzero
  have hae := (eLpNorm_eq_zero_iff hmd.aestronglyMeasurable (by norm_num)).mp h0
  have hae2 : (fun p : Ω × ℝ × ℝ => U' p.2.1 p.1 p.2.2)
      =ᵐ[Poisson.Compensated.markedEnergyMeasure P (Measure.dirac (1 : ℝ)) 1]
        fun p : Ω × ℝ × ℝ => jumpU Ω p.2.1 p.1 p.2.2 := by
    filter_upwards [hae] with p hp
    have hp' : U' p.2.1 p.1 p.2.2 - jumpU Ω p.2.1 p.1 p.2.2 = 0 := hp
    linarith
  rw [Poisson.Compensated.markedEnergy_eq_eLpNorm_sq (φ := fun ω s e => U' s ω e) hmU 1,
    eLpNorm_congr_ae hae2, ← Poisson.Compensated.markedEnergy_eq_eLpNorm_sq
      (φ := fun ω s e => jumpU Ω s ω e) hmJ 1]
  exact _root_.Prove2MeSourceProof.h_f155e4082a26872bbbd3bfda
/-! ### The witness -/

/-- On some probability space there are a Lévy driver with one Brownian coordinate and jump
intensity `δ_1`, and a solution triple of the backward equation with vanishing generator,
terminal datum the compensated integral of `1_{(0, 1]}` at time `1` and horizon `1` whose jump
integrand is `1_{(0, 1]}`, of marked energy `1` on the horizon; the jump integrand of every
solution triple of that equation has nonzero marked energy on the horizon. -/
theorem exists_solvesBSDEJ_markedEnergy_ne_zero :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))),
      (∃ Y : ℝ → Ω → ℝ,
          SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (jumpLeg D 1) 1 Y (zeroZ Ω) (jumpU Ω) ∧
            ∀ t, Y t =ᵐ[P] jumpLeg D t) ∧
        Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
            (fun ω s e => jumpU Ω s ω e) = 1 ∧
        ∀ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin 1 → ℝ)) (U' : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (jumpLeg D 1) 1 Y' Z' U' →
            Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
              (fun ω s e => U' s ω e) ≠ 0 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (1 : ℝ))
  exact ⟨Ω, inferInstance, P, inferInstance, D, _root_.Prove2MeSourceProof.h_037e724daadf008d5ad1442c D, _root_.Prove2MeSourceProof.h_f155e4082a26872bbbd3bfda,
    fun _ _ _ h => by rw [markedEnergy_eq_one_of_solvesBSDEJ D h]; exact one_ne_zero⟩
end LevyStochCalc.Examples.Nonvacuity


