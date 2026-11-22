-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpDiffusionItoLevyPinned_F000
-- name    : LevyStochCalc_Ito_JumpDiffusionItoLevyPinned_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:16:03.558547+00:00
-- url     : https://prove2.me/theorems/3a009f11-59c0-456d-9a0b-6f2c0c0d9be3
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpDiffusionItoLevyPinned
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpDiffusionItoLevyPinned. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoQuadVarSum_F003
import Definitions.Def_LevyStochCalc_Driver_AugJointRightCont_F000
import Definitions.Def_LevyStochCalc_Driver_AugJointRightCont_F002
import Definitions.Def_LevyStochCalc_Ito_ItoLevyProcess_F000
import Definitions.Def_LevyStochCalc_Ito_JumpDiffusionAdapted_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Jump-diffusion coordinates as Itô–Lévy processes over a named filtration

`JumpDiffusion.exists_isItoLevyProcess` reads a coordinate of a jump diffusion as an Itô–Lévy
process over the filtration bundled in the `is_solution` existential, so the filtration is not
the caller's. Over a filtration named in advance the same decomposition is the integral equation
of `LevyStochCalc.Ito.Picard.SolvesOn` read coordinatewise: the Picard map is the sum of the
initial value, the drift integral, the Brownian integral of the diffusion row and the
compensated Poisson integral of the jump row.

For the augmented joint filtration of a Lévy driver, Lipschitz and regular coefficients give
such a process in every coordinate, adapted and square integrable at every nonnegative time; the
square integrability is the `S²` bound `JumpDiffusion.sup_L2` restricted to a fixed time and a
single coordinate.

## Main statements

* `LevyStochCalc.Ito.Setting.memLp_two_coord_of_supL2` — a coordinate of a process with a finite
  `S²` norm on every horizon is square integrable at every nonnegative time.
* `LevyStochCalc.Ito.Setting.JumpDiffusion.isItoLevyProcess_coord_of_solvesOn` — a coordinate of
  a jump diffusion solving the equation relative to a filtration is an Itô–Lévy process over
  that filtration.
* `LevyStochCalc.Driver.LevyDriver.exists_isItoLevyProcess_augJoint` — over the augmented joint
  filtration of a Lévy driver, Lipschitz and regular coefficients give a jump diffusion whose
  coordinates are Itô–Lévy processes, adapted and square integrable at every nonnegative time.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Ito.Setting

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

omit [IsProbabilityMeasure P] in
/-- A coordinate of a process with a finite `S²` norm on every horizon is square integrable at
every nonnegative time. -/
theorem memLp_two_coord_of_supL2 {X : ℝ → Ω → (Fin n → ℝ)}
    (hXm : Measurable (Function.uncurry X))
    (hsup : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖X t.1 ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) (i : Fin n) : MemLp (fun ω => X t ω i) 2 P := by
  have hmeas : Measurable fun ω => X t ω i :=
    (hXm.comp (measurable_const.prodMk measurable_id)).eval
  refine LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top hmeas.aestronglyMeasurable
    (lt_of_le_of_lt (lintegral_mono fun ω => ?_) (hsup (t + 1) (by linarith)))
  refine le_trans (Finset.single_le_sum (f := fun j : Fin n => (‖X t ω j‖₊ : ℝ≥0∞) ^ 2)
    (fun _ _ => zero_le) (Finset.mem_univ i)) ?_
  exact le_iSup (fun u : Set.Icc (0 : ℝ) (t + 1) => ∑ j, (‖X u.1 ω j‖₊ : ℝ≥0∞) ^ 2)
    ⟨t, ⟨ht, by linarith⟩⟩
namespace JumpDiffusion

/-- **Every coordinate of a jump diffusion solving the equation relative to a filtration is an
Itô–Lévy process over that filtration**, with the integrands the coefficients evaluated along
the path. -/
theorem isItoLevyProcess_coord_of_solvesOn
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} (jd : JumpDiffusion W N coeffs x₀)
    (hjd : ∀ T : ℝ, LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ jd.X T)
    (i : Fin n) :
    IsItoLevyProcess W N ℱ hℱW hℱN (fun t ω => jd.X t ω i) (fun _ => x₀ i)
      (fun s ω => coeffs.μ s (jd.X s ω) i) (fun s ω => coeffs.σ s (jd.X s ω) i)
      (fun ω s e => coeffs.γ s (jd.X s ω) e i) where
  measurable_path := jd.measurable_path.eval
  σ_meas := fun j => (hjd 1).h_σ_meas i j
  σ_prog := fun j => (hjd 1).h_σ_progMeas i j
  σ_sq := fun j => (hjd 1).h_σ_sq i j
  γ_meas := (hjd 1).h_γ_meas i
  γ_prog := (hjd 1).h_γ_progMeas i
  γ_sq := (hjd 1).h_γ_sq i
  decomposition := by
    intro t ht
    filter_upwards [(hjd t).eqn t ⟨ht, le_rfl⟩] with ω hω
    exact hω i
end JumpDiffusion

end LevyStochCalc.Ito.Setting

namespace LevyStochCalc.Driver

open LevyStochCalc.Ito.Setting

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

namespace LevyDriver

/-- **The jump-diffusion SDE over a Lévy driver, coordinatewise.** For Lipschitz and regular
coefficients there is a jump diffusion driven by `D` which is adapted to the augmented joint
filtration of `D` and whose every coordinate is an Itô–Lévy process over that filtration, square
integrable at every nonnegative time. -/
theorem exists_isItoLevyProcess_augJoint (D : LevyDriver.{u, v, w} P d ν)
    (coeffs : JumpDiffusionCoeffs n d E) (x₀ : Fin n → ℝ) {L : ℝ}
    (hLip : JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (hReg : JumpDiffusionCoeffs.IsRegular coeffs ν) :
    ∃ jd : JumpDiffusion D.W D.N coeffs x₀,
      (∀ t : ℝ, 0 ≤ t → StronglyMeasurable[Brownian.augFiltration D.filtration P t] (jd.X t)) ∧
        ∀ i : Fin n,
          IsItoLevyProcess D.W D.N (Brownian.augFiltration D.filtration P)
              D.isBrownianFiltration_aug D.isPoissonFiltration_aug (fun t ω => jd.X t ω i)
              (fun _ => x₀ i) (fun s ω => coeffs.μ s (jd.X s ω) i)
              (fun s ω => coeffs.σ s (jd.X s ω) i)
              (fun ω s e => coeffs.γ s (jd.X s ω) e i) ∧
            (∀ t : ℝ, 0 ≤ t →
              StronglyMeasurable[Brownian.augFiltration D.filtration P t] fun ω => jd.X t ω i) ∧
            (∀ t : ℝ, 0 ≤ t → MemLp (fun ω => jd.X t ω i) 2 P) := by
  obtain ⟨jd, hjd, hadapt, -⟩ :=
    JumpDiffusion.exists_unique_adapted D.W D.N (Brownian.augFiltration D.filtration P)
      D.isBrownianFiltration_aug D.isPoissonFiltration_aug
      (fun _ ht => D.augFiltration_le_of_nonpos ht)
      (fun _ hs h0 => D.measurableSet_augFiltration_of_null hs h0) coeffs x₀ hLip hReg
  refine ⟨jd, hadapt, fun i => ⟨?_, ?_, ?_⟩⟩
  · exact JumpDiffusion.isItoLevyProcess_coord_of_solvesOn D.W D.N
      (Brownian.augFiltration D.filtration P) D.isBrownianFiltration_aug
      D.isPoissonFiltration_aug jd hjd i
  · intro t ht
    letI : MeasurableSpace Ω := Brownian.augFiltration D.filtration P t
    exact ((hadapt t ht).measurable.eval (a := i)).stronglyMeasurable
  · exact fun t ht => memLp_two_coord_of_supL2 jd.measurable_path jd.sup_L2 ht i
end LevyDriver

end LevyStochCalc.Driver


