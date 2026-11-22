-- Prove2me | Definitions.Def_NonvacuityBSDEJData_F000
-- name    : NonvacuityBSDEJData_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:26:32.951046+00:00
-- url     : https://prove2.me/theorems/ec9f9fc2-143b-45f6-9907-08af9c84e779
-- title:
--   Source declarations: NonvacuityBSDEJData
-- statement:
--   Source-preserving extracted declarations from NonvacuityBSDEJData. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Bridge_F000
import Definitions.Def_LevyStochCalc_BSDEJ_Existence_F000
import Definitions.Def_LevyStochCalc_Brownian_PRPMultidimRange_F000
import Definitions.Def_LevyStochCalc_Driver_JointRange_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedRange_F001
import Definitions.Def_NonvacuityBSDEJExp_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The BSDEJ data and the joint integral of a Lévy driver on a concrete model

The data of the scalar backward equation

  `Y_t = W_1 + ∫_t^1 Y_s ds − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`,

driven by a Lévy driver with one Brownian coordinate and a Poisson random measure of intensity
`dt ⊗ δ_1` on `[0, ∞) × ℝ`, as a `BSDEJ.Definition.BSDEJData 1 1 ℝ`: the generator is
`f(s, x, y, z, u) = y`, the terminal map is the coordinate `0`, the horizon is `T = 1` and the
forward process is constant at `W_1`. The solution triples of `BSDEJ.Solves.SolvesBSDEJ` for
this equation are solutions in the sense of `BSDEJ.Definition.IsBSDEJSolution` for that data.

The joint integral `Driver.LevyDriver.jointIntegral` of the same driver is taken on the
integrand `1_{[0,1]}` in the single Brownian coordinate against the zero marked integrand, and
on the zero Brownian integrand against the marked integrand `1_{[0,1]}`; both have second
moment `1` at the horizon.

## Main statements

* `bsdejDataId` — the data of the equation, with generator the identity in the value argument
  and terminal map the coordinate `0`, neither the zero map nor a constant.
* `lipschitz_bsdejDataId` — the `ℝ≥0∞` Lipschitz condition `BSDEJ.Existence.Lipschitz` holds
  for this data with constant `1`, and `abs_sub_bsdejDataId_le_one` is its real form at a pair
  of value arguments with positive increment.
* `isBSDEJSolution_generator_id` — a solution triple of the equation is a solution for this
  data, `isBSDEJSolution_generator_id_terminal` reads its terminal value off the equation of
  `BSDEJ.Definition.IsBSDEJSolution.eqn_canonical`, and
  `exists_isBSDEJSolution_bsdejDataId` assembles the witness, whose value process is not almost
  surely `0` at the horizon.
* `exists_jointIntegral_brownianLeg_not_ae_zero` and
  `exists_jointIntegral_markedLeg_not_ae_zero` — the joint integral of the driver, on each of
  the two integrand pairs above, has second moment `1` and is not almost surely `0`.

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

/-! ### The data of the equation -/

/-- The BSDEJ data of the generator `f(s, x, y, z, u) = y` on one forward coordinate, one
Brownian coordinate and marks in `ℝ`, with terminal map the coordinate `0`. -/
def bsdejDataId : BSDEJ.Definition.BSDEJData 1 1 ℝ :=
  bsdejDataOfGenerator (fun _ y _ _ => y) measurable_generator_id
/-- The generator of `bsdejDataId` is the identity in the value argument. -/
theorem bsdejDataId_f (s : ℝ) (x : Fin 1 → ℝ) (y : ℝ) (z : Fin 1 → ℝ) (u : ℝ → ℝ) :
    bsdejDataId.f s x y z u = y := rfl
/-- The terminal map of `bsdejDataId` is the coordinate `0`. -/
theorem bsdejDataId_g (x : Fin 1 → ℝ) : bsdejDataId.g x = x 0 := rfl
/-- The generator of `bsdejDataId` is not the zero map. -/
theorem bsdejDataId_f_ne_zero : bsdejDataId.f 0 0 1 0 0 ≠ 0 := one_ne_zero
/-- The terminal map of `bsdejDataId` is not constant. -/
theorem bsdejDataId_g_ne : bsdejDataId.g (fun _ => 1) ≠ bsdejDataId.g (fun _ => 0) :=
  one_ne_zero
/-! ### The Lipschitz condition -/

/-- The Lipschitz condition on the generator of `bsdejDataId` for the intensity `δ_1`, with
constant `1`. -/
theorem lipschitz_bsdejDataId :
    BSDEJ.Existence.Lipschitz bsdejDataId (Measure.dirac (1 : ℝ)) 1 :=
  fun s _x y₁ y₂ z₁ z₂ u₁ u₂ => lipschitz_generator_id s y₁ y₂ z₁ z₂ u₁ u₂
/-- The increment of the generator of `bsdejDataId` between the value arguments `1` and `0` is
positive. -/
theorem abs_sub_bsdejDataId_pos :
    0 < |bsdejDataId.f 0 0 1 0 0 - bsdejDataId.f 0 0 0 0 0| := by
  rw [bsdejDataId_f, bsdejDataId_f]
  norm_num
/-- The real-valued Lipschitz bound for `bsdejDataId` between the value arguments `1` and `0`,
the remaining arguments being equal. -/
theorem abs_sub_bsdejDataId_le_one :
    |bsdejDataId.f 0 0 1 0 0 - bsdejDataId.f 0 0 0 0 0| ≤ 1 := by
  have h := BSDEJ.Existence.abs_sub_le_of_lipschitz zero_le_one lipschitz_bsdejDataId
    0 0 1 0 0 0 0 0 (by simp)
  simpa using h
/-! ### Solutions for the data -/

/-- A solution triple of the backward equation with generator `f(s, y, z, u) = y`, terminal
datum `W_1` and horizon `1` is a solution for the data `bsdejDataId` and the forward process
constant at `W_1`. -/
theorem isBSDEJSolution_generator_id (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin 1 → ℝ)} {U : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U) :
    BSDEJ.Definition.IsBSDEJSolution D.W D.N bsdejDataId
      (fun _ ω _ => (D.W.W 0).W 1 ω) Y Z U 1 :=
  isBSDEJSolution_of_solvesBSDEJ_const D measurable_generator_id zero_le_one h
/-- The equation of a solution for the data `bsdejDataId` and the forward process constant at
`W_1`. -/
theorem exists_eqn_isBSDEJSolution_generator_id (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin 1 → ℝ)} {U : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U) :
    ∃ M_W M_N : ℝ → Ω → ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ ω ∂P,
      Y t ω = (D.W.W 0).W 1 ω + (∫ s in Set.Icc t 1, Y s ω)
        - (M_W 1 ω - M_W t ω) - (M_N 1 ω - M_N t ω) :=
  (isBSDEJSolution_generator_id D h).eqn_canonical
/-- The value process of a solution for the data `bsdejDataId` agrees with `W_1` at the horizon
almost surely. -/
theorem isBSDEJSolution_generator_id_terminal (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin 1 → ℝ)} {U : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U) :
    Y 1 =ᵐ[P] fun ω => (D.W.W 0).W 1 ω := by
  obtain ⟨M_W, M_N, heqn⟩ := exists_eqn_isBSDEJSolution_generator_id D h
  filter_upwards [heqn 1 ⟨zero_le_one, le_rfl⟩] with ω hω
  have hint : ∫ s in Set.Icc (1 : ℝ) 1, Y s ω = 0 :=
    MeasureTheory.setIntegral_measure_zero _ (by simp)
  rw [hω, hint]
  ring
/-- On some probability space there are a Lévy driver with one Brownian coordinate and jump
intensity `δ_1` and a solution, in the sense of `BSDEJ.Definition.IsBSDEJSolution`, of the
backward equation with data `bsdejDataId` and forward process constant at `W_1`, whose value
process equals `W_1` at the horizon and is not almost surely `0` there, and whose Brownian
integrand has nonzero energy on the horizon. -/
theorem exists_isBSDEJSolution_bsdejDataId :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) (Y : ℝ → Ω → ℝ)
      (Z : ℝ → Ω → (Fin 1 → ℝ)) (U : ℝ → Ω → ℝ → ℝ),
      BSDEJ.Definition.IsBSDEJSolution D.W D.N bsdejDataId
          (fun _ ω _ => (D.W.W 0).W 1 ω) Y Z U 1 ∧
        (Y 1 =ᵐ[P] fun ω => (D.W.W 0).W 1 ω) ∧ ¬ (Y 1 =ᵐ[P] fun _ => (0 : ℝ)) ∧
        Brownian.Ito.energy P 1 (fun ω s => Z s ω 0) ≠ 0 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (1 : ℝ))
  obtain ⟨Y, hY, -⟩ := _root_.Prove2MeSourceProof.h_cdebc989955e2f6003b4385b D
  exact ⟨Ω, inferInstance, P, inferInstance, D, Y, expZ Ω, fun _ _ _ => (0 : ℝ),
    isBSDEJSolution_generator_id D hY, isBSDEJSolution_generator_id_terminal D hY,
    solvesBSDEJ_generator_id_not_zero hY, energy_expZ_ne_zero 0⟩
/-! ### The joint integral with a nonzero Brownian leg -/

/-- The deterministic integrand equal to `1` on the horizon `[0, 1]` and to `0` off it. -/
noncomputable def windowOne (Ω : Type u) : Ω → ℝ → ℝ :=
  fun _ s => Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => (1 : ℝ)) s
/-- The windowed constant integrand is jointly measurable in the sample point and the time. -/
theorem measurable_windowOne (Ω : Type u) [MeasurableSpace Ω] :
    Measurable (Function.uncurry (windowOne Ω)) :=
  (measurable_const.indicator measurableSet_Icc).comp measurable_snd
/-- The windowed constant integrand is progressively measurable for every filtration. -/
theorem progressive_windowOne (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    Probability.ProgressivelyMeasurable ℱ (windowOne Ω) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hg : Measurable
      (Set.indicator (Set.Iic t) (Set.indicator (Set.Icc (0 : ℝ) 1) fun _ => (1 : ℝ))) :=
    (measurable_const.indicator measurableSet_Icc).indicator measurableSet_Iic
  exact (hg.comp measurable_snd).stronglyMeasurable
omit [MeasurableSpace Ω] in
/-- The windowed constant integrand vanishes off the horizon `[0, 1]`. -/
theorem windowOne_vanish (ω : Ω) (s : ℝ) (hs : s ∉ Set.Icc (0 : ℝ) 1) : windowOne Ω ω s = 0 :=
  Set.indicator_of_notMem hs _
omit [MeasurableSpace Ω] in
/-- The square of a path of the windowed constant integrand integrates to `1` on the
horizon `[0, 1]`. -/
theorem lintegral_sq_windowOne (ω : Ω) :
    ∫⁻ s in Set.Icc (0 : ℝ) 1, (‖windowOne Ω ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume = 1 := by
  have hpt : (fun s : ℝ => (‖windowOne Ω ω s‖₊ : ℝ≥0∞) ^ 2)
      = Set.indicator (Set.Icc (0 : ℝ) 1) fun _ => (1 : ℝ≥0∞) := by
    funext s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) 1 <;> simp [windowOne, hs]
  rw [hpt, lintegral_indicator measurableSet_Icc]
  simp [Real.volume_Icc]
/-- The energy of the windowed constant integrand on the horizon `[0, 1]` is `1`. -/
theorem energy_windowOne (P : Measure Ω) [IsProbabilityMeasure P] :
    Brownian.Ito.energy P 1 (windowOne Ω) = 1 := by
  simp only [Brownian.Ito.energy, lintegral_sq_windowOne]
  simp
/-- The windowed constant integrand, as an integrand admissible for the Itô integral on the
horizon `[0, 1]`. -/
noncomputable def windowOneIntegrand (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) : Brownian.Ito.HorizonIntegrand P ℱ 1 where
  toFun := windowOne Ω
  measurable_uncurry := measurable_windowOne Ω
  progressive := progressive_windowOne ℱ
  vanishing := windowOne_vanish
  energy_ne_top := by rw [energy_windowOne]; exact ENNReal.one_ne_top
/-- The Itô integral of the windowed constant integrand against the Brownian coordinate of a
Lévy driver has second moment `1` at time `1`. -/
theorem lintegral_sq_integral_windowOne (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    ∫⁻ ω, (‖(windowOneIntegrand P (augJoint D)).integral (D.W.W 0)
        (D.isBrownianFiltration_aug 0) ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 := by
  have h : ∫⁻ ω, (‖(windowOneIntegrand P (augJoint D)).integral (D.W.W 0)
        (D.isBrownianFiltration_aug 0) ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) 1,
          (‖windowOne Ω ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    Brownian.Ito.itoIsometry (D.W.W 0) (augJoint D) (D.isBrownianFiltration_aug 0)
      (windowOne Ω) 1 one_pos (measurable_windowOne Ω) (progressive_windowOne (augJoint D))
      (windowOneIntegrand P (augJoint D)).sq_int_global
  rw [h]
  exact energy_windowOne P
/-- The joint integral over a Lévy driver of the windowed constant Brownian integrand in the
single coordinate and of the zero marked integrand, on the horizon `[0, 1]`. -/
noncomputable def jointOne (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) : Ω → ℝ :=
  LevyStochCalc.Driver.LevyDriver.jointIntegral D.isBrownianFiltration_aug
    D.isPoissonFiltration_aug (fun _ => windowOneIntegrand P (augJoint D))
    (Poisson.Compensated.MarkedHorizonIntegrand.zero P (Measure.dirac (1 : ℝ)) (augJoint D) 1)
/-- The joint integral of the windowed constant Brownian integrand and the zero marked
integrand agrees almost surely with the Itô integral of its Brownian leg. -/
theorem jointOne_ae_eq (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    jointOne D =ᵐ[P] (windowOneIntegrand P (augJoint D)).integral (D.W.W 0)
      (D.isBrownianFiltration_aug 0) := by
  have hK := Poisson.Compensated.MarkedHorizonIntegrand.integral_zero D.N
    D.isPoissonFiltration_aug (T := (1 : ℝ)) one_pos
  filter_upwards [hK] with ω hω
  simp only [jointOne, LevyStochCalc.Driver.LevyDriver.jointIntegral,
    LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.vectorIntegral, Fin.sum_univ_one,
    hω, Pi.zero_apply, add_zero]
/-- The joint integral of the windowed constant Brownian integrand and the zero marked
integrand has second moment `1`. -/
theorem lintegral_sq_jointOne (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    ∫⁻ ω, (‖jointOne D ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 := by
  have hae : (fun ω => (‖jointOne D ω‖₊ : ℝ≥0∞) ^ 2)
      =ᵐ[P] fun ω => (‖(windowOneIntegrand P (augJoint D)).integral (D.W.W 0)
        (D.isBrownianFiltration_aug 0) ω‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [jointOne_ae_eq D] with ω hω
    rw [hω]
  rw [lintegral_congr_ae hae]
  exact lintegral_sq_integral_windowOne D
/-- The joint integral of the windowed constant Brownian integrand and the zero marked
integrand is not almost surely `0`. -/
theorem jointOne_not_ae_zero (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    ¬ jointOne D =ᵐ[P] fun _ => (0 : ℝ) := by
  intro h
  have hzero : (fun ω => (‖jointOne D ω‖₊ : ℝ≥0∞) ^ 2) =ᵐ[P] fun _ => (0 : ℝ≥0∞) := by
    filter_upwards [h] with ω hω
    simp [hω]
  have h0 := (lintegral_sq_jointOne D).symm.trans
    ((lintegral_congr_ae hzero).trans lintegral_zero)
  exact one_ne_zero h0
/-- On some probability space there are a Lévy driver with one Brownian coordinate and jump
intensity `δ_1` and a pair of admissible integrands, the marked one zero, whose joint integral
has second moment `1` and is not almost surely `0`. -/
theorem exists_jointIntegral_brownianLeg_not_ae_zero :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
      (G : ∀ _ : Fin 1, Brownian.Ito.HorizonIntegrand P (augJoint D) 1)
      (K : Poisson.Compensated.MarkedHorizonIntegrand P (Measure.dirac (1 : ℝ))
        (augJoint D) 1),
      ∫⁻ ω, (‖LevyStochCalc.Driver.LevyDriver.jointIntegral D.isBrownianFiltration_aug
          D.isPoissonFiltration_aug G K ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 ∧
        ¬ LevyStochCalc.Driver.LevyDriver.jointIntegral D.isBrownianFiltration_aug
            D.isPoissonFiltration_aug G K =ᵐ[P] fun _ => (0 : ℝ) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (1 : ℝ))
  exact ⟨Ω, inferInstance, P, inferInstance, D, fun _ => windowOneIntegrand P (augJoint D),
    Poisson.Compensated.MarkedHorizonIntegrand.zero P (Measure.dirac (1 : ℝ)) (augJoint D) 1,
    lintegral_sq_jointOne D, jointOne_not_ae_zero D⟩
/-! ### The joint integral with a nonzero marked leg -/

/-- The deterministic marked integrand equal to `1` on the horizon `[0, 1]` at every mark and
to `0` off it. -/
noncomputable def windowMark (Ω : Type u) : Ω → ℝ → ℝ → ℝ :=
  fun _ s _ => Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => (1 : ℝ)) s
/-- The windowed constant marked integrand is jointly measurable in the sample point, the time
and the mark. -/
theorem measurable_windowMark (Ω : Type u) [MeasurableSpace Ω] :
    Measurable fun p : Ω × ℝ × ℝ => windowMark Ω p.1 p.2.1 p.2.2 :=
  (measurable_const.indicator measurableSet_Icc).comp measurable_snd.fst
/-- The windowed constant marked integrand is progressively measurable for every filtration. -/
theorem markedProgressive_windowMark (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    Probability.MarkedProgressivelyMeasurable ℱ (windowMark Ω) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hg : Measurable
      (Set.indicator (Set.Iic t) (Set.indicator (Set.Icc (0 : ℝ) 1) fun _ => (1 : ℝ))) :=
    (measurable_const.indicator measurableSet_Icc).indicator measurableSet_Iic
  exact (hg.comp measurable_snd.fst).stronglyMeasurable
omit [MeasurableSpace Ω] in
/-- The windowed constant marked integrand vanishes off the horizon `[0, 1]`. -/
theorem windowMark_vanish (ω : Ω) (s e : ℝ) (hs : s ∉ Set.Icc (0 : ℝ) 1) :
    windowMark Ω ω s e = 0 :=
  Set.indicator_of_notMem hs _
/-- The marked energy of the windowed constant marked integrand on the horizon `[0, 1]`, for
the intensity `δ_1`, is `1`. -/
theorem markedEnergy_windowMark (P : Measure Ω) [IsProbabilityMeasure P] :
    Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1 (windowMark Ω) = 1 := by
  have hinner : ∀ (ω : Ω) (s : ℝ),
      ∫⁻ e : ℝ, (‖windowMark Ω ω s e‖₊ : ℝ≥0∞) ^ 2 ∂Measure.dirac (1 : ℝ)
        = (‖windowOne Ω ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    simp [windowMark, windowOne]
  simp only [Poisson.Compensated.markedEnergy, hinner, lintegral_sq_windowOne]
  simp
/-- The windowed constant marked integrand, as a marked integrand admissible for the
compensated integral on the horizon `[0, 1]`. -/
noncomputable def windowMarkIntegrand (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    Poisson.Compensated.MarkedHorizonIntegrand P (Measure.dirac (1 : ℝ)) ℱ 1 where
  toFun := windowMark Ω
  measurable_uncurry := measurable_windowMark Ω
  progressive := markedProgressive_windowMark ℱ
  vanishing := windowMark_vanish
  energy_ne_top := by rw [markedEnergy_windowMark]; exact ENNReal.one_ne_top
/-- The compensated integral of the windowed constant marked integrand against the Poisson
random measure of a Lévy driver has second moment `1` at time `1`. -/
theorem lintegral_sq_integral_windowMark (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    ∫⁻ ω, (‖(windowMarkIntegrand P (augJoint D)).integral D.N
        D.isPoissonFiltration_aug ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 := by
  have h : ∫⁻ ω, (‖(windowMarkIntegrand P (augJoint D)).integral D.N
        D.isPoissonFiltration_aug ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) 1, ∫⁻ e,
          (‖windowMark Ω ω s e‖₊ : ℝ≥0∞) ^ 2 ∂Measure.dirac (1 : ℝ) ∂volume ∂P :=
    Poisson.L2Isometry.itoLevyIsometry D.N (augJoint D) D.isPoissonFiltration_aug
      (windowMark Ω) (measurable_windowMark Ω) (markedProgressive_windowMark (augJoint D))
      (windowMarkIntegrand P (augJoint D)).sq_int_global 1 one_pos
  rw [h]
  exact markedEnergy_windowMark P
/-- The joint integral over a Lévy driver of the zero Brownian integrand and the windowed
constant marked integrand, on the horizon `[0, 1]`. -/
noncomputable def jointMark (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) : Ω → ℝ :=
  LevyStochCalc.Driver.LevyDriver.jointIntegral D.isBrownianFiltration_aug
    D.isPoissonFiltration_aug (fun _ => Brownian.Ito.HorizonIntegrand.zero P (augJoint D) 1)
    (windowMarkIntegrand P (augJoint D))
/-- The joint integral of the zero Brownian integrand and the windowed constant marked
integrand agrees almost surely with the compensated integral of its marked leg. -/
theorem jointMark_ae_eq (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    jointMark D =ᵐ[P] (windowMarkIntegrand P (augJoint D)).integral D.N
      D.isPoissonFiltration_aug := by
  have hG := Brownian.Ito.HorizonIntegrand.integral_zero (D.W.W 0)
    (D.isBrownianFiltration_aug 0) (T := (1 : ℝ)) one_pos
  filter_upwards [hG] with ω hω
  simp only [jointMark, LevyStochCalc.Driver.LevyDriver.jointIntegral,
    LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.vectorIntegral, Fin.sum_univ_one,
    hω, Pi.zero_apply, zero_add]
/-- The joint integral of the zero Brownian integrand and the windowed constant marked
integrand has second moment `1`. -/
theorem lintegral_sq_jointMark (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    ∫⁻ ω, (‖jointMark D ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 := by
  have hae : (fun ω => (‖jointMark D ω‖₊ : ℝ≥0∞) ^ 2)
      =ᵐ[P] fun ω => (‖(windowMarkIntegrand P (augJoint D)).integral D.N
        D.isPoissonFiltration_aug ω‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [jointMark_ae_eq D] with ω hω
    rw [hω]
  rw [lintegral_congr_ae hae]
  exact lintegral_sq_integral_windowMark D
/-- The joint integral of the zero Brownian integrand and the windowed constant marked
integrand is not almost surely `0`. -/
theorem jointMark_not_ae_zero (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    ¬ jointMark D =ᵐ[P] fun _ => (0 : ℝ) := by
  intro h
  have hzero : (fun ω => (‖jointMark D ω‖₊ : ℝ≥0∞) ^ 2) =ᵐ[P] fun _ => (0 : ℝ≥0∞) := by
    filter_upwards [h] with ω hω
    simp [hω]
  have h0 := (lintegral_sq_jointMark D).symm.trans
    ((lintegral_congr_ae hzero).trans lintegral_zero)
  exact one_ne_zero h0
/-- On some probability space there are a Lévy driver with one Brownian coordinate and jump
intensity `δ_1` and a pair of admissible integrands, the Brownian one zero, whose joint
integral has second moment `1` and is not almost surely `0`. -/
theorem exists_jointIntegral_markedLeg_not_ae_zero :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
      (G : ∀ _ : Fin 1, Brownian.Ito.HorizonIntegrand P (augJoint D) 1)
      (K : Poisson.Compensated.MarkedHorizonIntegrand P (Measure.dirac (1 : ℝ))
        (augJoint D) 1),
      ∫⁻ ω, (‖LevyStochCalc.Driver.LevyDriver.jointIntegral D.isBrownianFiltration_aug
          D.isPoissonFiltration_aug G K ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 1 ∧
        ¬ LevyStochCalc.Driver.LevyDriver.jointIntegral D.isBrownianFiltration_aug
            D.isPoissonFiltration_aug G K =ᵐ[P] fun _ => (0 : ℝ) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (1 : ℝ))
  exact ⟨Ω, inferInstance, P, inferInstance, D,
    fun _ => Brownian.Ito.HorizonIntegrand.zero P (augJoint D) 1,
    windowMarkIntegrand P (augJoint D), lintegral_sq_jointMark D, jointMark_not_ae_zero D⟩
end LevyStochCalc.Examples.Nonvacuity


