-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_Solves_F000
-- name    : LevyStochCalc_BSDEJ_Solves_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:35:52.512525+00:00
-- url     : https://prove2.me/theorems/9fc08fa7-95cf-4451-9c9b-047c90d66b1d
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.Solves
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.Solves. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Definition_F000
import Definitions.Def_LevyStochCalc_Driver_JointFiltration_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Solutions of a BSDEJ pinned to a Lévy driver

`SolvesBSDEJ D f ξ T Y Z U` is the solution predicate of the backward equation

  `Y_t = ξ + ∫_t^T f(s, Y_s, Z_s, U_s) ds − ∫_t^T Z_s dW_s − ∫_t^T ∫_E U_s(e) Ñ(ds, de)`

over the augmented joint filtration `augJoint D` of a single `LevyDriver D`, with the two
stochastic integrals the canonical ones for that filtration. `Z` and `U` vanish off `[0, T]`,
which turns their finite energy on the horizon into the global square integrability the
integrals are defined under (`sq_int_global_of_vanishing`,
`marked_sq_int_global_of_vanishing`).

`BSDEJ.Definition.IsBSDEJSolution` quantifies existentially over the filtration and over the
martingale legs, so a pair of solutions may be stated over different filtrations; pinning the
filtration to `augJoint D` is what makes a uniqueness statement expressible. The intended
bridge `isBSDEJSolution_of_solvesBSDEJ` takes a `SolvesBSDEJ D f ξ T Y Z U` to
`IsBSDEJSolution D.W D.N (bsdejDataOfGenerator f hf) X Y Z U T` for a forward process `X` with
`X T = ξ`, witnessing the existential by `ℱ := augJoint D`, the filtration facts
`LevyStochCalc.Driver.LevyDriver.isBrownianFiltration_aug` and
`LevyStochCalc.Driver.LevyDriver.isPoissonFiltration_aug` at `D`, and
`Filt := (augJoint D).rightCont`, and the martingale legs by
the two canonical integrals; it needs the `S²` bound on `Y`, the martingale property of the
legs and the progressive measurability of the mark slices of `U`, and is not stated here.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- The joint filtration of a Lévy driver, frozen before time `0` and augmented by the
`P`-null sets. -/
noncomputable abbrev augJoint (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) :
    MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω› :=
  LevyStochCalc.Brownian.augFiltration D.filtration P
omit [IsProbabilityMeasure P] in
/-- An integrand vanishing off a horizon on which each coordinate has finite energy is square
integrable on every horizon. -/
theorem sq_int_global_of_vanishing {Z : ℝ → Ω → (Fin d → ℝ)} {T : ℝ}
    (hvan : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0)
    (hsq : ∀ i : Fin d, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤) :
    ∀ i : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  fun i T' _ => lt_of_le_of_lt
    (_root_.Prove2MeSourceProof.h_6afbd3f9a4aa317ea9c9ba3c (H := fun ω s => Z s ω i)
      (fun ω s hs => by simp [hvan ω s hs]) T')
    (lt_top_iff_ne_top.mpr (hsq i))
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- A marked integrand vanishing off a horizon on which it has finite marked energy is square
integrable on every horizon. -/
theorem marked_sq_int_global_of_vanishing {U : ℝ → Ω → E → ℝ} {T : ℝ}
    (hvan : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0)
    (hsq : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤) :
    ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖(fun ω' s e => U s ω' e) ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
  fun T' _ => lt_of_le_of_lt
    (_root_.Prove2MeSourceProof.h_5fad5a5e72ace6c4e33f3a33
      (φ := fun ω s e => U s ω e) hvan T')
    (lt_top_iff_ne_top.mpr hsq)
/-- `(Y, Z, U)` solves the BSDEJ with generator `f`, terminal value `ξ` and horizon `T`, driven
by `D` over the augmented joint filtration `augJoint D`:

`Y_t = ξ + ∫_t^T f(s, Y_s, Z_s, U_s) ds − ∫_t^T Z_s dW_s − ∫_t^T ∫_E U_s(e) Ñ(ds, de)`

almost surely at each `t ∈ [0, T]`, with the two stochastic integrals the canonical ones for
`augJoint D`, `Y` càdlàg, adapted to `(augJoint D).rightCont` and of finite `S²` seminorm on the
horizon, and `Z`, `U` progressive with finite energy on `[0, T]` and vanishing off it. The
path conditions on `Y`, `Z`, `U` are asked at every sample point; `SolvesBSDEJAe` asks them
almost surely, and `SolvesBSDEJAe.exists_modification` recovers a solution in this sense by
setting the three processes to `0` on a null set. -/
structure SolvesBSDEJ (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ) (ξ : Ω → ℝ) (T : ℝ)
    (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ) : Prop where
  /-- Each coordinate of `Z` is jointly measurable. -/
  Z_meas : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i)
  /-- Each coordinate of `Z` is progressively measurable for the augmented joint filtration. -/
  Z_prog : ∀ i : Fin d,
    LevyStochCalc.Probability.ProgressivelyMeasurable (augJoint D) fun ω s => Z s ω i
  /-- `Z` vanishes off the horizon. -/
  Z_vanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0
  /-- Each coordinate of `Z` has finite energy on the horizon. -/
  Z_sq : ∀ i : Fin d, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤
  /-- `U` is jointly measurable in the sample point, the time and the mark. -/
  U_meas : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2
  /-- `U` is marked progressively measurable for the augmented joint filtration. -/
  U_prog : LevyStochCalc.Probability.MarkedProgressivelyMeasurable (augJoint D)
    fun ω s e => U s ω e
  /-- `U` vanishes off the horizon. -/
  U_vanish : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0
  /-- `U` has finite marked energy on the horizon. -/
  U_sq : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤
  /-- `Y` is jointly measurable. -/
  Y_meas : Measurable (Function.uncurry Y)
  /-- `Y` is adapted to the right-continuous augmented joint filtration. -/
  Y_adapted : MeasureTheory.Adapted (augJoint D).rightCont Y
  /-- Every path of `Y` is right-continuous with left limits. -/
  Y_cadlag : ∀ ω : Ω, ∀ t : ℝ,
    Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
      ∧ ∃ L : ℝ, Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L)
  /-- The running supremum of `Y` on the horizon is square integrable. -/
  Y_sup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤
  /-- The backward equation, almost surely at each time of the horizon. -/
  eqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
    Y t ω = ξ ω + (∫ s in Set.Icc t T, f s (Y s ω) (Z s ω) (U s ω))
      - (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
            (augJoint D) D.isBrownianFiltration_aug Z Z_meas Z_prog
            (sq_int_global_of_vanishing Z_vanish Z_sq) T ω
          - LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
            (augJoint D) D.isBrownianFiltration_aug Z Z_meas Z_prog
            (sq_int_global_of_vanishing Z_vanish Z_sq) t ω)
      - (LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N (augJoint D)
            D.isPoissonFiltration_aug (fun ω' s e => U s ω' e) U_meas U_prog
            (marked_sq_int_global_of_vanishing U_vanish U_sq) T ω
          - LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N (augJoint D)
            D.isPoissonFiltration_aug (fun ω' s e => U s ω' e) U_meas U_prog
            (marked_sq_int_global_of_vanishing U_vanish U_sq) t ω)
/-- The value process of a solution agrees with the terminal datum almost surely at the horizon. -/
theorem SolvesBSDEJ.Y_terminal {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {ξ : Ω → ℝ} {T : ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (h : SolvesBSDEJ D f ξ T Y Z U) (hT : 0 ≤ T) : Y T =ᵐ[P] ξ := by
  filter_upwards [h.eqn T ⟨hT, le_rfl⟩] with ω hω
  have hint : ∫ s in Set.Icc T T, f s (Y s ω) (Z s ω) (U s ω) = 0 :=
    MeasureTheory.setIntegral_measure_zero _ (by simp)
  rw [hω, hint]
  ring
/-- The `BSDEJData` of a generator that does not read the forward process, with the forward
dimension `n = 1` and the terminal condition the evaluation `x ↦ x 0`. -/
def bsdejDataOfGenerator (f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ)
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u) :
    LevyStochCalc.BSDEJ.Definition.BSDEJData 1 d E where
  f := fun s _ y z u => f s y z u
  g := fun x => x 0
  g_measurable := measurable_pi_apply 0
  f_measurable_slice := fun u => by
    have hmap : Measurable fun p : ℝ × (Fin 1 → ℝ) × ℝ × (Fin d → ℝ) =>
        ((p.1, p.2.2.1, p.2.2.2) : ℝ × ℝ × (Fin d → ℝ)) := by fun_prop
    exact (hf u).comp hmap
end LevyStochCalc.BSDEJ.Solves


