-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_Integrands_F000
-- name    : LevyStochCalc_BSDEJ_Integrands_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:32:35.873158+00:00
-- url     : https://prove2.me/theorems/057e24f1-2794-491d-8c46-8208ab938c29
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.Integrands
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.Integrands. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Solves_F000
import Definitions.Def_LevyStochCalc_Driver_JointRange_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Integrands of a BSDEJ solution as horizon integrands

The martingale legs `Z` and `U` of a BSDEJ solution carry exactly the data of a family of
`HorizonIntegrand`s indexed by the coordinates and of a single `MarkedHorizonIntegrand`:
`horizonIntegrandOfCoord` and `markedHorizonIntegrandOfProcess` package the `SolvesBSDEJ`
fields into those structures, `coordOfHorizonIntegrand` and `processOfMarkedHorizonIntegrand`
read them back, and the two pairs are mutually inverse. Under this dictionary the joint
integral `jointIntegral` of `Driver.LevyDriver` is the sum of the multidimensional Itô
integral and the compensated integral that the backward equation is written with.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

/-! ### The Brownian leg -/

/-- The `i`-th coordinate of a vector integrand that is measurable, progressive, vanishing off
the horizon and of finite energy, as an integrand admissible for the Itô integral. -/
def horizonIntegrandOfCoord (Z : ℝ → Ω → (Fin d → ℝ))
    (hm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hp : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hvan : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0)
    (hsq : ∀ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤) (i : Fin d) :
    Brownian.Ito.HorizonIntegrand P ℱ T where
  toFun := fun ω s => Z s ω i
  measurable_uncurry := hm i
  progressive := hp i
  vanishing := fun ω s hs => congrFun (hvan ω s hs) i
  energy_ne_top := hsq i
omit [IsProbabilityMeasure P] in
/-- The underlying process of the `i`-th coordinate integrand is the `i`-th coordinate. -/
@[simp]
theorem toFun_horizonIntegrandOfCoord (Z : ℝ → Ω → (Fin d → ℝ))
    (hm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hp : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hvan : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0)
    (hsq : ∀ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤) (i : Fin d) :
    (horizonIntegrandOfCoord Z hm hp hvan hsq i).toFun = fun ω s => Z s ω i :=
  rfl
/-- The vector process whose `i`-th coordinate at `(s, ω)` is the value of the `i`-th member of
a family of admissible Itô integrands. -/
def coordOfHorizonIntegrand (G : ∀ _ : Fin d, Brownian.Ito.HorizonIntegrand P ℱ T) :
    ℝ → Ω → (Fin d → ℝ) := fun s ω i => (G i).toFun ω s
omit [IsProbabilityMeasure P] in
/-- The value of the vector process of a family of admissible Itô integrands. -/
@[simp]
theorem coordOfHorizonIntegrand_apply (G : ∀ _ : Fin d, Brownian.Ito.HorizonIntegrand P ℱ T)
    (s : ℝ) (ω : Ω) (i : Fin d) : coordOfHorizonIntegrand G s ω i = (G i).toFun ω s :=
  rfl
omit [IsProbabilityMeasure P] in
/-- Each coordinate of the vector process of a family of admissible Itô integrands is jointly
measurable. -/
theorem measurable_coordOfHorizonIntegrand
    (G : ∀ _ : Fin d, Brownian.Ito.HorizonIntegrand P ℱ T) :
    ∀ i : Fin d, Measurable (Function.uncurry fun ω s => coordOfHorizonIntegrand G s ω i) :=
  fun i => (G i).measurable_uncurry
omit [IsProbabilityMeasure P] in
/-- Each coordinate of the vector process of a family of admissible Itô integrands is
progressively measurable. -/
theorem progressive_coordOfHorizonIntegrand
    (G : ∀ _ : Fin d, Brownian.Ito.HorizonIntegrand P ℱ T) :
    ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordOfHorizonIntegrand G s ω i :=
  fun i => (G i).progressive
omit [IsProbabilityMeasure P] in
/-- The vector process of a family of admissible Itô integrands vanishes off the horizon. -/
theorem coordOfHorizonIntegrand_vanish (G : ∀ _ : Fin d, Brownian.Ito.HorizonIntegrand P ℱ T) :
    ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → coordOfHorizonIntegrand G s ω = 0 := by
  intro ω s hs
  funext i
  exact (G i).vanishing ω s hs
omit [IsProbabilityMeasure P] in
/-- Each coordinate of the vector process of a family of admissible Itô integrands has finite
energy on the horizon. -/
theorem energy_coordOfHorizonIntegrand_ne_top
    (G : ∀ _ : Fin d, Brownian.Ito.HorizonIntegrand P ℱ T) :
    ∀ i : Fin d, Brownian.Ito.energy P T (fun ω s => coordOfHorizonIntegrand G s ω i) ≠ ⊤ :=
  fun i => (G i).energy_ne_top
/-! ### The jump leg -/

/-- A marked process that is measurable, marked progressive, vanishing off the horizon and of
finite marked energy, as an integrand admissible for the compensated integral. -/
def markedHorizonIntegrandOfProcess (U : ℝ → Ω → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U s ω e)
    (hvan : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0)
    (hsq : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤) :
    Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T where
  toFun := fun ω s e => U s ω e
  measurable_uncurry := hm
  progressive := hp
  vanishing := hvan
  energy_ne_top := hsq
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The underlying marked process of the integrand built from a marked process. -/
@[simp]
theorem toFun_markedHorizonIntegrandOfProcess (U : ℝ → Ω → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U s ω e)
    (hvan : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0)
    (hsq : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤) :
    (markedHorizonIntegrandOfProcess U hm hp hvan hsq).toFun = fun ω s e => U s ω e :=
  rfl
/-- The marked process whose value at `(s, ω, e)` is the value of an admissible marked
integrand. -/
def processOfMarkedHorizonIntegrand (K : Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T) :
    ℝ → Ω → E → ℝ := fun s ω e => K.toFun ω s e
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The value of the marked process of an admissible marked integrand. -/
@[simp]
theorem processOfMarkedHorizonIntegrand_apply
    (K : Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T) (s : ℝ) (ω : Ω) (e : E) :
    processOfMarkedHorizonIntegrand K s ω e = K.toFun ω s e :=
  rfl
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The marked process of an admissible marked integrand is jointly measurable in the sample
point, the time and the mark. -/
theorem measurable_processOfMarkedHorizonIntegrand
    (K : Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T) :
    Measurable fun p : Ω × ℝ × E => processOfMarkedHorizonIntegrand K p.2.1 p.1 p.2.2 :=
  K.measurable_uncurry
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The marked process of an admissible marked integrand is marked progressively measurable. -/
theorem progressive_processOfMarkedHorizonIntegrand
    (K : Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T) :
    Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => processOfMarkedHorizonIntegrand K s ω e :=
  K.progressive
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The marked process of an admissible marked integrand vanishes off the horizon. -/
theorem processOfMarkedHorizonIntegrand_vanish
    (K : Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T) :
    ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → processOfMarkedHorizonIntegrand K s ω e = 0 :=
  K.vanishing
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The marked process of an admissible marked integrand has finite marked energy on the
horizon. -/
theorem markedEnergy_processOfMarkedHorizonIntegrand_ne_top
    (K : Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T) :
    Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => processOfMarkedHorizonIntegrand K s ω e) ≠ ⊤ :=
  K.energy_ne_top
/-! ### Round trips -/

omit [IsProbabilityMeasure P] in
/-- Reading the coordinates of the horizon integrands built from a vector integrand returns
that integrand. -/
theorem coordOfHorizonIntegrand_horizonIntegrandOfCoord (Z : ℝ → Ω → (Fin d → ℝ))
    (hm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hp : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hvan : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0)
    (hsq : ∀ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤) :
    coordOfHorizonIntegrand (horizonIntegrandOfCoord Z hm hp hvan hsq) = Z :=
  rfl
omit [IsProbabilityMeasure P] in
/-- The horizon integrands built from the coordinates of a family of admissible Itô integrands
are that family. -/
theorem horizonIntegrandOfCoord_coordOfHorizonIntegrand
    (G : ∀ _ : Fin d, Brownian.Ito.HorizonIntegrand P ℱ T) :
    horizonIntegrandOfCoord (coordOfHorizonIntegrand G) (measurable_coordOfHorizonIntegrand G)
      (progressive_coordOfHorizonIntegrand G) (coordOfHorizonIntegrand_vanish G)
      (energy_coordOfHorizonIntegrand_ne_top G) = G :=
  rfl
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- Reading the marked process of the marked integrand built from a marked process returns that
process. -/
theorem processOfMarkedHorizonIntegrand_markedHorizonIntegrandOfProcess (U : ℝ → Ω → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U s ω e)
    (hvan : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0)
    (hsq : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤) :
    processOfMarkedHorizonIntegrand (markedHorizonIntegrandOfProcess U hm hp hvan hsq) = U :=
  rfl
omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The marked integrand built from the marked process of an admissible marked integrand is
that integrand. -/
theorem markedHorizonIntegrandOfProcess_processOfMarkedHorizonIntegrand
    (K : Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T) :
    markedHorizonIntegrandOfProcess (processOfMarkedHorizonIntegrand K)
      (measurable_processOfMarkedHorizonIntegrand K)
      (progressive_processOfMarkedHorizonIntegrand K)
      (processOfMarkedHorizonIntegrand_vanish K)
      (markedEnergy_processOfMarkedHorizonIntegrand_ne_top K) = K :=
  rfl
/-! ### The joint integral in the shape of the backward equation -/

/-- The joint integral of a family of admissible Itô integrands and an admissible marked
integrand is the multidimensional Itô integral of the coordinate process plus the compensated
integral of the marked process. -/
theorem jointIntegral_eq (D : Driver.LevyDriver.{u, v, w} P d ν)
    (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ)
    (hℱN : Poisson.IsPoissonFiltration D.N ℱ)
    (G : ∀ _ : Fin d, Brownian.Ito.HorizonIntegrand P ℱ T)
    (K : Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ T)
    (hm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => coordOfHorizonIntegrand G s ω i))
    (hp : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordOfHorizonIntegrand G s ω i)
    (hq : ∀ i : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordOfHorizonIntegrand G s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hKm : Measurable fun p : Ω × ℝ × E => processOfMarkedHorizonIntegrand K p.2.1 p.1 p.2.2)
    (hKp : Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => processOfMarkedHorizonIntegrand K s ω e)
    (hKq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖processOfMarkedHorizonIntegrand K s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    Driver.LevyDriver.jointIntegral hcoord hℱN G K = fun ω =>
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (coordOfHorizonIntegrand G) hm hp hq T ω
        + Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
          (fun ω' s e => processOfMarkedHorizonIntegrand K s ω' e) hKm hKp hKq T ω :=
  rfl
end LevyStochCalc.BSDEJ.Solves


