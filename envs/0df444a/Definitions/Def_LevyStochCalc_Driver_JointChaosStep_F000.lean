-- Prove2me | Definitions.Def_LevyStochCalc_Driver_JointChaosStep_F000
-- name    : LevyStochCalc_Driver_JointChaosStep_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:30:39.057742+00:00
-- url     : https://prove2.me/theorems/a045e902-5cd4-4ff5-a767-e541e67ee4df
-- title:
--   Source declarations: LevyStochCalc.Driver.JointChaosStep
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.JointChaosStep. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ChaosStep_F000
import Definitions.Def_LevyStochCalc_Driver_GridIncrement_F000
import Definitions.Def_LevyStochCalc_Poisson_ChaosStep_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint chaos element of one step of a Lévy driver

For a Lévy driver, a coordinate `j`, a step `(a, b]` and a mark set `A`, the bidegree-`(n, m)`
element of the step is the product `H_n(ΔWʲ; b - a) C_m(N(B); ν̂(B))` of the degree-`n` Wiener
chaos element of the increment `ΔWʲ = Wʲ_b - Wʲ_a` and the degree-`m` Poisson chaos element of
the strip `B = (a, b] ×ˢ A`. Since `σ(W)` and `σ(N)` are independent, the expectation of a
product of a function of the increment and a function of the count factors, so the `L²` pairing
of two such elements is the product of the Brownian and the Poisson pairings,
`E[J_(n, m) J_(n', m')] = δ_(n n') δ_(m m') n! τ ^ n m! λ ^ m` for `τ = b - a` and
`λ = (b - a) ν(A)`. Distinct bidegrees are therefore orthogonal, and a fortiori so are distinct
total degrees `n + m`. The step tuple is independent of the joint filtration at `a`, so the
conditional pairing at that node is the same constant.

One Brownian coordinate and one mark set are covered: these are polynomials of the single
increment `ΔWʲ` and the single count `N(B)`, with no mark profile beyond the indicator of `A`.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosStep` — the bidegree-`(n, m)` element of a step.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.indepFun_increment_count` — a Brownian increment of the driver
  is independent of a count of its Poisson random measure.
* `LevyStochCalc.Driver.LevyDriver.integral_increment_count_mul` — the expectation of a product
  of a function of an increment and a function of a count factors.
* `LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStep` — square integrability.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStep_mul` —
  `E[J_(n, m) J_(n', m')] = δ_(n n') δ_(m m') n! τ ^ n m! λ ^ m`.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStep_mul_eq_zero_of_add_ne` — orthogonality
  across total degrees.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStep_mul_eq_zero` — orthogonality across
  bidegrees.
* `LevyStochCalc.Driver.LevyDriver.condExp_jointChaosStep_mul` — the conditional pairing at the
  node preceding the step.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

section Independence

variable {γ δ : Type*} [MeasurableSpace γ] [MeasurableSpace δ]

/-- A variable measurable for the Brownian σ-algebra of the driver is independent of a variable
measurable for its Poisson σ-algebra. -/
theorem indepFun_of_measurable (D : LevyDriver.{u, v, w} P d ν) {X : Ω → γ} {Y : Ω → δ}
    (hX : Measurable[⨆ i, Brownian.sigmaBrownian (D.W.W i)] X)
    (hY : Measurable[sigmaPoisson D.N] Y) : IndepFun X Y P :=
  (IndepFun_iff_Indep _ _ _).2
    (indep_of_indep_of_le_right (indep_of_indep_of_le_left D.indep hX.comap_le) hY.comap_le)
/-- An increment of one Brownian coordinate of the driver is independent of a count of its
Poisson random measure. -/
theorem indepFun_increment_count (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (s t : ℝ)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) :
    IndepFun (fun ω => (D.W.W j).W t ω - (D.W.W j).W s ω) (fun ω => D.N.N ω B) P :=
  D.indepFun_of_measurable
    (Measurable.of_comap_le ((Brownian.comap_increment_le_sigmaBrownian (D.W.W j) s t).trans
      (le_iSup (fun i => Brownian.sigmaBrownian (D.W.W i)) j)))
    (Measurable.of_comap_le (comap_count_le_sigmaPoisson D.N hB))
/-- The vector of Brownian increments of the driver over a step is independent of a count of its
Poisson random measure. -/
theorem indepFun_vectorIncrement_count (D : LevyDriver.{u, v, w} P d ν) (s t : ℝ)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) :
    IndepFun (fun ω (i : Fin d) => (D.W.W i).W t ω - (D.W.W i).W s ω)
      (fun ω => D.N.N ω B) P :=
  D.indepFun_of_measurable
    (@measurable_pi_lambda Ω _ _ (⨆ i, Brownian.sigmaBrownian (D.W.W i)) _ _
      fun i => Measurable.of_comap_le
        ((Brownian.comap_increment_le_sigmaBrownian (D.W.W i) s t).trans
          (le_iSup (fun i => Brownian.sigmaBrownian (D.W.W i)) i)))
    (Measurable.of_comap_le (comap_count_le_sigmaPoisson D.N hB))
/-- The expectation of a product of a function of a Brownian increment of the driver and a
function of a count of its Poisson random measure factors. -/
theorem integral_increment_count_mul (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (s t : ℝ)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) {f : ℝ → ℝ} {g : ℝ≥0∞ → ℝ} (hf : Measurable f)
    (hg : Measurable g) :
    ∫ ω, f ((D.W.W j).W t ω - (D.W.W j).W s ω) * g (D.N.N ω B) ∂P
      = (∫ ω, f ((D.W.W j).W t ω - (D.W.W j).W s ω) ∂P) * ∫ ω, g (D.N.N ω B) ∂P :=
  (D.indepFun_increment_count j s t hB).integral_fun_comp_mul_comp
    (((D.W.W j).measurable_eval t).sub ((D.W.W j).measurable_eval s)).aemeasurable
    (D.N.measurable_eval hB).aemeasurable hf.aestronglyMeasurable hg.aestronglyMeasurable
/-- The expectation of a product of a function of the vector of Brownian increments of the driver
and a function of a count of its Poisson random measure factors. -/
theorem integral_vectorIncrement_count_mul (D : LevyDriver.{u, v, w} P d ν) (s t : ℝ)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) {f : (Fin d → ℝ) → ℝ} {g : ℝ≥0∞ → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    ∫ ω, f (fun i => (D.W.W i).W t ω - (D.W.W i).W s ω) * g (D.N.N ω B) ∂P
      = (∫ ω, f (fun i => (D.W.W i).W t ω - (D.W.W i).W s ω) ∂P)
        * ∫ ω, g (D.N.N ω B) ∂P :=
  (D.indepFun_vectorIncrement_count s t hB).integral_fun_comp_mul_comp
    (measurable_pi_lambda _ fun i =>
      ((D.W.W i).measurable_eval t).sub ((D.W.W i).measurable_eval s)).aemeasurable
    (D.N.measurable_eval hB).aemeasurable hf.aestronglyMeasurable hg.aestronglyMeasurable
end Independence

/-- The joint chaos element of bidegree `(n, m)` of the step `(a, b]` of the driver over the mark
set `A`: the product of the degree-`n` Wiener chaos element of the increment of the coordinate
`j` and the degree-`m` Poisson chaos element of the strip `(a, b] ×ˢ A`. -/
noncomputable def jointChaosStep (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (n m : ℕ)
    (a b : ℝ≥0) (A : Set E) (ω : Ω) : ℝ :=
  Probability.wienerChaosStep n (b - a) ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
    * Poisson.poissonChaosStep D.N m (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω
/-- The bidegree-`(0, 0)` element of a step of the driver is `1`. -/
@[simp] theorem jointChaosStep_zero_zero (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (a b : ℝ≥0)
    (A : Set E) (ω : Ω) : D.jointChaosStep j 0 0 a b A ω = 1 := by
  simp [jointChaosStep]
/-- The bidegree-`(1, 1)` element is the product of the Brownian increment and the compensated
count of the strip. -/
theorem jointChaosStep_one_one (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (a b : ℝ≥0)
    (A : Set E) (ω : Ω) :
    D.jointChaosStep j 1 1 a b A ω
      = ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
        * D.N.compensated (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω := by
  simp [jointChaosStep]
/-- A joint chaos element of a step of the driver over a measurable mark set is
measurable. -/
theorem measurable_jointChaosStep (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (n m : ℕ)
    (a b : ℝ≥0) {A : Set E} (hA : MeasurableSet A) :
    Measurable (D.jointChaosStep j n m a b A) :=
  ((Probability.measurable_wienerChaosStep n _).comp
      (((D.W.W j).measurable_eval _).sub ((D.W.W j).measurable_eval _))).mul
    (Poisson.measurable_poissonChaosStep D.N m (measurableSet_Ioc.prod hA))
end LevyDriver

end LevyStochCalc.Driver


