-- Prove2me | Definitions.Def_LevyStochCalc_Driver_JointChaosProfile_F000
-- name    : LevyStochCalc_Driver_JointChaosProfile_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:41:57.75822+00:00
-- url     : https://prove2.me/theorems/9e79e1a6-8ecb-4b95-b6e4-3f8bb804aa61
-- title:
--   Source declarations: LevyStochCalc.Driver.JointChaosProfile
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.JointChaosProfile. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosStep_F001
import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegree_F001
import Definitions.Def_LevyStochCalc_Poisson_SimpleChaosDegree_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The joint chaos element of one step of a Lévy driver at a simple mark profile

For a Lévy driver, a coordinate `j`, a step `(a, b]` and a finite pairwise disjoint family `A` of
mark sets of finite intensity carrying a profile `c` constant on each of them, the
bidegree-`(n, m)` element of the step is the product `H_n(ΔWʲ; b - a) D_m(c)` of the degree-`n`
Wiener chaos element of the increment `ΔWʲ = Wʲ_b - Wʲ_a` and the degree-`m` chaos element of the
profile over the strips `(a, b] ×ˢ A k`. Since `σ(W)` and `σ(N)` are independent, the expectation
of a product of a function of the increment and a function of the counts of the strips factors,
so the `L²` pairing of two such elements is the product of the Hermite and the Charlier factor,
`E[J_(n, m)(c) J_(n', m')(c')] = δ_(n n') δ_(m m') n! τ ^ n m! ⟨c, c'⟩ ^ m` for `τ = b - a` and
the bilinear form `⟨c, c'⟩ = ∑_k c_k c'_k τ ν(A k)`. Distinct bidegrees are therefore orthogonal,
and a fortiori so are distinct total degrees `n + m`. The step tuple is independent of the joint
filtration at `a`, so the conditional pairing at that node is the same constant.

One Brownian coordinate is covered, and the profile is constant on the sets of one given family:
no mode of `L²(ν)` beyond such combinations of indicators enters. On a one-set family the element
is the single-mark-set element of a step scaled by `c 0 ^ m`.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosStepProfile` — the bidegree-`(n, m)` element of a
  step at a mark profile.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.measurable_markedChaosDegree_sigmaPoisson` — a degree element
  of a profile is measurable for the Poisson σ-algebra of the driver.
* `LevyStochCalc.Driver.LevyDriver.indepFun_increment_markedChaosDegree` — a Brownian increment
  of the driver is independent of a degree element of a profile of its Poisson random measure.
* `LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStepProfile` — square integrability.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_mul` —
  `E[J_(n,m)(c) J_(n',m')(c')] = δ_(n n') δ_(m m') n! τ ^ n m! ⟨c, c'⟩ ^ m`.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_sq` — the second moment as the
  product of the Hermite and the Charlier factor.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_mul_eq_zero`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_mul_eq_zero_of_add_ne` —
  orthogonality across bidegrees and across total degrees.
* `LevyStochCalc.Driver.LevyDriver.condExp_jointChaosStepProfile_mul` — the conditional pairing
  at the node preceding the step.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Independence of the Brownian and the Poisson data of a step -/

namespace LevyDriver

/-- A degree element of a profile on a finite family of measurable regions is measurable for the
Poisson σ-algebra of the driver. -/
theorem measurable_markedChaosDegree_sigmaPoisson (D : LevyDriver.{u, v, w} P d ν) {p : ℕ}
    (s : ℕ) {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k)) (c : Fin p → ℝ) :
    Measurable[sigmaPoisson D.N] (Poisson.markedChaosDegree D.N s B c) :=
  Finset.measurable_sum _ fun α _ =>
    (Finset.univ.measurable_prod fun k _ =>
        (((Probability.continuous_charlierScaled (α k) _).measurable).comp
            ENNReal.measurable_toReal).comp
          (Measurable.of_comap_le (comap_count_le_sigmaPoisson D.N (hB k)))).const_mul _
/-- An increment of one Brownian coordinate of the driver is independent of a degree element of a
profile on a finite family of measurable regions of its Poisson random measure. -/
theorem indepFun_increment_markedChaosDegree (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (s t : ℝ) {p : ℕ} (m : ℕ) {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (c : Fin p → ℝ) :
    IndepFun (fun ω => (D.W.W j).W t ω - (D.W.W j).W s ω)
      (Poisson.markedChaosDegree D.N m B c) P :=
  D.indepFun_of_measurable
    (Measurable.of_comap_le ((Brownian.comap_increment_le_sigmaBrownian (D.W.W j) s t).trans
      (le_iSup (fun i => Brownian.sigmaBrownian (D.W.W i)) j)))
    (D.measurable_markedChaosDegree_sigmaPoisson m hB c)
/-! ### The element of a bidegree at a mark profile -/

/-- The joint chaos element of bidegree `(n, m)` of the step `(a, b]` of the driver at a profile
`c` on a finite family `A` of mark sets: the product of the degree-`n` Wiener chaos element of the
increment of the coordinate `j` and the degree-`m` chaos element of the profile over the strips
`(a, b] ×ˢ A k`. -/
noncomputable def jointChaosStepProfile (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (n m : ℕ)
    (a b : ℝ≥0) {p : ℕ} (A : Fin p → Set E) (c : Fin p → ℝ) (ω : Ω) : ℝ :=
  Probability.wienerChaosStep n (b - a) ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
    * Poisson.markedChaosDegree D.N m (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω
/-- The bidegree-`(0, 0)` element of a step of the driver at a mark profile is `1`. -/
@[simp] theorem jointChaosStepProfile_zero_zero (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (a b : ℝ≥0) {p : ℕ} (A : Fin p → Set E) (c : Fin p → ℝ) (ω : Ω) :
    D.jointChaosStepProfile j 0 0 a b A c ω = 1 := by
  simp [jointChaosStepProfile]
/-- On a one-set family the element at a mark profile is the single-mark-set element of the step
scaled by the `m`-th power of the value of the profile. -/
theorem jointChaosStepProfile_fin_one (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (n m : ℕ)
    (a b : ℝ≥0) (A : Fin 1 → Set E) (c : Fin 1 → ℝ) (ω : Ω) :
    D.jointChaosStepProfile j n m a b A c ω = c 0 ^ m * D.jointChaosStep j n m a b (A 0) ω := by
  rw [jointChaosStepProfile, Poisson.markedChaosDegree_fin_one, jointChaosStep]
  ring
/-- A joint chaos element of a step of the driver at a profile on a family of measurable mark
sets is measurable. -/
theorem measurable_jointChaosStepProfile (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (n m : ℕ)
    (a b : ℝ≥0) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k)) (c : Fin p → ℝ) :
    Measurable (D.jointChaosStepProfile j n m a b A c) :=
  ((Probability.measurable_wienerChaosStep n _).comp
      (((D.W.W j).measurable_eval _).sub ((D.W.W j).measurable_eval _))).mul
    (Poisson.measurable_markedChaosDegree D.N m (fun k => measurableSet_Ioc.prod (hA k)) c)
/-- A joint chaos element of a step of the driver at a profile on a finite pairwise disjoint
family of mark sets of finite intensity lies in `L²`. -/
theorem memLp_two_jointChaosStepProfile (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (n m : ℕ)
    (c : Fin p → ℝ) :
    MemLp (D.jointChaosStepProfile j n m a b A c) 2 P := by
  have hBm : ∀ k, MeasurableSet (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) :=
    fun k => measurableSet_Ioc.prod (hA k)
  have hBd : Pairwise fun k l => Disjoint (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k)
      (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A l) := fun k l hkl =>
    Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 (hd hkl) hx.2 hx'.2
  have hBfin : ∀ k, Poisson.referenceIntensity ν (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) ≠ ⊤ :=
    fun k => Poisson.referenceIntensity_strip_ne_top a.coe_nonneg (hAν k)
  have hW : Integrable (fun ω => Probability.wienerChaosStep n (b - a)
      ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) ^ 2) P := by
    simpa only [pow_two] using
      Brownian.BrownianMotion.integrable_wienerChaosStep_increment_mul (D.W.W j) a b hab n n
  have hN : Integrable (fun ω => Poisson.markedChaosDegree D.N m
      (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω ^ 2) P := by
    simpa only [pow_two] using
      Poisson.integrable_markedChaosDegree_mul D.N hBm hBd hBfin m m c c
  have hcomp : IndepFun
      (fun ω => Probability.wienerChaosStep n (b - a)
        ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) ^ 2)
      (fun ω => Poisson.markedChaosDegree D.N m
        (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω ^ 2) P :=
    (D.indepFun_increment_markedChaosDegree j (a : ℝ) (b : ℝ) m hBm c).comp
      ((Probability.measurable_wienerChaosStep n _).pow_const 2) (measurable_id.pow_const 2)
  refine (memLp_two_iff_integrable_sq
    (D.measurable_jointChaosStepProfile j n m a b hA c).aestronglyMeasurable).2 ?_
  have hmul := hcomp.integrable_mul hW hN
  simp only [jointChaosStepProfile, mul_pow]
  exact hmul
end LevyDriver

end LevyStochCalc.Driver


