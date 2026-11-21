-- Prove2me | Definitions.Def_SourceProof_37a7ff2c7873067deccef303
-- name    : SourceProof_37a7ff2c7873067deccef303
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:39:12.840649+00:00
-- url     : https://prove2.me/theorems/a3c36aad-e008-443a-9c57-7e40adc181e7
-- title:
--   LevyStochCalc source module: SourceProof_37a7ff2c7873067deccef303
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_mul` comes from the `LevyStochCalc.Driver.JointChaosProfile` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosProfile_F000

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

/-! ### The element of a bidegree at a mark profile -/


theorem _root_.Prove2MeSourceProof.h_37a7ff2c7873067deccef303 (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (n m n' m' : ℕ)
    (c c' : Fin p → ℝ) :
    ∫ ω, D.jointChaosStepProfile j n m a b A c ω
        * D.jointChaosStepProfile j n' m' a b A c' ω ∂P
      = (if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
        * (if m = m' then (m.factorial : ℝ)
            * (∑ k, c k * c' k * (((b : ℝ) - (a : ℝ)) * (ν (A k)).toReal)) ^ m else 0) := by
  classical
  have hBm : ∀ k, MeasurableSet (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) :=
    fun k => measurableSet_Ioc.prod (hA k)
  have hincr : Measurable[⨆ i, LevyStochCalc.Brownian.sigmaBrownian (D.W.W i)]
      (fun ω => (D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) :=
    Measurable.of_comap_le
      ((LevyStochCalc.Brownian.comap_increment_le_sigmaBrownian (D.W.W j) (a : ℝ) (b : ℝ)).trans
        (le_iSup (fun i => LevyStochCalc.Brownian.sigmaBrownian (D.W.W i)) j))
  have hX : Measurable[⨆ i, LevyStochCalc.Brownian.sigmaBrownian (D.W.W i)]
      (fun ω => LevyStochCalc.Probability.wienerChaosStep n (b - a)
          ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
        * LevyStochCalc.Probability.wienerChaosStep n' (b - a)
          ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)) :=
    ((LevyStochCalc.Probability.measurable_wienerChaosStep n _).mul
      (LevyStochCalc.Probability.measurable_wienerChaosStep n' _)).comp hincr
  have hY : Measurable[LevyStochCalc.Driver.sigmaPoisson D.N]
      (fun ω => LevyStochCalc.Poisson.markedChaosDegree D.N m (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω
        * LevyStochCalc.Poisson.markedChaosDegree D.N m' (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c' ω) :=
    (D.measurable_markedChaosDegree_sigmaPoisson m hBm c).mul
      (D.measurable_markedChaosDegree_sigmaPoisson m' hBm c')
  have hXm : Measurable fun ω => LevyStochCalc.Probability.wienerChaosStep n (b - a)
      ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
    * LevyStochCalc.Probability.wienerChaosStep n' (b - a)
      ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) :=
    ((LevyStochCalc.Probability.measurable_wienerChaosStep n _).mul
      (LevyStochCalc.Probability.measurable_wienerChaosStep n' _)).comp
      (((D.W.W j).measurable_eval _).sub ((D.W.W j).measurable_eval _))
  have hYm : Measurable fun ω =>
      LevyStochCalc.Poisson.markedChaosDegree D.N m (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω
        * LevyStochCalc.Poisson.markedChaosDegree D.N m' (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c' ω :=
    (LevyStochCalc.Poisson.measurable_markedChaosDegree D.N m hBm c).mul
      (LevyStochCalc.Poisson.measurable_markedChaosDegree D.N m' hBm c')
  have hrw : ∀ ω : Ω, (LevyStochCalc.Driver.LevyDriver.jointChaosStepProfile D) j n m a b A c ω
      * (LevyStochCalc.Driver.LevyDriver.jointChaosStepProfile D) j n' m' a b A c' ω
      = (LevyStochCalc.Probability.wienerChaosStep n (b - a)
            ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
          * LevyStochCalc.Probability.wienerChaosStep n' (b - a)
            ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω))
        * (LevyStochCalc.Poisson.markedChaosDegree D.N m (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω
          * LevyStochCalc.Poisson.markedChaosDegree D.N m'
              (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c' ω) := by
    intro ω
    simp only [LevyStochCalc.Driver.LevyDriver.jointChaosStepProfile]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw),
    (D.indepFun_of_measurable hX hY).integral_fun_mul_eq_mul_integral
      hXm.aestronglyMeasurable hYm.aestronglyMeasurable]
  congr 1
  · rw [LevyStochCalc.Brownian.BrownianMotion.integral_wienerChaosStep_increment_mul (D.W.W j) a b hab n n',
      NNReal.coe_sub hab]
  · exact LevyStochCalc.Poisson.integral_markedChaosDegree_strip_mul D.N a.coe_nonneg
      (by exact_mod_cast hab) hA hAν hd m m' c c'
end LevyDriver

end LevyStochCalc.Driver


