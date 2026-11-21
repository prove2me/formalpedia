-- Prove2me | Definitions.Def_SourceProof_ebefc144eb70c8d3856a45a9
-- name    : SourceProof_ebefc144eb70c8d3856a45a9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:02:01.94618+00:00
-- url     : https://prove2.me/theorems/c3125699-532a-457a-bfcf-7f1c68900e75
-- title:
--   LevyStochCalc source module: SourceProof_ebefc144eb70c8d3856a45a9
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStepProfileC` comes from the `LevyStochCalc.Driver.JointChaosProfileComplex` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosProfileComplex_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Complex joint chaos elements of a step at a mark profile, across mark families

For a Lévy driver, a coordinate `j`, a step `(a, b]` with `τ = b − a`, a finite pairwise
disjoint family `A` of mark sets of finite intensity and a complex profile `c` constant on each of
them, the complex bidegree-`(r, s)` element of the step is `X_(r, s)(c; A) = H_r(ΔWʲ; τ) D_s(c)`,
the product of the degree-`r` Wiener chaos element of the increment and the degree-`s` element of
the profile over the strips `(a, b] ×ˢ A k`. The Brownian and the Poisson factors are independent,
so the bilinear moment of two such elements over different families `A`, `A'` factors into the
Hermite and the Charlier Gram across the families,

  `E[X_(r, s)(c; A) X_(r', s')(c'; A')] = δ_(r r') r! τ ^ r δ_(s s') s! (τ ⟨c, c'⟩) ^ s`,

with `⟨c, c'⟩ = ∑_(k, l) c_k c'_l ν(A k ∩ A' l)`; distinct bidegrees, and a fortiori distinct total
degrees, are orthogonal whatever the two families. Every element of the step is measurable for
the σ-algebra of the step over the strips of both families, which is independent of the joint
filtration at `a`, and also of the augmentation of its join with an initial σ-algebra independent
of the whole filtration. So against a coefficient measurable for such a node σ-algebra the pairing
of two elements is the mean of the coefficient times their pairing, and the conditional pairing
given the node σ-algebra is the constant pairing.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosStepProfileC` — the complex bidegree-`(r, s)` element.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStepProfileC` — square integrability.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfileC_mul_cross`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfileC_mul_conj_cross` — the bidegree
  Gram across two mark families.
* `LevyStochCalc.Driver.LevyDriver.indep_stepSigma_filtration`,
  `LevyStochCalc.Driver.LevyDriver.indep_stepSigma_aug_sup` — the σ-algebra of the step is
  independent of the joint filtration at the node, and of the augmentation of its join with an
  independent initial σ-algebra.
* `LevyStochCalc.Driver.LevyDriver.integral_mul_eq_mul_integral_of_indep_stepSigma` — the pairing
  of a variable of the step against a coefficient measurable at the node.
* `LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointChaosStepProfileC_mul_conj` — the
  same for the Hermitian pairing of two elements over different families.
* `LevyStochCalc.Driver.LevyDriver.condExp_jointChaosStepProfileC_mul_conj` — the conditional
  Hermitian pairing at the node is the constant Gram.
-/

namespace LevyStochCalc.Driver.LevyDriver

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability LevyStochCalc.Poisson Finset
  Filter
open scoped NNReal ENNReal Topology

universe u v w

section Elements

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Measurability -/

/-! ### The complex bidegree element -/


theorem _root_.Prove2MeSourceProof.h_ebefc144eb70c8d3856a45a9 (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (r s : ℕ)
    (c : Fin p → ℂ) :
    MemLp (D.jointChaosStepProfileC j r s a b A c) 2 P := by
  have hBm : ∀ k, MeasurableSet (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) :=
    fun k => measurableSet_Ioc.prod (hA k)
  have hBd : Pairwise fun k l => Disjoint (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k)
      (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A l) := fun k l hkl =>
    Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 (hd hkl) hx.2 hx'.2
  have hBfin : ∀ k, LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) ≠ ⊤ :=
    fun k => LevyStochCalc.Poisson.referenceIntensity_strip_ne_top a.coe_nonneg (hAν k)
  have hW : Integrable (fun ω => ‖(LevyStochCalc.Probability.wienerChaosStep r (b - a)
      ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) : ℂ)‖ ^ 2) P :=
    (LevyStochCalc.Brownian.BrownianMotion.memLp_two_wienerChaosStep_increment (D.W.W j) a b hab
      r).ofReal.integrable_norm_pow two_ne_zero
  have hN : Integrable (fun ω => ‖LevyStochCalc.Poisson.markedChaosDegreeC D.N s
      (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω‖ ^ 2) P :=
    (LevyStochCalc.Poisson.memLp_two_markedChaosDegreeC D.N hBm hBd hBfin s c).integrable_norm_pow two_ne_zero
  have hind : IndepFun
      (fun ω => ‖(LevyStochCalc.Probability.wienerChaosStep r (b - a)
        ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) : ℂ)‖ ^ 2)
      (fun ω => ‖LevyStochCalc.Poisson.markedChaosDegreeC D.N s
        (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω‖ ^ 2) P :=
    D.indepFun_of_measurable
      (((continuous_norm.pow 2).measurable.comp
        (Complex.measurable_ofReal.comp (LevyStochCalc.Probability.measurable_wienerChaosStep r _))).comp
          (Measurable.of_comap_le
            ((LevyStochCalc.Brownian.comap_increment_le_sigmaBrownian (D.W.W j) (a : ℝ) (b : ℝ)).trans
              (le_iSup (fun i => LevyStochCalc.Brownian.sigmaBrownian (D.W.W i)) j))))
      ((continuous_norm.pow 2).measurable.comp
        (D.measurable_markedChaosDegreeC_sigmaPoisson s hBm c))
  refine (memLp_two_iff_integrable_sq_norm
    (D.measurable_jointChaosStepProfileC j r s a b hA c).aestronglyMeasurable).2 ?_
  refine (hind.integrable_mul hW hN).congr (Eventually.of_forall fun ω => ?_)
  simp only [Pi.mul_apply, LevyStochCalc.Driver.LevyDriver.jointChaosStepProfileC, norm_mul, mul_pow]
end Elements

/-! ### The pairing at the node preceding the step -/

section Node

variable {Ω : Type u} {M 𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {d : ℕ}

end Node

end LevyStochCalc.Driver.LevyDriver


