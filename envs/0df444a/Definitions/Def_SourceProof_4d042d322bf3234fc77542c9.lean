-- Prove2me | Definitions.Def_SourceProof_4d042d322bf3234fc77542c9
-- name    : SourceProof_4d042d322bf3234fc77542c9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:59:15.666801+00:00
-- url     : https://prove2.me/theorems/a91e4234-1343-4218-8496-f98ebce139af
-- title:
--   LevyStochCalc source module: SourceProof_4d042d322bf3234fc77542c9
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfileC_mul_cross` comes from the `LevyStochCalc.Driver.JointChaosProfileComplex` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_4d042d322bf3234fc77542c9 (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (hA' : ∀ l, MeasurableSet (A' l))
    (hAν' : ∀ l, ν (A' l) ≠ ⊤) (hd' : Pairwise fun k l => Disjoint (A' k) (A' l))
    (r s r' s' : ℕ) (c : Fin p → ℂ) (c' : Fin q → ℂ) :
    ∫ ω, D.jointChaosStepProfileC j r s a b A c ω
        * D.jointChaosStepProfileC j r' s' a b A' c' ω ∂P
      = (((if r = r' then (r.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ r else 0 : ℝ)) : ℂ)
        * (if s = s' then (s.factorial : ℂ) * ((((b : ℝ) - (a : ℝ) : ℝ) : ℂ)
            * ∑ k, ∑ l, c k * c' l * ((ν (A k ∩ A' l)).toReal : ℂ)) ^ s else 0) := by
  have hBm : ∀ k, MeasurableSet (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) :=
    fun k => measurableSet_Ioc.prod (hA k)
  have hBm' : ∀ l, MeasurableSet (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A' l) :=
    fun l => measurableSet_Ioc.prod (hA' l)
  have hincr : Measurable[⨆ i, LevyStochCalc.Brownian.sigmaBrownian (D.W.W i)]
      (fun ω => (D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) :=
    Measurable.of_comap_le
      ((LevyStochCalc.Brownian.comap_increment_le_sigmaBrownian (D.W.W j) (a : ℝ) (b : ℝ)).trans
        (le_iSup (fun i => LevyStochCalc.Brownian.sigmaBrownian (D.W.W i)) j))
  set X : Ω → ℂ := fun ω => ((LevyStochCalc.Probability.wienerChaosStep r (b - a)
      ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
    * LevyStochCalc.Probability.wienerChaosStep r' (b - a) ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) : ℝ) : ℂ)
    with hXdef
  set Y : Ω → ℂ := fun ω =>
    LevyStochCalc.Poisson.markedChaosDegreeC D.N s (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω
      * LevyStochCalc.Poisson.markedChaosDegreeC D.N s' (fun l => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A' l) c' ω with hYdef
  have hX : Measurable[⨆ i, LevyStochCalc.Brownian.sigmaBrownian (D.W.W i)] X :=
    Complex.measurable_ofReal.comp (((LevyStochCalc.Probability.measurable_wienerChaosStep r _).mul
      (LevyStochCalc.Probability.measurable_wienerChaosStep r' _)).comp hincr)
  have hY : Measurable[LevyStochCalc.Driver.sigmaPoisson D.N] Y :=
    (D.measurable_markedChaosDegreeC_sigmaPoisson s hBm c).mul
      (D.measurable_markedChaosDegreeC_sigmaPoisson s' hBm' c')
  have hXm : Measurable X := hX.mono (iSup_le fun i => LevyStochCalc.Brownian.sigmaBrownian_le _) le_rfl
  have hYm : Measurable Y := hY.mono (LevyStochCalc.Driver.sigmaPoisson_le _) le_rfl
  have hrw : ∀ ω, (LevyStochCalc.Driver.LevyDriver.jointChaosStepProfileC D) j r s a b A c ω
      * (LevyStochCalc.Driver.LevyDriver.jointChaosStepProfileC D) j r' s' a b A' c' ω = X ω * Y ω := by
    intro ω
    simp only [LevyStochCalc.Driver.LevyDriver.jointChaosStepProfileC, hXdef, hYdef]
    push_cast
    ring
  rw [integral_congr_ae (Eventually.of_forall hrw),
    (D.indepFun_of_measurable hX hY).integral_fun_mul_eq_mul_integral
      hXm.aestronglyMeasurable hYm.aestronglyMeasurable]
  congr 1
  · rw [hXdef, integral_complex_ofReal,
      LevyStochCalc.Brownian.BrownianMotion.integral_wienerChaosStep_increment_mul (D.W.W j) a b hab r r',
      NNReal.coe_sub hab]
  · exact _root_.Prove2MeSourceProof.h_75f5d72d7cf5f46600559b33 D.N a.coe_nonneg (by exact_mod_cast hab)
      hA hAν hd hA' hAν' hd' s s' c c'
end Elements

/-! ### The pairing at the node preceding the step -/

section Node

variable {Ω : Type u} {M 𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {d : ℕ}

end Node

end LevyStochCalc.Driver.LevyDriver


