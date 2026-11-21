-- Prove2me | Definitions.Def_SourceProof_dc0655f17321fa2fa8890ee8
-- name    : SourceProof_dc0655f17321fa2fa8890ee8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T15:12:14.499935+00:00
-- url     : https://prove2.me/theorems/6a815754-8ca1-4798-b6e4-fa6ce95f12ed
-- title:
--   LevyStochCalc source module: SourceProof_dc0655f17321fa2fa8890ee8
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.SimpleProfile.integral_stepIntegral_mul` comes from the `LevyStochCalc.Poisson.SimpleProfile` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_SimpleProfile_F001
import Definitions.Def_SourceProof_99ba0164ebb17461a6598da8
import Definitions.Def_SourceProof_adfffb5c0bed4c951bccc3c4

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Simple mark profiles and their compensated step integrals

A *simple mark profile* for an intensity `ν` on the mark space is a finite family of pairwise
disjoint mark sets of finite intensity carrying constant coefficients, `∑ₖ cₖ 𝟙_{Bₖ}`. Every
square-integrable mark profile is the `L²(ν)` limit of simple profiles, obtained from the nonzero
level sets of square-integrable simple functions approximating it in `L²(ν)`; a bounded one is
the limit of simple profiles obeying the same bound, obtained from the simple functions
approximating it inside the interval the bound cuts out.

The compensated integral of a simple profile over the step `(a, b]` is
`∑ₖ cₖ Ñ((a, b] × Bₖ)`. The `L²(P)` pairing of two such integrals over a common step is
`(b − a) ∫ f g dν`, so profiles converging in `L²(ν)` have compensated integrals converging in
`L²(P)`.

## Main definitions

* `LevyStochCalc.Poisson.SimpleProfile` — a simple mark profile.
* `LevyStochCalc.Poisson.SimpleProfile.toFun` — the function it carries.
* `LevyStochCalc.Poisson.SimpleProfile.stepIntegral` — its compensated integral over a step.

## Main statements

* `LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2_of_memLp` — approximation of a
  square-integrable mark profile by simple profiles.
* `LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2` — approximation of a bounded
  square-integrable mark profile by simple profiles obeying the same bound.
* `LevyStochCalc.Poisson.SimpleProfile.integral_stepIntegral_mul` — the `L²(P)` pairing of two
  compensated step integrals.
* `LevyStochCalc.Poisson.SimpleProfile.eLpNorm_stepIntegral_sub` — the isometry
  `‖J(f) − J(g)‖_{L²(P)} = √(b − a) ‖f − g‖_{L²(ν)}`.
* `LevyStochCalc.Poisson.exists_memLp_tendsto_stepIntegral` — convergence of the compensated
  integrals in `L²(P)`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

namespace SimpleProfile

/-! ### The compensated integral of a simple profile over a step -/

variable (N : PoissonRandomMeasure P ν)


theorem _root_.Prove2MeSourceProof.h_dc0655f17321fa2fa8890ee8 (G G' : SimpleProfile E ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    ∫ ω, G.stepIntegral N a b ω * G'.stepIntegral N a b ω ∂P
      = (b - a) * ∫ e, G.toFun e * G'.toFun e ∂ν := by
  have hmemk : ∀ k : Fin G.K, MemLp (fun ω => G.c k
      * N.compensated (Set.Ioc a b ×ˢ G.B k) ω) 2 P :=
    fun k => (G.memLp_compensated_step N ha b k).const_mul _
  have hmeml : ∀ l : Fin G'.K, MemLp (fun ω => G'.c l
      * N.compensated (Set.Ioc a b ×ˢ G'.B l) ω) 2 P :=
    fun l => (G'.memLp_compensated_step N ha b l).const_mul _
  have hint : ∀ (k : Fin G.K) (l : Fin G'.K), Integrable (fun ω =>
      (G.c k * N.compensated (Set.Ioc a b ×ˢ G.B k) ω)
        * (G'.c l * N.compensated (Set.Ioc a b ×ˢ G'.B l) ω)) P :=
    fun k l => (hmemk k).integrable_mul (hmeml l)
  have hcross : ∀ (k : Fin G.K) (l : Fin G'.K),
      ∫ ω, N.compensated (Set.Ioc a b ×ˢ G.B k) ω
        * N.compensated (Set.Ioc a b ×ˢ G'.B l) ω ∂P
        = (b - a) * (ν (G.B k ∩ G'.B l)).toReal := by
    intro k l
    rw [_root_.Prove2MeSourceProof.h_99ba0164ebb17461a6598da8 N (measurableSet_Ioc.prod (G.B_measurable k))
      (measurableSet_Ioc.prod (G'.B_measurable l))
      (by rw [LevyStochCalc.Poisson.referenceIntensity_Ioc_prod' _ ha]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (G.B_finite k))
      (by rw [LevyStochCalc.Poisson.referenceIntensity_Ioc_prod' _ ha]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (G'.B_finite l))]
    rw [Set.prod_inter_prod, Set.inter_self, LevyStochCalc.Poisson.referenceIntensity_Ioc_prod' _ ha,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
  simp_rw [LevyStochCalc.Poisson.SimpleProfile.stepIntegral, Fintype.sum_mul_sum]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l,
    _root_.Prove2MeSourceProof.h_adfffb5c0bed4c951bccc3c4, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => hint k l, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (fun ω => (G.c k * N.compensated (Set.Ioc a b ×ˢ G.B k) ω)
        * (G'.c l * N.compensated (Set.Ioc a b ×ˢ G'.B l) ω))
      = fun ω => (G.c k * G'.c l) * (N.compensated (Set.Ioc a b ×ˢ G.B k) ω
        * N.compensated (Set.Ioc a b ×ˢ G'.B l) ω) from by funext ω; ring,
    integral_const_mul, hcross k l]
  ring
/-! ### Simple profiles from simple functions -/

end SimpleProfile

/-! ### Approximation of a square-integrable mark profile -/

/-! ### Convergence of the compensated step integrals -/

end LevyStochCalc.Poisson


