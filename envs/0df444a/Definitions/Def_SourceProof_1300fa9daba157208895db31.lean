-- Prove2me | Definitions.Def_SourceProof_1300fa9daba157208895db31
-- name    : SourceProof_1300fa9daba157208895db31
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:03:04.2381+00:00
-- url     : https://prove2.me/theorems/cc6bc26a-8c77-4fdb-80df-50c6a1875dda
-- title:
--   LevyStochCalc source module: SourceProof_1300fa9daba157208895db31
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.tendsto_eLpNorm_profileExpVector_sub` comes from the `LevyStochCalc.Poisson.ProfileExpVectorCont` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProductMoments_F001
import Definitions.Def_LevyStochCalc_Poisson_ProfileExpVector_F000
import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F000
import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F001
import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F002
import Definitions.Def_LevyStochCalc_Probability_L2Series_F001
import Definitions.Def_SourceProof_d975e82a4c940db7d3cd3990
import Definitions.Def_SourceProof_f993fbc9ff9a1b70b006b96e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Continuity of the exponential vector of a step in the mark profile

For a Poisson random measure with intensity `ν`, a step `(a, b]` and a real frequency `u`, the
exponential vector `𝓔_u(f) = exp (i u J(f)) · exp (−(b − a) ∫ ψ_u(f) dν)` of the step at a
square-integrable mark profile `f` depends continuously on `f`: if `f_n → f` in `L²(ν)` then
`𝓔_u(f_n) → 𝓔_u(f)` in `L²(P; ℂ)`. The compensated integrals converge in `L²(P)` by the isometry,
so their characters converge in `L²(P)` because `x ↦ e^{iux}` is `|u|`-Lipschitz, and the
deterministic factors converge because the Lévy characteristic exponent is continuous along
`L²(ν)` convergence.

The same Lipschitz bound `|e^{iux} − e^{iuy}| ≤ |u| |x − y|` makes `e^{iu f_n} − 1 → e^{iu f} − 1`
in `L²(ν; ℂ)`, whence the two constants
`∫ ‖e^{iu f} − 1‖ ^ 2 dν` and `∫ (e^{iu f} − 1) ^ 2 dν` are continuous along `L²(ν)` convergence.

## Main statements

* `LevyStochCalc.Poisson.tendsto_eLpNorm_profileExpVector_sub` — `𝓔_u(f_n) → 𝓔_u(f)` in
  `L²(P; ℂ)`.
* `LevyStochCalc.Poisson.tendsto_eLpNorm_exp_I_mul_sub_one_sub` — `e^{iu f_n} − 1 → e^{iu f} − 1`
  in `L²(ν; ℂ)`.
* `LevyStochCalc.Poisson.tendsto_integral_norm_sq_exp_I_mul_sub_one` —
  `∫ ‖e^{iu f_n} − 1‖ ^ 2 dν → ∫ ‖e^{iu f} − 1‖ ^ 2 dν`.
* `LevyStochCalc.Poisson.tendsto_integral_sq_exp_I_mul_sub_one` —
  `∫ (e^{iu f_n} − 1) ^ 2 dν → ∫ (e^{iu f} − 1) ^ 2 dν`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]


theorem _root_.Prove2MeSourceProof.h_1300fa9daba157208895db31 (N : PoissonRandomMeasure P ν) {h : ℕ → E → ℝ}
    {f : E → ℝ} (hh : ∀ n, MemLp (h n) 2 ν) (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (u : ℝ)
    (hc : Tendsto (fun n => eLpNorm (fun e => h n e - f e) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun ω => profileExpVector N (h n) a b u ω
      - profileExpVector N f a b u ω) 2 P) atTop (𝓝 0) := by
  set X : (E → ℝ) → Ω → ℂ :=
    fun g ω => Complex.exp (Complex.I * ((u * LevyStochCalc.Poisson.compensatedProfile N g a b ω : ℝ) : ℂ)) with hX
  set K : (E → ℝ) → ℂ :=
    fun g => Complex.exp (-(((b - a : ℝ) : ℂ) * ∫ e, LevyStochCalc.Poisson.levyCharIntegrand u (g e) ∂ν)) with hK
  have hXm : ∀ g, MemLp (X g) 2 P := fun g =>
    LevyStochCalc.Probability.memLp_exp_I_mul u (LevyStochCalc.Poisson.measurable_compensatedProfile N g a b).aestronglyMeasurable
  have hXc : Tendsto (fun n => (hXm (h n)).toLp (X (h n))) atTop (𝓝 ((hXm f).toLp (X f))) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n => hXm (h n)) _ (hXm f)).2
      (_root_.Prove2MeSourceProof.h_d975e82a4c940db7d3cd3990 u
        (LevyStochCalc.Poisson.tendsto_compensatedProfile_of_tendsto N hh hf ha hab hc))
  have hKc : Tendsto (fun n => K (h n)) atTop (𝓝 (K f)) :=
    (Complex.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousAt.tendsto.comp
      (_root_.Prove2MeSourceProof.h_f993fbc9ff9a1b70b006b96e u hh hf hc)
  have hV : ∀ g, MemLp (LevyStochCalc.Poisson.profileExpVector N g a b u) 2 P := fun g =>
    LevyStochCalc.Poisson.memLp_profileExpVector N g a b u 2
  have hsmul : ∀ g, (hV g).toLp (LevyStochCalc.Poisson.profileExpVector N g a b u) = K g • (hXm g).toLp (X g) := by
    intro g
    refine Lp.ext ?_
    filter_upwards [(hV g).coeFn_toLp, Lp.coeFn_smul (K g) ((hXm g).toLp (X g)),
      (hXm g).coeFn_toLp] with ω h1 h2 h3
    rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul, LevyStochCalc.Poisson.profileExpVector, mul_comm]
  have hlim := hKc.smul hXc
  simp_rw [← hsmul] at hlim
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n => hV (h n)) _ (hV f)).1 hlim
end LevyStochCalc.Poisson


