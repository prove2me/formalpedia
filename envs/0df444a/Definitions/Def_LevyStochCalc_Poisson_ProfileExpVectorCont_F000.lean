-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ProfileExpVectorCont_F000
-- name    : LevyStochCalc_Poisson_ProfileExpVectorCont_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:03:05.679029+00:00
-- url     : https://prove2.me/theorems/7e2c1b16-d89d-4dfa-a2d5-3d59c8d0f457
-- title:
--   Source declarations: LevyStochCalc.Poisson.ProfileExpVectorCont
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ProfileExpVectorCont. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProductMoments_F001
import Definitions.Def_LevyStochCalc_Poisson_ProfileExpVector_F000
import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F000
import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F001
import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F002
import Definitions.Def_LevyStochCalc_Probability_L2Series_F001
import Definitions.Def_SourceProof_d7ae88512b435ecbc76009a2
import Definitions.Def_SourceProof_d975e82a4c940db7d3cd3990

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

omit [SigmaFinite ν] in
/-- If mark profiles `f_n` converge to `f` in `L²(ν)`, then `e^{iu f_n} − 1 → e^{iu f} − 1` in
`L²(ν; ℂ)`. -/
theorem tendsto_eLpNorm_exp_I_mul_sub_one_sub {h : ℕ → E → ℝ} {f : E → ℝ} (u : ℝ)
    (hc : Tendsto (fun n => eLpNorm (fun e => h n e - f e) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun e => (Complex.exp (Complex.I * ((u * h n e : ℝ) : ℂ)) - 1)
      - (Complex.exp (Complex.I * ((u * f e : ℝ) : ℂ)) - 1)) 2 ν) atTop (𝓝 0) := by
  refine (_root_.Prove2MeSourceProof.h_d975e82a4c940db7d3cd3990 u hc).congr fun n => ?_
  congr 1
  funext e
  ring
omit [SigmaFinite ν] in
/-- The constant `∫ ‖e^{iu f} − 1‖ ^ 2 dν` is continuous along `L²(ν)` convergence of the
square-integrable mark profile `f`. -/
theorem tendsto_integral_norm_sq_exp_I_mul_sub_one {h : ℕ → E → ℝ} {f : E → ℝ}
    (hh : ∀ n, MemLp (h n) 2 ν) (hf : MemLp f 2 ν) (u : ℝ)
    (hc : Tendsto (fun n => eLpNorm (fun e => h n e - f e) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ e, ‖Complex.exp (Complex.I * ((u * h n e : ℝ) : ℂ)) - 1‖ ^ 2 ∂ν) atTop
      (𝓝 (∫ e, ‖Complex.exp (Complex.I * ((u * f e : ℝ) : ℂ)) - 1‖ ^ 2 ∂ν)) := by
  have hm : ∀ n, MemLp (fun e => Complex.exp (Complex.I * ((u * h n e : ℝ) : ℂ)) - 1) 2 ν :=
    fun n => Probability.memLp_exp_I_mul_sub_one u (hh n)
  have hm' : MemLp (fun e => Complex.exp (Complex.I * ((u * f e : ℝ) : ℂ)) - 1) 2 ν :=
    Probability.memLp_exp_I_mul_sub_one u hf
  have hL := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hm _ hm').2
    (tendsto_eLpNorm_exp_I_mul_sub_one_sub u hc)
  have hn := hL.norm.pow 2
  rw [_root_.Prove2MeSourceProof.h_a136dbb94044eec9a3219314 _ hm'] at hn
  exact hn.congr fun n => _root_.Prove2MeSourceProof.h_a136dbb94044eec9a3219314 _ (hm n)
omit [SigmaFinite ν] in
/-- The constant `∫ (e^{iu f} − 1) ^ 2 dν` is continuous along `L²(ν)` convergence of the
square-integrable mark profile `f`. -/
theorem tendsto_integral_sq_exp_I_mul_sub_one {h : ℕ → E → ℝ} {f : E → ℝ}
    (hh : ∀ n, MemLp (h n) 2 ν) (hf : MemLp f 2 ν) (u : ℝ)
    (hc : Tendsto (fun n => eLpNorm (fun e => h n e - f e) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ e, (Complex.exp (Complex.I * ((u * h n e : ℝ) : ℂ)) - 1) ^ 2 ∂ν) atTop
      (𝓝 (∫ e, (Complex.exp (Complex.I * ((u * f e : ℝ) : ℂ)) - 1) ^ 2 ∂ν)) := by
  have hm : ∀ n, MemLp (fun e => Complex.exp (Complex.I * ((u * h n e : ℝ) : ℂ)) - 1) 2 ν :=
    fun n => Probability.memLp_exp_I_mul_sub_one u (hh n)
  have hm' : MemLp (fun e => Complex.exp (Complex.I * ((u * f e : ℝ) : ℂ)) - 1) 2 ν :=
    Probability.memLp_exp_I_mul_sub_one u hf
  have h2 := _root_.Prove2MeSourceProof.h_d7ae88512b435ecbc76009a2 hm hm hm' hm'
    (tendsto_eLpNorm_exp_I_mul_sub_one_sub u hc) (tendsto_eLpNorm_exp_I_mul_sub_one_sub u hc)
  simpa only [sq] using h2
end LevyStochCalc.Poisson


