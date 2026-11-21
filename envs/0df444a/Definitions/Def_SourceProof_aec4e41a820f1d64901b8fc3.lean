-- Prove2me | Definitions.Def_SourceProof_aec4e41a820f1d64901b8fc3
-- name    : SourceProof_aec4e41a820f1d64901b8fc3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:09:12.329184+00:00
-- url     : https://prove2.me/theorems/744ae429-5d16-4464-8732-e54451e7dea2
-- title:
--   LevyStochCalc source module: SourceProof_aec4e41a820f1d64901b8fc3
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile_mul_compensatedProduct` comes from the `LevyStochCalc.Poisson.ProfileExpProduct` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairing_F001
import Definitions.Def_SourceProof_7dc1cbb71138213c4e7fd64a
import Definitions.Def_SourceProof_dbf1c2d8b35dab53e919bddc

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The pairing of the character of a compensated profile integral with a compensated product

For mark profiles `f, g` whose product is square integrable, the compensated product over the
step `(a, b]` is `Q(f, g) = J(f) J(g) − J(f g) − (b − a) ∫ f g dν`, with `J` the compensated
integral over the step. For a square-integrable profile `h`, a real frequency `u` and
`γ_u = e^{iuh} − 1`,

  `E[e^{iuJ(h)} Q(f, g)] = (b − a)² ∫ γ_u f dν ∫ γ_u g dν · E[e^{iuJ(h)}]`.

It is the second-order pairing `E[e^{iuJ(h)} J(f) J(g)]` less the first-order pairing with
`J(f g)` and the constant: the diagonal term `(b − a) ∫ e^{iuh} f g dν` of the former splits as
`(b − a) ∫ γ_u f g dν`, the pairing with `J(f g)`, plus `(b − a) ∫ f g dν`, the constant. The
profile `h` is only square integrable; `f g` is square integrable when one of the two profiles is
bounded.

## Main statements

* `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile_mul_compensatedProduct` — the
  pairing with the compensated product.
* `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile_mul_compensatedProduct_of_bound`
  — the same when one of the two profiles is bounded.
-/

open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]


theorem _root_.Prove2MeSourceProof.h_aec4e41a820f1d64901b8fc3
    (N : PoissonRandomMeasure P ν) {h f g : E → ℝ} (hh : MemLp h 2 ν) (hf : MemLp f 2 ν)
    (hg : MemLp g 2 ν) (hfg : MemLp (fun e => f e * g e) 2 ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N h a b ω : ℝ) : ℂ))
        * (compensatedProduct N f g a b ω : ℂ) ∂P
      = ((b - a : ℝ) : ℂ) ^ 2
          * (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (f e : ℂ) ∂ν)
          * (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (g e : ℂ) ∂ν)
        * ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N h a b ω : ℝ) : ℂ)) ∂P := by
  have hJm : ∀ g : E → ℝ, MemLp (LevyStochCalc.Poisson.compensatedProfile N g a b) 2 P :=
    fun g => LevyStochCalc.Poisson.memLp_compensatedProfile N g a b
  set c : ℂ := (((b - a) * ∫ e, f e * g e ∂ν : ℝ) : ℂ) with hc
  have hpt : ∀ ω, Complex.exp (Complex.I * ((u * LevyStochCalc.Poisson.compensatedProfile N h a b ω : ℝ) : ℂ))
      * (LevyStochCalc.Poisson.compensatedProduct N f g a b ω : ℂ)
      = (Complex.exp (Complex.I * ((u * LevyStochCalc.Poisson.compensatedProfile N h a b ω : ℝ) : ℂ))
          * (LevyStochCalc.Poisson.compensatedProfile N f a b ω : ℂ) * (LevyStochCalc.Poisson.compensatedProfile N g a b ω : ℂ)
        - Complex.exp (Complex.I * ((u * LevyStochCalc.Poisson.compensatedProfile N h a b ω : ℝ) : ℂ))
          * (LevyStochCalc.Poisson.compensatedProfile N (fun e => f e * g e) a b ω : ℂ))
        - c * Complex.exp (Complex.I * ((u * LevyStochCalc.Poisson.compensatedProfile N h a b ω : ℝ) : ℂ)) := by
    intro ω
    simp only [LevyStochCalc.Poisson.compensatedProduct, hc]
    push_cast
    ring
  have i1 : Integrable (fun ω =>
      Complex.exp (Complex.I * ((u * LevyStochCalc.Poisson.compensatedProfile N h a b ω : ℝ) : ℂ))
        * (LevyStochCalc.Poisson.compensatedProfile N f a b ω : ℂ) * (LevyStochCalc.Poisson.compensatedProfile N g a b ω : ℂ)) P := by
    simp_rw [mul_assoc]
    exact LevyStochCalc.Probability.integrable_exp_I_mul_mul u (hJm h).1
      ((hJm f).ofReal.integrable_mul (hJm g).ofReal)
  have i2 : Integrable (fun ω =>
      Complex.exp (Complex.I * ((u * LevyStochCalc.Poisson.compensatedProfile N h a b ω : ℝ) : ℂ))
        * (LevyStochCalc.Poisson.compensatedProfile N (fun e => f e * g e) a b ω : ℂ)) P :=
    LevyStochCalc.Probability.integrable_exp_I_mul_mul u (hJm h).1 ((hJm _).integrable one_le_two).ofReal
  have i3 : Integrable (fun ω =>
      Complex.exp (Complex.I * ((u * LevyStochCalc.Poisson.compensatedProfile N h a b ω : ℝ) : ℂ))) P :=
    (LevyStochCalc.Probability.memLp_exp_I_mul u (hJm h).1).integrable one_le_two
  have i12 : Integrable (fun ω =>
      Complex.exp (Complex.I * ((u * LevyStochCalc.Poisson.compensatedProfile N h a b ω : ℝ) : ℂ))
        * (LevyStochCalc.Poisson.compensatedProfile N f a b ω : ℂ) * (LevyStochCalc.Poisson.compensatedProfile N g a b ω : ℂ)
      - Complex.exp (Complex.I * ((u * LevyStochCalc.Poisson.compensatedProfile N h a b ω : ℝ) : ℂ))
        * (LevyStochCalc.Poisson.compensatedProfile N (fun e => f e * g e) a b ω : ℂ)) P := i1.sub i2
  have hγf := LevyStochCalc.Probability.memLp_mul_of_norm_le (LevyStochCalc.Probability.memLp_exp_I_mul_sub_one u hh).1
    (fun e => LevyStochCalc.Probability.norm_exp_I_mul_sub_one_le_two (u * h e)) hf.ofReal
  have j1 : Integrable (fun e => (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1)
      * (f e : ℂ) * (g e : ℂ)) ν := hγf.integrable_mul hg.ofReal
  have j2 : Integrable (fun e => (f e : ℂ) * (g e : ℂ)) ν := hf.ofReal.integrable_mul hg.ofReal
  have hsplit : ∫ e, Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) * (f e : ℂ) * (g e : ℂ) ∂ν
      = (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (f e : ℂ) * (g e : ℂ) ∂ν)
        + ∫ e, (f e : ℂ) * (g e : ℂ) ∂ν := by
    rw [← integral_add j1 j2]
    exact integral_congr_ae (Eventually.of_forall fun e => by simp only; ring)
  simp_rw [hpt]
  rw [integral_sub i12 (i3.const_mul c), integral_sub i1 i2, integral_const_mul,
    _root_.Prove2MeSourceProof.h_7dc1cbb71138213c4e7fd64a N hh hf hg ha hab u, hsplit,
    _root_.Prove2MeSourceProof.h_dbf1c2d8b35dab53e919bddc N hh hfg ha hab u]
  have hγfg : ∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1)
      * ((f e * g e : ℝ) : ℂ) ∂ν
      = ∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (f e : ℂ) * (g e : ℂ) ∂ν :=
    integral_congr_ae (Eventually.of_forall fun e => by simp only; push_cast; ring)
  have hfg' : ∫ e, (f e : ℂ) * (g e : ℂ) ∂ν = ((∫ e, f e * g e ∂ν : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun e => by simp only; push_cast; ring)
  rw [hγfg, hfg', hc]
  push_cast
  ring
end LevyStochCalc.Poisson


