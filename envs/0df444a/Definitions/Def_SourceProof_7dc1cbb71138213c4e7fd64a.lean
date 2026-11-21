-- Prove2me | Definitions.Def_SourceProof_7dc1cbb71138213c4e7fd64a
-- name    : SourceProof_7dc1cbb71138213c4e7fd64a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:07:16.607459+00:00
-- url     : https://prove2.me/theorems/f067db65-a6fc-4600-9cf7-21344b46173e
-- title:
--   LevyStochCalc source module: SourceProof_7dc1cbb71138213c4e7fd64a
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile_mul_mul` comes from the `LevyStochCalc.Poisson.ProfileExpPairing` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairing_F001

open private pairing_two from Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairing_F001
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The character of a compensated profile integral against first- and second-order elements

For a Poisson random measure with intensity `ν`, the compensated integral `J` over the step
`(a, b]`, square-integrable mark profiles `h, f, g`, a real frequency `u` and the mark function
`γ_u = e^{iuh} − 1`,

  `E[e^{iuJ(h)} J(f)] = (b − a) ∫ γ_u f dν · E[e^{iuJ(h)}]`,
  `E[e^{iuJ(h)} J(f) J(g)]`
  `  = ((b − a)² ∫ γ_u f dν ∫ γ_u g dν + (b − a) ∫ e^{iuh} f g dν) · E[e^{iuJ(h)}]`.

No bound is placed on the profiles.

At simple profiles these are the identities of `Poisson/ProfileExpPairingSimple.lean`. At
general profiles both sides are limits along simple approximants: the characters
`e^{iuJ(h_n)}`, the compensated integrals `J(f_n)` and the mark functions `e^{iuh_n} − 1`
converge in `L²`, and the complex pairing is continuous along `L²` convergence. For the
second-order identity `h` is approximated first, with `f` and `g` simple so that `J(f) J(g)` is
a fixed square-integrable variable, and `f`, `g` afterwards, with `h` fixed.

## Main statements

* `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile_mul` — the first-order pairing.
* `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile_mul_mul` — the second-order
  pairing.
-/

open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Probability
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### `L²` limits -/

/-! ### The pairings at square-integrable profiles -/


theorem _root_.Prove2MeSourceProof.h_7dc1cbb71138213c4e7fd64a (N : PoissonRandomMeasure P ν)
    {h f g : E → ℝ} (hh : MemLp h 2 ν) (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N h a b ω : ℝ) : ℂ))
        * (compensatedProfile N f a b ω : ℂ) * (compensatedProfile N g a b ω : ℂ) ∂P
      = (((b - a : ℝ) : ℂ) ^ 2
          * (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (f e : ℂ) ∂ν)
          * (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (g e : ℂ) ∂ν)
          + ((b - a : ℝ) : ℂ)
            * ∫ e, Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) * (f e : ℂ) * (g e : ℂ) ∂ν)
        * ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N h a b ω : ℝ) : ℂ)) ∂P := by
  have hγf := LevyStochCalc.Probability.memLp_mul_of_norm_le (LevyStochCalc.Probability.memLp_exp_I_mul_sub_one u hh).1
    (fun e => LevyStochCalc.Probability.norm_exp_I_mul_sub_one_le_two (u * h e)) hf.ofReal
  have hsplit : ∫ e, Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) * (f e : ℂ) * (g e : ℂ) ∂ν
      = (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (f e : ℂ) * (g e : ℂ) ∂ν)
        + ∫ e, (f e : ℂ) * (g e : ℂ) ∂ν := by
    have j1 : Integrable (fun e => (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1)
        * (f e : ℂ) * (g e : ℂ)) ν := hγf.integrable_mul hg.ofReal
    have j2 : Integrable (fun e => (f e : ℂ) * (g e : ℂ)) ν := hf.ofReal.integrable_mul hg.ofReal
    rw [← integral_add j1 j2]
    exact integral_congr_ae (Eventually.of_forall fun e => by simp only; ring)
  rw [hsplit]
  exact pairing_two N hh hf hg ha hab u
end LevyStochCalc.Poisson


