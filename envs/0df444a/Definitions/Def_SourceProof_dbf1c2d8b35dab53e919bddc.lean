-- Prove2me | Definitions.Def_SourceProof_dbf1c2d8b35dab53e919bddc
-- name    : SourceProof_dbf1c2d8b35dab53e919bddc
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:03:53.45763+00:00
-- url     : https://prove2.me/theorems/2f080c7c-a4a1-4dcf-9153-61ae7d21cb30
-- title:
--   LevyStochCalc source module: SourceProof_dbf1c2d8b35dab53e919bddc
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile_mul` comes from the `LevyStochCalc.Poisson.ProfileExpPairing` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairing_F000
import Definitions.Def_SourceProof_16c21c9e1fb7e2d07f448605
import Definitions.Def_SourceProof_d7ae88512b435ecbc76009a2

open private tendsto_compensatedProfile_simple tendsto_eLpNorm_exp_sub_one from Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairing_F000
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


theorem _root_.Prove2MeSourceProof.h_dbf1c2d8b35dab53e919bddc (N : PoissonRandomMeasure P ν) {h f : E → ℝ}
    (hh : MemLp h 2 ν) (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N h a b ω : ℝ) : ℂ))
        * (compensatedProfile N f a b ω : ℂ) ∂P
      = ((b - a : ℝ) : ℂ)
          * (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (f e : ℂ) ∂ν)
        * ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N h a b ω : ℝ) : ℂ)) ∂P := by
  obtain ⟨G, hG⟩ := _root_.Prove2MeSourceProof.h_abfa6819f153687cc685dc62 hh
  obtain ⟨F, hF⟩ := _root_.Prove2MeSourceProof.h_abfa6819f153687cc685dc62 hf
  have hJm : ∀ g : E → ℝ, MemLp (LevyStochCalc.Poisson.compensatedProfile N g a b) 2 P :=
    fun g => LevyStochCalc.Poisson.memLp_compensatedProfile N g a b
  have he := _root_.Prove2MeSourceProof.h_d975e82a4c940db7d3cd3990 u (tendsto_compensatedProfile_simple N hh ha hab hG)
  have hL := _root_.Prove2MeSourceProof.h_d7ae88512b435ecbc76009a2
    (fun n => LevyStochCalc.Probability.memLp_exp_I_mul u (hJm (G n).toFun).1)
    (fun n => (hJm (F n).toFun).ofReal) (LevyStochCalc.Probability.memLp_exp_I_mul u (hJm h).1) (hJm f).ofReal he
    (LevyStochCalc.Probability.tendsto_eLpNorm_ofReal_sub (tendsto_compensatedProfile_simple N hf ha hab hF))
  have hγ := _root_.Prove2MeSourceProof.h_d7ae88512b435ecbc76009a2
    (fun n => LevyStochCalc.Probability.memLp_exp_I_mul_sub_one u (G n).memLp_toFun)
    (fun n => (F n).memLp_toFun.ofReal) (LevyStochCalc.Probability.memLp_exp_I_mul_sub_one u hh) hf.ofReal
    (tendsto_eLpNorm_exp_sub_one u hG) (LevyStochCalc.Probability.tendsto_eLpNorm_ofReal_sub hF)
  have hχ := _root_.Prove2MeSourceProof.h_d7ae88512b435ecbc76009a2 (G := fun _ _ => (1 : ℂ))
    (fun n => LevyStochCalc.Probability.memLp_exp_I_mul u (hJm (G n).toFun).1) (fun _ => memLp_const 1)
    (LevyStochCalc.Probability.memLp_exp_I_mul u (hJm h).1)
    (memLp_const 1) he (by simp)
  simp only [mul_one] at hχ
  exact tendsto_nhds_unique (hL.congr fun n =>
    _root_.Prove2MeSourceProof.h_16c21c9e1fb7e2d07f448605 N (G n) (F n) ha hab u)
    ((tendsto_const_nhds.mul hγ).mul hχ)
end LevyStochCalc.Poisson


