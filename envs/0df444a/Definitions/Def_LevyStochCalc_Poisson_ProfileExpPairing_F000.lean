-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairing_F000
-- name    : LevyStochCalc_Poisson_ProfileExpPairing_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:02:29.88239+00:00
-- url     : https://prove2.me/theorems/7557dc76-b0bc-4168-ae10-9761df2335ff
-- title:
--   Source declarations: LevyStochCalc.Poisson.ProfileExpPairing
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ProfileExpPairing. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedProductMoments_F001
import Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairingSimple_F000
import Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairingSimple_F001
import Definitions.Def_SourceProof_d975e82a4c940db7d3cd3990

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

/-- The compensated integrals of simple profiles converging in `L²(ν)` converge in `L²(P)`. -/
private theorem tendsto_compensatedProfile_simple (N : PoissonRandomMeasure P ν)
    {G : ℕ → SimpleProfile E ν} {f : E → ℝ} (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hG : Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun ω => compensatedProfile N (G n).toFun a b ω
      - compensatedProfile N f a b ω) 2 P) atTop (𝓝 0) := by
  simp_rw [eLpNorm_compensatedProfile_sub N (G _).memLp_toFun hf ha hab]
  have h := ENNReal.Tendsto.const_mul hG (Or.inr ENNReal.ofReal_ne_top)
    (a := ENNReal.ofReal (Real.sqrt (b - a)))
  rwa [mul_zero] at h
omit [SigmaFinite ν] in
/-- The mark functions `e^{iuG_n} − 1` of simple profiles `G_n` converging in `L²(ν)` converge
in `L²(ν)`. -/
private theorem tendsto_eLpNorm_exp_sub_one {G : ℕ → SimpleProfile E ν} {h : E → ℝ} (u : ℝ)
    (hG : Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - h e) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun e => (Complex.exp (Complex.I * ((u * (G n).toFun e : ℝ) : ℂ))
      - 1) - (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1)) 2 ν) atTop (𝓝 0) := by
  simp_rw [sub_sub_sub_cancel_right]
  exact _root_.Prove2MeSourceProof.h_d975e82a4c940db7d3cd3990 u hG
/-! ### The pairings at square-integrable profiles -/

end LevyStochCalc.Poisson


