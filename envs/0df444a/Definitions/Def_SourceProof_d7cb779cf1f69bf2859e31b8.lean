-- Prove2me | Definitions.Def_SourceProof_d7cb779cf1f69bf2859e31b8
-- name    : SourceProof_d7cb779cf1f69bf2859e31b8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:18:30.990179+00:00
-- url     : https://prove2.me/theorems/53e20522-61ef-4e3d-a9c0-0122b6ac4d87
-- title:
--   LevyStochCalc source module: SourceProof_d7cb779cf1f69bf2859e31b8
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointChaosStep_mul` comes from the `LevyStochCalc.Driver.JointChaosBlock` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosStep_F001
import Definitions.Def_SourceProof_a8df8d1e682dc608b5be8245
import Definitions.Def_SourceProof_b395c3180260589aa3fb5846

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Total-degree blocks of a step of a Lévy driver

For a step `(a, b]` with `a < b` and a coefficient `c` bounded and strongly measurable for the
joint filtration at `a`, the node preceding the step, the pairing `E[c J_(n, m) J_(n', m')]` of
two joint chaos elements of the step weighted by `c` is the mean `E[c]` of the coefficient times
the bidegree pairing `δ_(n n') δ_(m m') n! τ ^ n m! λ ^ m`, for `τ = b - a` and
`λ = (b - a) ν(A)`; elements of different bidegree therefore stay orthogonal against such a
coefficient. The block of total degree `e` is the sum over the bidegrees `(n, m)` with `n + m = e`
of the elements of that bidegree weighted by such coefficients, and two blocks of different total
degree are orthogonal in `L²(P)`.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosBlock` — the block of total degree `e` of a step.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointChaosStep_mul` — the pairing of two
  elements of a step weighted by a bounded coefficient measurable at the node preceding the step
  is the mean of the coefficient times the bidegree pairing.
* `LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointChaosStep_mul_eq_zero` — orthogonality
  across bidegrees against such a coefficient.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosBlock_mul_eq_zero` — orthogonality of two
  blocks of different total degree.
-/

namespace LevyStochCalc.Driver.LevyDriver

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability LevyStochCalc.Poisson
open scoped NNReal ENNReal

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}


theorem _root_.Prove2MeSourceProof.h_d7cb779cf1f69bf2859e31b8 (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a < b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {c : Ω → ℝ} (hc : StronglyMeasurable[D.filtration (a : ℝ)] c) {Cb : ℝ}
    (hcb : ∀ ω, ‖c ω‖ ≤ Cb) (n m n' m' : ℕ) :
    ∫ ω, c ω * (D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω) ∂P
      = (∫ ω, c ω ∂P)
        * ((if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
          * (if m = m' then (m.factorial : ℝ)
              * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ m else 0)) := by
  set L : ℝ := (if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
        * (if m = m' then (m.factorial : ℝ)
            * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ m else 0) with hL
  have hm : (D.filtration (a : ℝ) : MeasurableSpace Ω) ≤ ‹MeasurableSpace Ω› := D.filtration.le _
  have hcm : StronglyMeasurable c := hc.mono hm
  have hJJ : Integrable (fun ω => D.jointChaosStep j n m a b A ω
      * D.jointChaosStep j n' m' a b A ω) P :=
    ((_root_.Prove2MeSourceProof.h_b395c3180260589aa3fb5846 D) j hab.le hA hAν n m).integrable_mul
      ((_root_.Prove2MeSourceProof.h_b395c3180260589aa3fb5846 D) j hab.le hA hAν n' m')
  have hprod : Integrable (fun ω => c ω * (D.jointChaosStep j n m a b A ω
      * D.jointChaosStep j n' m' a b A ω)) P :=
    hJJ.bdd_mul hcm.aestronglyMeasurable (Filter.Eventually.of_forall hcb)
  have hmulEq : (fun ω => c ω * (D.jointChaosStep j n m a b A ω
      * D.jointChaosStep j n' m' a b A ω))
      = c * fun ω => D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω := rfl
  have hstep := condExp_mul_of_stronglyMeasurable_left (μ := P)
    (m := (D.filtration (a : ℝ) : MeasurableSpace Ω)) hc (hmulEq ▸ hprod) hJJ
  have hcond := (_root_.Prove2MeSourceProof.h_a8df8d1e682dc608b5be8245 D) j hab hA hAν n m n' m'
  rw [hmulEq, ← integral_condExp hm (f := c * fun ω => D.jointChaosStep j n m a b A ω
    * D.jointChaosStep j n' m' a b A ω)]
  have : P[c * fun ω => D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω
      | (D.filtration (a : ℝ) : MeasurableSpace Ω)] =ᵐ[P] fun ω => c ω * L := by
    filter_upwards [hstep, hcond] with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
  rw [integral_congr_ae this, integral_mul_const]
end LevyStochCalc.Driver.LevyDriver


