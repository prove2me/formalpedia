-- Prove2me | Definitions.Def_LevyStochCalc_Driver_JointChaosComplex_F000
-- name    : LevyStochCalc_Driver_JointChaosComplex_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:21:41.692408+00:00
-- url     : https://prove2.me/theorems/c631aea1-65d3-4f72-b966-07e241681e62
-- title:
--   Source declarations: LevyStochCalc.Driver.JointChaosComplex
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.JointChaosComplex. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosBlock_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Complex-scaled total-degree blocks of a step of a Lévy driver

For a step `(a, b]` of a Lévy driver and a family of complex numbers indexed by the bidegrees and
constant in the sample point, the block of total degree `e` is the sum, over the bidegrees
`(n, m)` with `n + m = e`, of the joint chaos elements of that bidegree scaled by those numbers.
Such a block is square integrable over a mark set of finite intensity, its complex conjugate is
the block of the conjugate scalars, and blocks of different total degree are orthogonal; at equal
total degree the bilinear pairing and the second moment of the modulus are the bidegree sums of
the products of the scalars against `n! τ ^ n m! λ ^ m`, for `τ = b - a` and `λ = (b - a) ν(A)`.
Against a bounded complex coefficient strongly measurable for the joint filtration at `a`, the
node preceding the step, the pairing of two joint chaos elements, and hence of two blocks, is the
mean of the coefficient times the bidegree pairing. Through `(ℑz)² = (‖z‖² − ℜ z²)/2` that
factorisation turns into the second moment of the imaginary part of the product of such a
coefficient with a block, read off the second moments of the two factors.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosBlockC` — the block of total degree `e` of a step at
  complex scalars.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosBlockC_mul` — the pairing of two
  complex-scaled blocks of a step.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosBlockC_sq` — the bilinear second moment of
  a complex-scaled block.
* `LevyStochCalc.Driver.LevyDriver.integral_norm_sq_jointChaosBlockC` — the second moment of the
  modulus of a complex-scaled block.
* `LevyStochCalc.Driver.LevyDriver.integral_coeffC_mul_jointChaosBlockC_mul` — the pairing of two
  complex-scaled blocks against a bounded complex coefficient measurable at the node preceding
  the step.
* `LevyStochCalc.Driver.LevyDriver.integral_sq_im_coeffC_mul_jointChaosBlockC` — the second
  moment of the imaginary part of such a coefficient times a block.
-/

namespace LevyStochCalc.Driver.LevyDriver

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability LevyStochCalc.Poisson Finset
open scoped NNReal ENNReal

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- The block of total degree `e` of a step at complex scalars: the joint chaos elements of the
bidegrees summing to `e`, each scaled by a complex number. -/
noncomputable def jointChaosBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (a b : ℝ≥0)
    (A : Set E) (c : ℕ × ℕ → ℂ) (e : ℕ) (ω : Ω) : ℂ :=
  ∑ p ∈ antidiagonal e, c p * (D.jointChaosStep j p.1 p.2 a b A ω : ℂ)
/-- The conjugate of a complex-scaled block is the block of the conjugate scalars. -/
theorem conj_jointChaosBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (a b : ℝ≥0)
    (A : Set E) (c : ℕ × ℕ → ℂ) (e : ℕ) (ω : Ω) :
    (starRingEnd ℂ) (jointChaosBlockC D j a b A c e ω)
      = jointChaosBlockC D j a b A (fun p => (starRingEnd ℂ) (c p)) e ω := by
  simp [jointChaosBlockC, map_sum]
/-- A complex-scaled block of a step over a mark set of finite intensity lies in `L²`. -/
theorem memLp_two_jointChaosBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (c : ℕ × ℕ → ℂ) (e : ℕ) :
    MemLp (jointChaosBlockC D j a b A c e) 2 P := by
  have h := memLp_finsetSum (μ := P) (p := 2) (antidiagonal e)
    (f := fun p (ω : Ω) => c p * (D.jointChaosStep j p.1 p.2 a b A ω : ℂ))
    fun p _ => (((_root_.Prove2MeSourceProof.h_b395c3180260589aa3fb5846 D) j hab hA hAν p.1 p.2).ofReal).const_mul (c p)
  exact h
end LevyStochCalc.Driver.LevyDriver


