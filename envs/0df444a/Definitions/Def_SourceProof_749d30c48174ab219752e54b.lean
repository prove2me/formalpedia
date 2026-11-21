-- Prove2me | Definitions.Def_SourceProof_749d30c48174ab219752e54b
-- name    : SourceProof_749d30c48174ab219752e54b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T12:44:55.459171+00:00
-- url     : https://prove2.me/theorems/8eb2a384-f08b-45da-8ad7-486eb2bc4467
-- title:
--   LevyStochCalc source module: SourceProof_749d30c48174ab219752e54b
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.integral_jointChaosBlockC_mul` comes from the `LevyStochCalc.Driver.JointChaosComplex` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointChaosComplex_F000

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


theorem _root_.Prove2MeSourceProof.h_749d30c48174ab219752e54b (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (c c' : ℕ × ℕ → ℂ)
    (e e' : ℕ) :
    ∫ ω, jointChaosBlockC D j a b A c e ω * jointChaosBlockC D j a b A c' e' ω ∂P
      = if e = e' then ∑ p ∈ antidiagonal e, c p * c' p
          * ((((p.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ p.1)
              * ((p.2.factorial : ℝ) * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ p.2) : ℝ) : ℂ)
        else 0 := by
  classical
  set F : ℕ × ℕ → ℕ × ℕ → Ω → ℂ := fun p q ω => (c p * c' q)
    * ((D.jointChaosStep j p.1 p.2 a b A ω
        * D.jointChaosStep j q.1 q.2 a b A ω : ℝ) : ℂ) with hF
  have hJJ : ∀ p q : ℕ × ℕ, Integrable (fun ω => D.jointChaosStep j p.1 p.2 a b A ω
      * D.jointChaosStep j q.1 q.2 a b A ω) P := fun p q =>
    ((_root_.Prove2MeSourceProof.h_b395c3180260589aa3fb5846 D) j hab hA hAν p.1 p.2).integrable_mul
      ((_root_.Prove2MeSourceProof.h_b395c3180260589aa3fb5846 D) j hab hA hAν q.1 q.2)
  have hterm : ∀ p q : ℕ × ℕ, Integrable (F p q) P :=
    fun p q => ((hJJ p q).ofReal).const_mul _
  have hexp : (fun ω => LevyStochCalc.Driver.LevyDriver.jointChaosBlockC D j a b A c e ω * LevyStochCalc.Driver.LevyDriver.jointChaosBlockC D j a b A c' e' ω)
      = fun ω => ∑ p ∈ antidiagonal e, ∑ q ∈ antidiagonal e', F p q ω := by
    funext ω
    simp only [LevyStochCalc.Driver.LevyDriver.jointChaosBlockC, Finset.sum_mul_sum, hF]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    push_cast
    ring
  have hinner : ∀ p q : ℕ × ℕ, ∫ ω, F p q ω ∂P
      = (c p * c' q) * (((if p.1 = q.1 then (p.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ p.1
              else 0)
            * (if p.2 = q.2 then (p.2.factorial : ℝ)
                * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ p.2 else 0) : ℝ) : ℂ) := by
    intro p q
    rw [hF, integral_const_mul, integral_complex_ofReal,
      (_root_.Prove2MeSourceProof.h_38d504a1087b78cbf737f4a0 D) j hab hA hAν p.1 p.2 q.1 q.2]
  rw [hexp, integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hterm p q]
  have hstep : ∀ p ∈ antidiagonal e, (∫ ω, ∑ q ∈ antidiagonal e', F p q ω ∂P)
      = ∑ q ∈ antidiagonal e', ∫ ω, F p q ω ∂P :=
    fun p _ => integral_finsetSum (antidiagonal e') (f := F p) fun q _ => hterm p q
  rw [Finset.sum_congr rfl hstep]
  simp only [hinner]
  have hkill : ∀ p q : ℕ × ℕ, p ≠ q →
      (((if p.1 = q.1 then (p.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ p.1 else 0)
        * (if p.2 = q.2 then (p.2.factorial : ℝ)
            * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ p.2 else 0) : ℝ) : ℂ) = 0 := by
    intro p q hpq
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h => hpq (Prod.ext_iff.2 ⟨h1, h⟩)
      simp [h2]
    · simp [h1]
  by_cases hee : e = e'
  · subst hee
    rw [if_pos rfl]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_eq_single_of_mem p hp fun q _ hqp => by
      rw [hkill p q (Ne.symm hqp), mul_zero]]
    simp
  · rw [if_neg hee]
    refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
    have hpq : p ≠ q := by
      have hpe : p.1 + p.2 = e := by simpa using hp
      have hqe : q.1 + q.2 = e' := by simpa using hq
      intro h
      exact hee (by rw [← hpe, ← hqe, h])
    rw [hkill p q hpq, mul_zero]
end LevyStochCalc.Driver.LevyDriver


