-- Prove2me | Definitions.Def_ApproxDegCompV1_CommutatorBounds
-- name    : ApproxDegCompV1_CommutatorBounds
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-13T04:11:16.765393+00:00
-- url     : https://prove2.me/theorems/959b9cad-10d7-482c-992a-5c3b0b13586f
-- title:
--   Approximate-degree composition: Spectral commutator and matrix phase bounds
-- statement:
--   This module formalizes spectral commutator and matrix phase bounds for the Lean proof of the approximate-degree composition lower bound.
-- source:
--   https://prove2.me/theorems/f8385c32-068c-45a1-99ed-f7cf0a99f266

import Definitions.Def_ApproxDegCompV1_PolynomialBandwidth
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.Permutation
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

-- BernsteinSample.lean
section
/-!
# A scalar Bernstein bound with an absolute constant

The analytic inputs are Mathlib's proved maximum modulus principle and Cauchy
derivative estimate. No matrix norm is introduced here.
-/

namespace ApproxDegree.BernsteinSample

open Metric Set Polynomial
open scoped Polynomial

noncomputable section

/-- A unit-circle bound for a polynomial holds throughout the closed unit disk. -/
theorem norm_eval_le_of_norm_le_one (p : ℂ[X]) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖p.eval z‖ ≤ M := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := ball (0 : ℂ) 1) isBounded_ball p.differentiable.diffContOnCl
  · intro w hw
    apply hM
    simpa only [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0),
      mem_sphere_iff_norm, sub_zero] using hw
  · simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0),
      mem_closedBall, dist_zero_right] using hz

/-- Polynomial reflection is an exact inversion identity away from zero. -/
theorem eval_reflect_inv_mul_pow (p : ℂ[X]) (N : ℕ) (hdegree : p.natDegree ≤ N)
    (z : ℂ) (hz : z ≠ 0) :
    (p.reflect N).eval z⁻¹ * z ^ N = p.eval z := by
  let : Invertible z := invertibleOfNonzero hz
  simpa only [invOf_eq_inv, eval₂_id] using
    Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) z N p hdegree

/-- Reflection preserves a unit-circle bound. -/
theorem norm_reflect_eval_le_on_circle (p : ℂ[X]) (N : ℕ)
    (hdegree : p.natDegree ≤ N) {M : ℝ}
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M) :
    ∀ z : ℂ, ‖z‖ = 1 → ‖(p.reflect N).eval z‖ ≤ M := by
  intro z hz
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have h := congrArg norm (eval_reflect_inv_mul_pow p N hdegree z⁻¹ (inv_ne_zero hz0))
  simp only [inv_inv, norm_mul, norm_pow, norm_inv, hz, inv_one, one_pow, mul_one] at h
  rw [h]
  exact hM z⁻¹ (by simp [hz])

/-- Outside the disk, a polynomial grows at most as the degree power of radius. -/
theorem norm_eval_le_radius_pow (p : ℂ[X]) (N : ℕ) (hdegree : p.natDegree ≤ N)
    {M r : ℝ} (hM0 : 0 ≤ M) (hr : 1 ≤ r)
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ r) : ‖p.eval z‖ ≤ r ^ N * M := by
  by_cases hz1 : ‖z‖ ≤ 1
  · calc
      ‖p.eval z‖ ≤ M := norm_eval_le_of_norm_le_one p hM hz1
      _ ≤ r ^ N * M := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hr) hM0
  · have hzgt : 1 < ‖z‖ := lt_of_not_ge hz1
    have hz0 : z ≠ 0 := by intro h; norm_num [h] at hzgt
    have hzinv : ‖z⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hzgt.le
    have hrev := norm_eval_le_of_norm_le_one (p.reflect N)
      (norm_reflect_eval_le_on_circle p N hdegree hM) hzinv
    rw [← eval_reflect_inv_mul_pow p N hdegree z hz0, norm_mul, norm_pow]
    calc
      ‖(p.reflect N).eval z⁻¹‖ * ‖z‖ ^ N ≤ M * r ^ N :=
        mul_le_mul hrev (pow_le_pow_left₀ (norm_nonneg z) hz N)
          (pow_nonneg (norm_nonneg z) N) hM0
      _ = r ^ N * M := mul_comm _ _

/-- The standard exponential estimate for the Cauchy radius `1/N`. -/
theorem one_add_inv_pow_le_exp (N : ℕ) (hN : 0 < N) :
    (1 + (N : ℝ)⁻¹) ^ N ≤ Real.exp 1 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  calc
    (1 + (N : ℝ)⁻¹) ^ N ≤ (Real.exp (N : ℝ)⁻¹) ^ N := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using Real.add_one_le_exp (N : ℝ)⁻¹
    _ = Real.exp ((N : ℝ) * (N : ℝ)⁻¹) := (Real.exp_nat_mul _ N).symm
    _ = Real.exp 1 := by rw [mul_inv_cancel₀ hN0]

/-- Cauchy's estimate plus reflected-polynomial growth gives a linear-degree
derivative bound on the unit circle. -/
theorem norm_derivative_eval_le (p : ℂ[X]) (N : ℕ) (hN : 0 < N)
    (hdegree : p.natDegree ≤ N) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖p.derivative.eval z‖ ≤ Real.exp 1 * N * M := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hbound : ∀ w ∈ sphere z (N : ℝ)⁻¹, ‖p.eval w‖ ≤ Real.exp 1 * M := by
    intro w hw
    have hdist : ‖w - z‖ = (N : ℝ)⁻¹ := mem_sphere_iff_norm.mp hw
    have hwbound : ‖w‖ ≤ 1 + (N : ℝ)⁻¹ := by
      calc
        ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ = 1 + (N : ℝ)⁻¹ := by rw [hdist, hz, add_comm]
    calc
      ‖p.eval w‖ ≤ (1 + (N : ℝ)⁻¹) ^ N * M :=
        norm_eval_le_radius_pow p N hdegree hM0
          (le_add_of_nonneg_right (inv_nonneg.mpr hNpos.le)) hM hwbound
      _ ≤ Real.exp 1 * M := mul_le_mul_of_nonneg_right (one_add_inv_pow_le_exp N hN) hM0
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (inv_pos.mpr hNpos) p.differentiable.diffContOnCl hbound
  rw [(p.hasDerivAt z).deriv] at h
  convert h using 1
  field_simp

/-- The explicit absolute constant in the non-sharp trigonometric estimate. -/
def bernsteinConstant : ℝ := 2 * Real.exp 1 + 1

theorem bernsteinConstant_pos : 0 < bernsteinConstant := by
  unfold bernsteinConstant
  positivity

theorem bernsteinConstant_lt_seven : bernsteinConstant < 7 := by
  unfold bernsteinConstant
  linarith [Real.exp_one_lt_three]

/-- Differentiation of a trigonometric polynomial with frequency shift `-D`,
represented by an ordinary polynomial of degree at most `2D`. -/
def angularStep (D : ℕ) (p : ℂ[X]) : ℂ[X] :=
  C Complex.I * (X * p.derivative - C (D : ℂ) * p)

/-- The angular derivative does not increase the ordinary polynomial degree. -/
theorem natDegree_angularStep_le (D : ℕ) (p : ℂ[X]) :
    (angularStep D p).natDegree ≤ p.natDegree := by
  have hx : (X * p.derivative).natDegree ≤ p.natDegree := by
    by_cases hd : p.natDegree = 0
    · simp [Polynomial.derivative_of_natDegree_zero hd]
    · have hm := Polynomial.natDegree_mul_le (p := (X : ℂ[X])) (q := p.derivative)
      have hder := Polynomial.natDegree_derivative_le p
      simp only [natDegree_X] at hm
      omega
  calc
    (angularStep D p).natDegree ≤ (X * p.derivative - C (D : ℂ) * p).natDegree :=
      natDegree_C_mul_le _ _
    _ ≤ max (X * p.derivative).natDegree (C (D : ℂ) * p).natDegree := natDegree_sub_le _ _
    _ ≤ p.natDegree := max_le hx (natDegree_C_mul_le _ _)

/-- Linear-degree unit-circle estimate for the angular derivative polynomial. -/
theorem norm_angularStep_eval_le (D : ℕ) (hD : 0 < D) (p : ℂ[X])
    (hdegree : p.natDegree ≤ 2 * D) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖(angularStep D p).eval z‖ ≤ bernsteinConstant * D * M := by
  have hp := norm_derivative_eval_le p (2 * D) (by omega) hdegree hM0 hM hz
  calc
    ‖(angularStep D p).eval z‖ = ‖z * p.derivative.eval z - (D : ℂ) * p.eval z‖ := by
      simp [angularStep]
    _ ≤ ‖z * p.derivative.eval z‖ + ‖(D : ℂ) * p.eval z‖ := norm_sub_le _ _
    _ = ‖p.derivative.eval z‖ + (D : ℝ) * ‖p.eval z‖ := by simp [hz]
    _ ≤ Real.exp 1 * (2 * D) * M + (D : ℝ) * M := by
      exact add_le_add (by exact_mod_cast hp) (mul_le_mul_of_nonneg_left (hM z hz) (by positivity))
    _ = bernsteinConstant * D * M := by unfold bernsteinConstant; ring

/-- Entire extension of the shifted trigonometric polynomial.
On the real line, degree at most `2D` means frequencies lie between `-D` and `D`. -/
def complexTrigEval (D : ℕ) (p : ℂ[X]) (t : ℂ) : ℂ :=
  Complex.exp (-(D : ℂ) * (t * Complex.I)) * p.eval (Complex.exp (t * Complex.I))

/-- The real-variable trigonometric polynomial, with complex scalar values. -/
def trigEval (D : ℕ) (p : ℂ[X]) (t : ℝ) : ℂ := complexTrigEval D p t

theorem hasDerivAt_complexTrigEval (D : ℕ) (p : ℂ[X]) (t : ℂ) :
    HasDerivAt (complexTrigEval D p) (complexTrigEval D (angularStep D p) t) t := by
  have he : HasDerivAt (fun t : ℂ => Complex.exp (t * Complex.I))
      (Complex.exp (t * Complex.I) * Complex.I) t := by
    simpa only [id_eq, one_mul] using ((hasDerivAt_id t).mul_const Complex.I).cexp
  have hs : HasDerivAt (fun t : ℂ => Complex.exp (-(D : ℂ) * (t * Complex.I)))
      (Complex.exp (-(D : ℂ) * (t * Complex.I)) * (-(D : ℂ) * Complex.I)) t := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id t).mul_const Complex.I).const_mul (-(D : ℂ))).cexp
  apply (hs.mul ((p.hasDerivAt _).comp t he)).congr_deriv
  simp only [complexTrigEval, angularStep, eval_mul, eval_sub, eval_C, eval_X,
    Function.comp_apply]
  ring

theorem deriv_trigEval (D : ℕ) (p : ℂ[X]) :
    deriv (trigEval D p) = trigEval D (angularStep D p) := by
  funext t
  exact (hasDerivAt_complexTrigEval D p (t : ℂ)).comp_ofReal.deriv

/-- The phase prefactor has unit norm on real inputs. -/
theorem norm_trigEval (D : ℕ) (p : ℂ[X]) (t : ℝ) :
    ‖trigEval D p t‖ = ‖p.eval (Complex.exp ((t : ℂ) * Complex.I))‖ := by
  simp [trigEval, complexTrigEval, Complex.norm_exp]

/-- Real-line bounds and unit-circle polynomial bounds are equivalent. -/
theorem trigEval_bound_iff (D : ℕ) (p : ℂ[X]) (M : ℝ) :
    (∀ t : ℝ, ‖trigEval D p t‖ ≤ M) ↔
      (∀ z : ℂ, ‖z‖ = 1 → ‖p.eval z‖ ≤ M) := by
  constructor
  · intro h z hz
    obtain ⟨t, rfl⟩ := (Complex.norm_eq_one_iff z).mp hz
    simpa only [norm_trigEval] using h t
  · intro h t
    rw [norm_trigEval]
    exact h _ (Complex.norm_exp_ofReal_mul_I t)

/-- A scalar trigonometric Bernstein inequality with explicit constant `2e+1`.
The only size input is a real-line bound for the original trigonometric polynomial. -/
theorem norm_deriv_trigEval_le (D : ℕ) (hD : 0 < D) (p : ℂ[X])
    (hdegree : p.natDegree ≤ 2 * D) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t : ℝ, ‖trigEval D p t‖ ≤ M) (t : ℝ) :
    ‖deriv (trigEval D p) t‖ ≤ bernsteinConstant * D * M := by
  rw [deriv_trigEval, norm_trigEval]
  exact norm_angularStep_eval_le D hD p hdegree hM0
    ((trigEval_bound_iff D p M).mp hM) (Complex.norm_exp_ofReal_mul_I t)

/-- Every iterated angular derivative still has degree at most the starting degree. -/
theorem natDegree_iterate_angularStep_le (D : ℕ) (p : ℂ[X]) (k : ℕ) :
    ((angularStep D)^[k] p).natDegree ≤ p.natDegree := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (natDegree_angularStep_le D _).trans ih

/-- The polynomial angular iteration equals actual iterated real differentiation. -/
theorem iteratedDeriv_trigEval (D : ℕ) (p : ℂ[X]) (k : ℕ) :
    iteratedDeriv k (trigEval D p) = trigEval D ((angularStep D)^[k] p) := by
  induction k with
  | zero => simp
  | succ k ih => rw [iteratedDeriv_succ, ih, deriv_trigEval, Function.iterate_succ_apply']

/-- The complete iterated linear-degree scalar bound. -/
theorem norm_iteratedDeriv_trigEval_le (D : ℕ) (hD : 0 < D) (p : ℂ[X])
    (hdegree : p.natDegree ≤ 2 * D) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t : ℝ, ‖trigEval D p t‖ ≤ M) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (trigEval D p) t‖ ≤ (bernsteinConstant * D) ^ k * M := by
  induction k generalizing t with
  | zero => simpa using hM t
  | succ k ih =>
    have hpoly : ((angularStep D)^[k] p).natDegree ≤ 2 * D :=
      (natDegree_iterate_angularStep_le D p k).trans hdegree
    have hsize : ∀ s : ℝ, ‖trigEval D ((angularStep D)^[k] p) s‖ ≤
        (bernsteinConstant * D) ^ k * M := by
      intro s
      simpa only [← iteratedDeriv_trigEval] using ih s
    rw [iteratedDeriv_succ, iteratedDeriv_trigEval]
    have h := norm_deriv_trigEval_le D hD ((angularStep D)^[k] p) hpoly
      (mul_nonneg (pow_nonneg (mul_nonneg bernsteinConstant_pos.le (by positivity)) k) hM0)
      hsize t
    convert h using 1
    ring

/-- The iterated estimate also covers degree zero, where the function is constant. -/
theorem norm_iteratedDeriv_trigEval_le_all (D : ℕ) (p : ℂ[X])
    (hdegree : p.natDegree ≤ 2 * D) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t : ℝ, ‖trigEval D p t‖ ≤ M) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (trigEval D p) t‖ ≤ (bernsteinConstant * D) ^ k * M := by
  by_cases hD : 0 < D
  · exact norm_iteratedDeriv_trigEval_le D hD p hdegree hM0 hM k t
  · have hD0 : D = 0 := by omega
    subst D
    have hp0 : p.natDegree = 0 := by omega
    have heq : trigEval 0 p = fun _ : ℝ => p.coeff 0 := by
      funext s
      simp only [trigEval, complexTrigEval, Nat.cast_zero, neg_zero, zero_mul,
        Complex.exp_zero, one_mul]
      simpa only [eval_C] using congrArg
        (fun q : ℂ[X] => q.eval (Complex.exp ((s : ℂ) * Complex.I)))
        (eq_C_of_natDegree_eq_zero hp0)
    cases k with
    | zero => simpa using hM t
    | succ k => simp [heq, iteratedDeriv_const]

/-- An ordinary polynomial built from the finite frequency coefficient list. -/
def coefficientPolynomial (D : ℕ) (c : ℕ → ℂ) : ℂ[X] :=
  ∑ n ∈ Finset.range (2 * D + 1), Polynomial.monomial n (c n)

theorem natDegree_coefficientPolynomial_le (D : ℕ) (c : ℕ → ℂ) :
    (coefficientPolynomial D c).natDegree ≤ 2 * D := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  exact (Polynomial.natDegree_monomial_le (c n)).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hn))

/-- The usual finite trigonometric sum with integer frequencies `-D,...,D`.
Coefficient `c n` belongs to frequency `n-D`. -/
def finiteTrigSum (D : ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (2 * D + 1),
    c n * Complex.exp (((n : ℂ) - D) * ((t : ℂ) * Complex.I))

/-- The finite Fourier sum is exactly the shifted ordinary polynomial model. -/
theorem trigEval_coefficientPolynomial (D : ℕ) (c : ℕ → ℂ) :
    trigEval D (coefficientPolynomial D c) = finiteTrigSum D c := by
  funext t
  simp only [trigEval, complexTrigEval, coefficientPolynomial, finiteTrigSum,
    eval_finsetSum, eval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have he : Complex.exp (-(D : ℂ) * ((t : ℂ) * Complex.I)) *
      Complex.exp ((t : ℂ) * Complex.I) ^ n =
      Complex.exp (((n : ℂ) - D) * ((t : ℂ) * Complex.I)) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    ring
  calc
    _ = c n * (Complex.exp (-(D : ℂ) * ((t : ℂ) * Complex.I)) *
        Complex.exp ((t : ℂ) * Complex.I) ^ n) := by ring
    _ = _ := by rw [he]

/-- Complete Bernstein replacement for arbitrary finite scalar trigonometric
sums: true real derivatives, all orders, all natural degrees, constant `2e+1`.
No complex-plane growth bound is an input. -/
theorem norm_iteratedDeriv_finiteTrigSum_le (D : ℕ) (c : ℕ → ℂ) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ t : ℝ, ‖finiteTrigSum D c t‖ ≤ M) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (finiteTrigSum D c) t‖ ≤ (bernsteinConstant * D) ^ k * M := by
  simpa only [trigEval_coefficientPolynomial] using
    norm_iteratedDeriv_trigEval_le_all D (coefficientPolynomial D c)
      (natDegree_coefficientPolynomial_le D c) hM0
      (by simpa only [trigEval_coefficientPolynomial] using hM) k t

/-- Integer-scale version convenient for the existing extraction interface,
whose degree-scale parameter is natural-valued. -/
theorem norm_iteratedDeriv_finiteTrigSum_le_seven (D : ℕ) (c : ℕ → ℂ) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ t : ℝ, ‖finiteTrigSum D c t‖ ≤ M) (k : ℕ) (t : ℝ) :
    ‖iteratedDeriv k (finiteTrigSum D c) t‖ ≤ ((7 * D : ℕ) : ℝ) ^ k * M := by
  apply (norm_iteratedDeriv_finiteTrigSum_le D c hM0 hM k t).trans
  apply mul_le_mul_of_nonneg_right _ hM0
  apply pow_le_pow_left₀ (mul_nonneg bernsteinConstant_pos.le (by positivity))
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    mul_le_mul_of_nonneg_right bernsteinConstant_lt_seven.le (Nat.cast_nonneg (α := ℝ) D)

end
end ApproxDegree.BernsteinSample
end

-- SpectralCommutator.lean
section
/-!
# Bernstein bounds for integer-weight spectral commutators

All operator norms are norms of continuous linear maps on `EuclideanSpace ℂ X`.
The entry bandwidth is an explicit input. The scalar Fourier orbit and its
uniform size bound are derived from the matrix and integer weights.
-/

namespace ApproxDegree.SpectralCommutator

open scoped BigOperators ComplexConjugate
open Complex BernsteinSample

noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]

abbrev Hilbert (X : Type*) := EuclideanSpace ℂ X

/-- The genuine Hilbert-space operator represented by a finite matrix. -/
def matrixOp (A : Matrix X X ℂ) : Hilbert X →L[ℂ] Hilbert X :=
  A.toEuclideanLin.toContinuousLinearMap

theorem matrixOp_apply (A : Matrix X X ℂ) (v : Hilbert X) (a : X) :
    matrixOp A v a = ∑ b, A a b * v b := rfl

theorem inner_matrixOp (A : Matrix X X ℂ) (u v : Hilbert X) :
    inner ℂ u (matrixOp A v) =
      ∑ r : X × X, conj (u r.1) * A r.1 r.2 * v r.2 := by
  rw [Fintype.sum_prod_type]
  simp only [PiLp.inner_apply, RCLike.inner_apply', matrixOp_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

def phaseFactor (e : X → ℤ) (t : ℝ) (a : X) : ℂ :=
  Complex.exp ((e a : ℂ) * ((t : ℂ) * Complex.I))

def phaseVector (e : X → ℤ) (t : ℝ) (v : Hilbert X) : Hilbert X :=
  WithLp.toLp 2 (fun a => phaseFactor e t a * v a)

omit [Fintype X] [DecidableEq X] in
@[simp] theorem phaseVector_apply (e : X → ℤ) (t : ℝ) (v : Hilbert X) (a : X) :
    phaseVector e t v a = phaseFactor e t a * v a := rfl

omit [Fintype X] [DecidableEq X] in
theorem norm_phaseFactor (e : X → ℤ) (t : ℝ) (a : X) :
    ‖phaseFactor e t a‖ = 1 := by
  simp [phaseFactor, Complex.norm_exp]

omit [DecidableEq X] in
/-- The diagonal spectral phase preserves the actual Euclidean Hilbert norm. -/
theorem norm_phaseVector (e : X → ℤ) (t : ℝ) (v : Hilbert X) :
    ‖phaseVector e t v‖ = ‖v‖ := by
  have hs : ‖phaseVector e t v‖ ^ 2 = ‖v‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, phaseVector_apply, norm_mul,
      norm_phaseFactor, one_mul]
  nlinarith [norm_nonneg (phaseVector e t v), norm_nonneg v]

omit [Fintype X] [DecidableEq X] in
theorem phase_pair (e : X → ℤ) (t : ℝ) (a b : X) :
    conj (phaseFactor e (-t) a) * phaseFactor e (-t) b =
      Complex.exp (((e a - e b : ℤ) : ℂ) * ((t : ℂ) * Complex.I)) := by
  simp only [phaseFactor, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp
  ring

/-- The actual scalar conjugation orbit in point coordinates. -/
def scalarOrbit (e : X → ℤ) (A : Matrix X X ℂ) (u v : Hilbert X) (t : ℝ) : ℂ :=
  ∑ r : X × X, (conj (u r.1) * A r.1 r.2 * v r.2) *
    Complex.exp (((e r.1 - e r.2 : ℤ) : ℂ) * ((t : ℂ) * Complex.I))

/-- The finite exponential sum is the genuine unitary conjugation matrix element. -/
theorem scalarOrbit_eq_inner (e : X → ℤ) (A : Matrix X X ℂ)
    (u v : Hilbert X) (t : ℝ) :
    scalarOrbit e A u v t =
      inner ℂ (phaseVector e (-t) u) (matrixOp A (phaseVector e (-t) v)) := by
  rw [inner_matrixOp]
  apply Finset.sum_congr rfl
  intro r _
  simp only [phaseVector_apply, map_mul]
  rw [← phase_pair e t r.1 r.2]
  ring

/-- Uniform size is supplied by Hilbert-space norm preservation and the true
operator norm, rather than a coefficientwise estimate. -/
theorem norm_scalarOrbit_le (e : X → ℤ) (A : Matrix X X ℂ)
    (u v : Hilbert X) (t : ℝ) :
    ‖scalarOrbit e A u v t‖ ≤ ‖u‖ * ‖matrixOp A‖ * ‖v‖ := by
  rw [scalarOrbit_eq_inner]
  calc
    _ ≤ ‖phaseVector e (-t) u‖ * ‖matrixOp A (phaseVector e (-t) v)‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖phaseVector e (-t) u‖ * (‖matrixOp A‖ * ‖phaseVector e (-t) v‖) :=
      mul_le_mul_of_nonneg_left ((matrixOp A).le_opNorm _) (norm_nonneg _)
    _ = _ := by rw [norm_phaseVector, norm_phaseVector]; ring

/-- Entry bandwidth in the supplied integer spectral weights. -/
def HasBandwidth (e : X → ℤ) (D : ℕ) (A : Matrix X X ℂ) : Prop :=
  ∀ a b, (D : ℤ) < |e a - e b| → A a b = 0

section FiniteFourier

variable {J : Type*} [Fintype J]

/-- Collect arbitrary finitely many integer frequencies into the standard range. -/
def frequencyCoefficients (D : ℕ) (f : J → ℤ) (a : J → ℂ) (n : ℕ) : ℂ :=
  ∑ j, if f j = (n : ℤ) - D then a j else 0

theorem single_frequency_sum (D : ℕ) (l : ℤ) (hl : |l| ≤ (D : ℤ))
    (a : ℂ) (t : ℝ) :
    (∑ n ∈ Finset.range (2 * D + 1),
      (if l = (n : ℤ) - D then a else 0) *
        Complex.exp (((n : ℂ) - D) * ((t : ℂ) * Complex.I))) =
      a * Complex.exp ((l : ℂ) * ((t : ℂ) * Complex.I)) := by
  have hlow : 0 ≤ l + D := by have := (abs_le.mp hl).1; omega
  have hupp : l + D ≤ (2 * D : ℕ) := by have := (abs_le.mp hl).2; omega
  let n : ℕ := (l + D).toNat
  have hncast : (n : ℤ) = l + D := Int.toNat_of_nonneg hlow
  have hnmem : n ∈ Finset.range (2 * D + 1) := by
    apply Finset.mem_range.mpr
    omega
  have hfreq : l = (n : ℤ) - D := by omega
  rw [Finset.sum_eq_single n]
  · rw [if_pos hfreq]
    congr 2
    have hc : (n : ℂ) - D = (l : ℂ) := by exact_mod_cast hfreq.symm
    rw [hc]
  · intro m _ hmn
    have hm : l ≠ (m : ℤ) - D := by intro h; apply hmn; omega
    simp only [if_neg hm, zero_mul]
  · exact fun h => False.elim (h hnmem)

/-- The Fourier representation follows from finite support and integer bandwidth. -/
theorem finite_sum_eq_finiteTrigSum (D : ℕ) (f : J → ℤ) (a : J → ℂ)
    (hband : ∀ j, (D : ℤ) < |f j| → a j = 0) (t : ℝ) :
    (∑ j, a j * Complex.exp ((f j : ℂ) * ((t : ℂ) * Complex.I))) =
      finiteTrigSum D (frequencyCoefficients D f a) t := by
  simp only [finiteTrigSum, frequencyCoefficients, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : |f j| ≤ (D : ℤ)
  · exact (single_frequency_sum D (f j) hj (a j) t).symm
  · have ha := hband j (lt_of_not_ge hj)
    simp [ha]

end FiniteFourier

def orbitCoefficients (D : ℕ) (e : X → ℤ) (A : Matrix X X ℂ)
    (u v : Hilbert X) : ℕ → ℂ :=
  frequencyCoefficients D (fun r : X × X => e r.1 - e r.2)
    (fun r => conj (u r.1) * A r.1 r.2 * v r.2)

omit [DecidableEq X] in
theorem scalarOrbit_eq_finiteTrigSum (e : X → ℤ) (D : ℕ) (A : Matrix X X ℂ)
    (hband : HasBandwidth e D A) (u v : Hilbert X) :
    scalarOrbit e A u v = finiteTrigSum D (orbitCoefficients D e A u v) := by
  funext t
  apply finite_sum_eq_finiteTrigSum
  intro r hr
  simp [hband r.1 r.2 hr]

/-- The literal matrix commutator with the supplied integer-weight diagonal. -/
def diagonalCommutator (e : X → ℤ) (A : Matrix X X ℂ) : Matrix X X ℂ :=
  Matrix.diagonal (fun a => (e a : ℂ)) * A - A * Matrix.diagonal (fun a => (e a : ℂ))

theorem diagonalCommutator_apply (e : X → ℤ) (A : Matrix X X ℂ) (a b : X) :
    diagonalCommutator e A a b = ((e a - e b : ℤ) : ℂ) * A a b := by
  simp only [diagonalCommutator, Matrix.sub_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Int.cast_sub]
  ring

theorem hasBandwidth_diagonalCommutator (e : X → ℤ) (D : ℕ) (A : Matrix X X ℂ)
    (hband : HasBandwidth e D A) : HasBandwidth e D (diagonalCommutator e A) := by
  intro a b hab
  rw [diagonalCommutator_apply, hband a b hab, mul_zero]

/-- The derivative of the actual scalar orbit at zero is `I` times the
actual diagonal commutator matrix element. -/
theorem deriv_scalarOrbit_zero (e : X → ℤ) (A : Matrix X X ℂ) (u v : Hilbert X) :
    deriv (scalarOrbit e A u v) 0 =
      Complex.I * inner ℂ u (matrixOp (diagonalCommutator e A) v) := by
  have hterm (r : X × X) :
      HasDerivAt (fun t : ℝ => (conj (u r.1) * A r.1 r.2 * v r.2) *
        Complex.exp (((e r.1 - e r.2 : ℤ) : ℂ) * ((t : ℂ) * Complex.I)))
        ((conj (u r.1) * A r.1 r.2 * v r.2) *
          (((e r.1 - e r.2 : ℤ) : ℂ) * Complex.I)) 0 := by
    have h := ((((hasDerivAt_id (0 : ℂ)).mul_const Complex.I).const_mul
      (((e r.1 - e r.2 : ℤ) : ℂ))).cexp).const_mul
        (conj (u r.1) * A r.1 r.2 * v r.2)
    have hc : HasDerivAt (fun z : ℂ => (conj (u r.1) * A r.1 r.2 * v r.2) *
        Complex.exp (((e r.1 - e r.2 : ℤ) : ℂ) * (z * Complex.I)))
        ((conj (u r.1) * A r.1 r.2 * v r.2) *
          (((e r.1 - e r.2 : ℤ) : ℂ) * Complex.I)) 0 := by
      simpa only [id_eq, zero_mul, mul_zero, Complex.exp_zero, one_mul] using h
    exact hc.comp_ofReal
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun r _ => hterm r)
  have hderiv : HasDerivAt (scalarOrbit e A u v)
    (∑ r : X × X, (conj (u r.1) * A r.1 r.2 * v r.2) *
      (((e r.1 - e r.2 : ℤ) : ℂ) * Complex.I)) 0 := by
    apply hsum.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun t => by simp only [scalarOrbit, Finset.sum_apply])
  rw [hderiv.deriv, inner_matrixOp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [diagonalCommutator_apply]
  ring

/-- The scalar Bernstein estimate applied to the derived orbit, with all
Fourier and uniform-norm hypotheses discharged. -/
theorem norm_inner_diagonalCommutator_le (e : X → ℤ) (D : ℕ) (A : Matrix X X ℂ)
    (hband : HasBandwidth e D A) (u v : Hilbert X)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖inner ℂ u (matrixOp (diagonalCommutator e A) v)‖ ≤
      ((7 * D : ℕ) : ℝ) * ‖matrixOp A‖ := by
  have horbit : ∀ t : ℝ, ‖scalarOrbit e A u v t‖ ≤ ‖matrixOp A‖ := by
    intro t
    simpa only [hu, hv, one_mul, mul_one] using norm_scalarOrbit_le e A u v t
  have hfourier := scalarOrbit_eq_finiteTrigSum e D A hband u v
  have hb := norm_iteratedDeriv_finiteTrigSum_le_seven D (orbitCoefficients D e A u v)
    (norm_nonneg (matrixOp A)) (by simpa only [← hfourier] using horbit) 1 0
  rw [← hfourier] at hb
  simpa only [iteratedDeriv_one, deriv_scalarOrbit_zero, norm_mul, Complex.norm_I,
    one_mul, pow_one] using hb

/-- A genuine Hilbert operator-norm commutator estimate. -/
theorem norm_diagonalCommutator_le (e : X → ℤ) (D : ℕ) (A : Matrix X X ℂ)
    (hband : HasBandwidth e D A) :
    ‖matrixOp (diagonalCommutator e A)‖ ≤ ((7 * D : ℕ) : ℝ) * ‖matrixOp A‖ := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (𝕜 := ℂ) (by positivity)
  intro x y hx hy
  calc
    (inner ℂ (matrixOp (diagonalCommutator e A) x) y).re ≤
        ‖inner ℂ (matrixOp (diagonalCommutator e A) x) y‖ := Complex.re_le_norm _
    _ = ‖inner ℂ y (matrixOp (diagonalCommutator e A) x)‖ := norm_inner_symm _ _
    _ ≤ _ := norm_inner_diagonalCommutator_le e D A hband y x hy hx

/-- The bandwidth persists under arbitrary diagonal commutator iterations. -/
theorem hasBandwidth_iterate_diagonalCommutator (e : X → ℤ) (D : ℕ)
    (A : Matrix X X ℂ) (hband : HasBandwidth e D A) (k : ℕ) :
    HasBandwidth e D ((diagonalCommutator e)^[k] A) := by
  induction k with
  | zero => simpa using hband
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hasBandwidth_diagonalCommutator e D _ ih

/-- Every commutator iterate satisfies the linear-degree Hilbert norm estimate. -/
theorem norm_iterate_diagonalCommutator_le (e : X → ℤ) (D : ℕ)
    (A : Matrix X X ℂ) (hband : HasBandwidth e D A) (k : ℕ) :
    ‖matrixOp ((diagonalCommutator e)^[k] A)‖ ≤
      ((7 * D : ℕ) : ℝ) ^ k * ‖matrixOp A‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ ((7 * D : ℕ) : ℝ) * ‖matrixOp ((diagonalCommutator e)^[k] A)‖ :=
        norm_diagonalCommutator_le e D _ (hasBandwidth_iterate_diagonalCommutator e D A hband k)
      _ ≤ ((7 * D : ℕ) : ℝ) * (((7 * D : ℕ) : ℝ) ^ k * ‖matrixOp A‖) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by ring

theorem matrixOp_mul (A B : Matrix X X ℂ) :
    matrixOp (A * B) = matrixOp A * matrixOp B := by
  apply ContinuousLinearMap.ext
  intro v
  change Matrix.toEuclideanLin (A * B) v =
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v)
  exact congrArg (fun L : Hilbert X →ₗ[ℂ] Hilbert X => L v)
    (Matrix.toLpLin_mul 2 2 2 A B)

theorem matrixOp_sub (A B : Matrix X X ℂ) :
    matrixOp (A - B) = matrixOp A - matrixOp B := by
  apply ContinuousLinearMap.ext
  intro v
  change Matrix.toEuclideanLin (A - B) v =
    (Matrix.toEuclideanLin A - Matrix.toEuclideanLin B) v
  exact congrArg (fun L : Hilbert X →ₗ[ℂ] Hilbert X => L v)
    (map_sub Matrix.toEuclideanLin A B)

/-- The supplied integer-weight diagonal, as a genuine Hilbert operator. -/
def weightOperator (e : X → ℤ) : Hilbert X →L[ℂ] Hilbert X :=
  matrixOp (Matrix.diagonal (fun a => (e a : ℂ)))

theorem matrixOp_diagonalCommutator (e : X → ℤ) (A : Matrix X X ℂ) :
    matrixOp (diagonalCommutator e A) =
      weightOperator e * matrixOp A - matrixOp A * weightOperator e := by
  rw [diagonalCommutator, matrixOp_sub, matrixOp_mul, matrixOp_mul]
  rfl

theorem matrixOp_iterate_diagonalCommutator (e : X → ℤ) (A : Matrix X X ℂ) (k : ℕ) :
    matrixOp ((diagonalCommutator e)^[k] A) =
      (fun T => weightOperator e * T - T * weightOperator e)^[k] (matrixOp A) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', matrixOp_diagonalCommutator, ih]

/-- Operator formulation of the full Bernstein commutator bound.
The hypothesis is concrete entry bandwidth; neither a Fourier representation
nor a scalar sample bound is assumed. -/
theorem norm_iterated_hilbertCommutator_le (e : X → ℤ) (D : ℕ)
    (A : Matrix X X ℂ) (hband : HasBandwidth e D A) (k : ℕ) :
    ‖(fun T => weightOperator e * T - T * weightOperator e)^[k] (matrixOp A)‖ ≤
      ((7 * D : ℕ) : ℝ) ^ k * ‖matrixOp A‖ := by
  rw [← matrixOp_iterate_diagonalCommutator]
  exact norm_iterate_diagonalCommutator_le e D A hband k

end
end ApproxDegree.SpectralCommutator
end

-- ProjectionCommutator.lean
section
/-!
# Hilbert commutator estimates from an orthogonal projection resolution

The phase orbit and its finite Fourier expansion are derived directly from
the projections. No adapted eigenbasis, orbit estimate, or matrix norm is
assumed. The result works on any complete complex Hilbert space.
-/

namespace ApproxDegree.ProjectionCommutator

open scoped BigOperators ComplexConjugate
open Complex BernsteinSample

noncomputable section

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Fintype ι]

/-- A concrete finite orthogonal resolution of the identity. -/
structure IsResolution (R : ι → E →L[ℂ] E) : Prop where
  selfAdjoint : ∀ a, IsSelfAdjoint (R a)
  idempotent : ∀ a, R a * R a = R a
  orthogonal : ∀ a b, a ≠ b → R a * R b = 0
  total : ∑ a, R a = 1

def spectralSum (R : ι → E →L[ℂ] E) (c : ι → ℂ) : E →L[ℂ] E :=
  ∑ a, c a • R a

theorem spectralSum_mul_projection (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (c : ι → ℂ) (a : ι) : spectralSum R c * R a = c a • R a := by
  rw [spectralSum, Finset.sum_mul]
  rw [Finset.sum_eq_single a]
  · rw [smul_mul_assoc, hR.idempotent]
  · intro b _ hba
    rw [smul_mul_assoc, hR.orthogonal b a hba, smul_zero]
  · exact fun h => False.elim (h (Finset.mem_univ a))

theorem projection_mul_spectralSum (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (c : ι → ℂ) (a : ι) : R a * spectralSum R c = c a • R a := by
  rw [spectralSum, Finset.mul_sum]
  rw [Finset.sum_eq_single a]
  · rw [mul_smul_comm, hR.idempotent]
  · intro b _ hba
    rw [mul_smul_comm, hR.orthogonal a b (Ne.symm hba), smul_zero]
  · exact fun h => False.elim (h (Finset.mem_univ a))

theorem spectralSum_mul (R : ι → E →L[ℂ] E) (hR : IsResolution R) (c d : ι → ℂ) :
    spectralSum R c * spectralSum R d = spectralSum R (fun a => c a * d a) := by
  change spectralSum R c * (∑ a, d a • R a) = ∑ a, (c a * d a) • R a
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_smul_comm, spectralSum_mul_projection R hR, smul_smul, mul_comm]

theorem spectralSum_star (R : ι → E →L[ℂ] E) (hR : IsResolution R) (c : ι → ℂ) :
    star (spectralSum R c) = spectralSum R (fun a => star (c a)) := by
  simp only [spectralSum, star_sum, star_smul, (hR.selfAdjoint _).star_eq]

def phase (R : ι → E →L[ℂ] E) (e : ι → ℤ) (t : ℝ) : E →L[ℂ] E :=
  spectralSum R (SpectralCommutator.phaseFactor e t)

theorem phase_star (R : ι → E →L[ℂ] E) (hR : IsResolution R) (e : ι → ℤ) (t : ℝ) :
    star (phase R e t) = phase R e (-t) := by
  rw [phase, spectralSum_star R hR]
  unfold phase spectralSum
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  simp only [star_def, SpectralCommutator.phaseFactor, ← Complex.exp_conj]
  congr 1
  simp

theorem phase_mul_neg (R : ι → E →L[ℂ] E) (hR : IsResolution R) (e : ι → ℤ) (t : ℝ) :
    phase R e t * phase R e (-t) = 1 := by
  rw [phase, phase, spectralSum_mul R hR]
  have hf (a : ι) : SpectralCommutator.phaseFactor e t a *
      SpectralCommutator.phaseFactor e (-t) a = 1 := by
    simp only [SpectralCommutator.phaseFactor, ← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    simp
  simpa only [spectralSum, hf, one_smul] using hR.total

/-- The explicitly constructed phase is a unitary Hilbert operator. -/
theorem phase_mem_unitary (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (t : ℝ) : phase R e t ∈ unitary (E →L[ℂ] E) := by
  apply Unitary.mem_iff.mpr
  rw [phase_star R hR]
  exact ⟨by simpa only [neg_neg] using phase_mul_neg R hR e (-t), phase_mul_neg R hR e t⟩

theorem norm_phase_apply (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (t : ℝ) (v : E) : ‖phase R e t v‖ = ‖v‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (phase_mem_unitary R hR e t) v

def generator (R : ι → E →L[ℂ] E) (e : ι → ℤ) : E →L[ℂ] E :=
  spectralSum R (fun a => (e a : ℂ))

def commutator (R : ι → E →L[ℂ] E) (e : ι → ℤ) (B : E →L[ℂ] E) : E →L[ℂ] E :=
  generator R e * B - B * generator R e

def HasBandwidth (R : ι → E →L[ℂ] E) (e : ι → ℤ) (D : ℕ) (B : E →L[ℂ] E) : Prop :=
  ∀ a b, (D : ℤ) < |e a - e b| → R a * B * R b = 0

theorem block_commutator (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (B : E →L[ℂ] E) (a b : ι) :
    R a * commutator R e B * R b =
      ((e a - e b : ℤ) : ℂ) • (R a * B * R b) := by
  calc
    _ = (R a * generator R e) * B * R b - R a * B * (generator R e * R b) := by
      unfold commutator
      noncomm_ring
    _ = _ := by
      rw [generator, projection_mul_spectralSum R hR, spectralSum_mul_projection R hR]
      simp only [smul_mul_assoc, mul_smul_comm, Int.cast_sub, sub_smul]

theorem sum_blocks (R : ι → E →L[ℂ] E) (hR : IsResolution R) (B : E →L[ℂ] E) :
    (∑ r : ι × ι, R r.1 * B * R r.2) = B := by
  rw [Fintype.sum_prod_type]
  calc
    _ = (∑ a, R a) * B * (∑ b, R b) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = B := by rw [hR.total]; simp

theorem commutator_eq_sum_blocks (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (B : E →L[ℂ] E) :
    commutator R e B = ∑ r : ι × ι,
      ((e r.1 - e r.2 : ℤ) : ℂ) • (R r.1 * B * R r.2) := by
  rw [← sum_blocks R hR (commutator R e B)]
  apply Finset.sum_congr rfl
  intro r _
  exact block_commutator R hR e B r.1 r.2

def scalarOrbit (R : ι → E →L[ℂ] E) (e : ι → ℤ) (B : E →L[ℂ] E)
    (u v : E) (t : ℝ) : ℂ :=
  ∑ r : ι × ι, inner ℂ u ((R r.1 * B * R r.2) v) *
    Complex.exp (((e r.1 - e r.2 : ℤ) : ℂ) * ((t : ℂ) * Complex.I))

theorem block_inner (R : ι → E →L[ℂ] E) (hR : IsResolution R) (B : E →L[ℂ] E)
    (u v : E) (a b : ι) :
    inner ℂ u ((R a * B * R b) v) = inner ℂ (R a u) (B (R b v)) :=
  ((hR.selfAdjoint a).isSymmetric u (B (R b v))).symm

/-- The Fourier sum is the actual matrix element of unitary conjugation. -/
theorem scalarOrbit_eq_inner (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (B : E →L[ℂ] E) (u v : E) (t : ℝ) :
    scalarOrbit R e B u v t = inner ℂ (phase R e (-t) u) (B (phase R e (-t) v)) := by
  simp only [scalarOrbit, Fintype.sum_prod_type, phase, spectralSum,
    sum_apply, smul_apply, map_sum, map_smul,
    sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [block_inner R hR, ← SpectralCommutator.phase_pair e t a b]
  ring

/-- Uniform orbit size comes from genuine Hilbert unitarity and operator norm. -/
theorem norm_scalarOrbit_le (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (B : E →L[ℂ] E) (u v : E) (t : ℝ) :
    ‖scalarOrbit R e B u v t‖ ≤ ‖u‖ * ‖B‖ * ‖v‖ := by
  rw [scalarOrbit_eq_inner R hR]
  calc
    _ ≤ ‖phase R e (-t) u‖ * ‖B (phase R e (-t) v)‖ := norm_inner_le_norm _ _
    _ ≤ ‖phase R e (-t) u‖ * (‖B‖ * ‖phase R e (-t) v‖) :=
      mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg _)
    _ = _ := by rw [norm_phase_apply R hR, norm_phase_apply R hR]; ring

def orbitCoefficients (R : ι → E →L[ℂ] E) (e : ι → ℤ) (D : ℕ)
    (B : E →L[ℂ] E) (u v : E) : ℕ → ℂ :=
  SpectralCommutator.frequencyCoefficients D (fun r : ι × ι => e r.1 - e r.2)
    (fun r => inner ℂ u ((R r.1 * B * R r.2) v))

omit [CompleteSpace E] in
/-- The Fourier representation is derived from the supplied spectral blocks. -/
theorem scalarOrbit_eq_finiteTrigSum (R : ι → E →L[ℂ] E) (e : ι → ℤ) (D : ℕ)
    (B : E →L[ℂ] E) (hband : HasBandwidth R e D B) (u v : E) :
    scalarOrbit R e B u v = finiteTrigSum D (orbitCoefficients R e D B u v) := by
  funext t
  apply SpectralCommutator.finite_sum_eq_finiteTrigSum
  intro r hr
  simp only [hband r.1 r.2 hr, zero_apply, inner_zero_right]

/-- Differentiation of the actual projection orbit gives the actual
commutator matrix element, with the exact factor `I`. -/
theorem deriv_scalarOrbit_zero (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (B : E →L[ℂ] E) (u v : E) :
    deriv (scalarOrbit R e B u v) 0 = Complex.I * inner ℂ u (commutator R e B v) := by
  have hterm (r : ι × ι) :
      HasDerivAt (fun t : ℝ => inner ℂ u ((R r.1 * B * R r.2) v) *
        Complex.exp (((e r.1 - e r.2 : ℤ) : ℂ) * ((t : ℂ) * Complex.I)))
        (inner ℂ u ((R r.1 * B * R r.2) v) *
          (((e r.1 - e r.2 : ℤ) : ℂ) * Complex.I)) 0 := by
    have h := ((((hasDerivAt_id (0 : ℂ)).mul_const Complex.I).const_mul
      (((e r.1 - e r.2 : ℤ) : ℂ))).cexp).const_mul
        (inner ℂ u ((R r.1 * B * R r.2) v))
    have hc : HasDerivAt (fun z : ℂ => inner ℂ u ((R r.1 * B * R r.2) v) *
        Complex.exp (((e r.1 - e r.2 : ℤ) : ℂ) * (z * Complex.I)))
        (inner ℂ u ((R r.1 * B * R r.2) v) *
          (((e r.1 - e r.2 : ℤ) : ℂ) * Complex.I)) 0 := by
      simpa only [id_eq, zero_mul, mul_zero, Complex.exp_zero, one_mul] using h
    exact hc.comp_ofReal
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun r _ => hterm r)
  have hd : HasDerivAt (scalarOrbit R e B u v)
      (∑ r : ι × ι, inner ℂ u ((R r.1 * B * R r.2) v) *
        (((e r.1 - e r.2 : ℤ) : ℂ) * Complex.I)) 0 := by
    apply hsum.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun t => by simp only [scalarOrbit, Finset.sum_apply])
  rw [hd.deriv, commutator_eq_sum_blocks R hR]
  simp only [sum_apply, smul_apply, inner_sum, inner_smul_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem hasBandwidth_commutator (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (D : ℕ) (B : E →L[ℂ] E) (hband : HasBandwidth R e D B) :
    HasBandwidth R e D (commutator R e B) := by
  intro a b hab
  rw [block_commutator R hR, hband a b hab, smul_zero]

/-- Unit-vector scalar estimate with all orbit and Fourier inputs derived. -/
theorem norm_inner_commutator_le (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (D : ℕ) (B : E →L[ℂ] E) (hband : HasBandwidth R e D B)
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖inner ℂ u (commutator R e B v)‖ ≤ ((7 * D : ℕ) : ℝ) * ‖B‖ := by
  have horbit : ∀ t : ℝ, ‖scalarOrbit R e B u v t‖ ≤ ‖B‖ := by
    intro t
    simpa only [hu, hv, one_mul, mul_one] using norm_scalarOrbit_le R hR e B u v t
  have hf := scalarOrbit_eq_finiteTrigSum R e D B hband u v
  have h := norm_iteratedDeriv_finiteTrigSum_le_seven D (orbitCoefficients R e D B u v)
    (norm_nonneg B) (by simpa only [← hf] using horbit) 1 0
  rw [← hf] at h
  simpa only [iteratedDeriv_one, deriv_scalarOrbit_zero R hR, norm_mul,
    Complex.norm_I, one_mul, pow_one] using h

/-- The genuine Hilbert operator-norm estimate, with no adapted basis. -/
theorem norm_commutator_le (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (D : ℕ) (B : E →L[ℂ] E) (hband : HasBandwidth R e D B) :
    ‖commutator R e B‖ ≤ ((7 * D : ℕ) : ℝ) * ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (𝕜 := ℂ) (by positivity)
  intro x y hx hy
  calc
    (inner ℂ (commutator R e B x) y).re ≤ ‖inner ℂ (commutator R e B x) y‖ :=
      Complex.re_le_norm _
    _ = ‖inner ℂ y (commutator R e B x)‖ := norm_inner_symm _ _
    _ ≤ _ := norm_inner_commutator_le R hR e D B hband y x hy hx

theorem hasBandwidth_iterated_commutator (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (D : ℕ) (B : E →L[ℂ] E) (hband : HasBandwidth R e D B) (k : ℕ) :
    HasBandwidth R e D ((commutator R e)^[k] B) := by
  induction k with
  | zero => simpa using hband
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact hasBandwidth_commutator R hR e D _ ih

/-- The full iterated commutator estimate for a finite orthogonal spectral
resolution on an arbitrary complete complex Hilbert space. -/
theorem norm_iterated_commutator_le (R : ι → E →L[ℂ] E) (hR : IsResolution R)
    (e : ι → ℤ) (D : ℕ) (B : E →L[ℂ] E) (hband : HasBandwidth R e D B) (k : ℕ) :
    ‖(commutator R e)^[k] B‖ ≤ ((7 * D : ℕ) : ℝ) ^ k * ‖B‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc
      _ ≤ ((7 * D : ℕ) : ℝ) * ‖(commutator R e)^[k] B‖ :=
        norm_commutator_le R hR e D _ (hasBandwidth_iterated_commutator R hR e D B hband k)
      _ ≤ ((7 * D : ℕ) : ℝ) * (((7 * D : ℕ) : ℝ) ^ k * ‖B‖) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ = _ := by ring

/-- Interface for a supplied generator identified with the spectral sum. -/
theorem norm_iterated_commutator_le_of_generator_eq (R : ι → E →L[ℂ] E)
    (hR : IsResolution R) (e : ι → ℤ) (H : E →L[ℂ] E)
    (hH : H = ∑ a, (e a : ℂ) • R a) (D : ℕ) (B : E →L[ℂ] E)
    (hband : HasBandwidth R e D B) (k : ℕ) :
    ‖(fun T => H * T - T * H)^[k] B‖ ≤ ((7 * D : ℕ) : ℝ) ^ k * ‖B‖ := by
  subst H
  exact norm_iterated_commutator_le R hR e D B hband k

end
end ApproxDegree.ProjectionCommutator
end

-- PhaseAverage.lean
section
/-!
# The common-phase alternating average

This file isolates the finite Fourier calculation in equation (6) of the
short composition proof. `phaseSample` is a Laurent polynomial with frequencies
`-k, ..., k`, written as an ordinary polynomial divided by the kth power of
its argument. Its sample points are `I * ζ ^ j`, where `ζ` is any primitive
`(2*k)`th root of unity. Primitivity is the only explicit sampling hypothesis.

No commutator, bandwidth, or approximate-degree statement is assumed or proved
here. The endpoint coefficient relation and the sample bounds are the inputs
to the final inequality.
-/

open scoped BigOperators
open Finset Complex

namespace ApproxDegree.PhaseAverage

noncomputable section

/-- Interior powers have zero sum over a complete primitive-root orbit. -/
theorem root_sum_interior {N r : ℕ} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ N) (hr0 : 0 < r) (hrN : r < N) :
    (∑ j ∈ range N, (ζ ^ j) ^ r) = 0 := by
  have hne : ζ ^ r ≠ 1 := hζ.pow_ne_one_of_pos_of_lt hr0.ne' hrN
  have hpow : (ζ ^ r) ^ N = 1 := by
    rw [← pow_mul, Nat.mul_comm r N, pow_mul, hζ.pow_eq_one, one_pow]
  have hg : (∑ j ∈ range N, (ζ ^ r) ^ j) = 0 := by
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]
  simpa only [← pow_mul, Nat.mul_comm] using hg

/-- The two endpoint powers are both constant on the primitive-root orbit. -/
theorem root_sum_endpoints {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) :
    (∑ j ∈ range N, (ζ ^ j) ^ 0) = (N : ℂ) ∧
    (∑ j ∈ range N, (ζ ^ j) ^ N) = (N : ℂ) := by
  constructor
  · simp
  · have hh : ∀ j : ℕ, (ζ ^ j) ^ N = 1 := by
      intro j
      rw [← pow_mul, Nat.mul_comm j N, pow_mul, hζ.pow_eq_one, one_pow]
    simp only [hh, sum_const, card_range, nsmul_eq_mul, mul_one]

/-- An orbit sum of a polynomial of degree at most N retains only its endpoints. -/
theorem sum_polynomial_orbit {N : ℕ} {ζ : ℂ}
    (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (t : ℂ) (c : ℕ → ℂ) :
    (∑ j ∈ range N, ∑ r ∈ range (N + 1), c r * (t * ζ ^ j) ^ r) =
      (N : ℂ) * (c 0 + c N * t ^ N) := by
  rw [sum_comm]
  simp_rw [mul_pow, ← mul_assoc, ← mul_sum]
  rw [sum_range_succ]
  have hlower :
      (∑ r ∈ range N, c r * t ^ r * ∑ j ∈ range N, (ζ ^ j) ^ r) =
        (N : ℂ) * c 0 := by
    rw [sum_eq_single 0]
    · simp [mul_comm]
    · intro r hr hr0
      rw [root_sum_interior hζ (Nat.pos_of_ne_zero hr0) (mem_range.mp hr)]
      simp
    · intro hn
      exact (hn (mem_range.mpr hN)).elim
  rw [hlower, (root_sum_endpoints hζ).2]
  ring

/-- A Laurent polynomial sampled at the common-phase grid. Coefficient `c r`
has frequency `r-k`; the two extreme coefficients are `c 0` and `c (2*k)`. -/
def phaseSample (k : ℕ) (ζ : ℂ) (c : ℕ → ℂ) (j : ℕ) : ℂ :=
  ((I * ζ ^ j) ^ k)⁻¹ *
    ∑ r ∈ range (2 * k + 1), c r * (I * ζ ^ j) ^ r

/-- Explicit connection to the integer-frequency Laurent representation. -/
theorem phaseSample_eq_laurent (k : ℕ) {ζ : ℂ} (hζ : ζ ≠ 0)
    (c : ℕ → ℂ) (j : ℕ) :
    phaseSample k ζ c j =
      ∑ r ∈ range (2 * k + 1), c r * (I * ζ ^ j) ^ ((r : ℤ) - (k : ℤ)) := by
  have hz : I * ζ ^ j ≠ 0 := mul_ne_zero I_ne_zero (pow_ne_zero j hζ)
  unfold phaseSample
  rw [mul_sum]
  apply sum_congr rfl
  intro r hr
  rw [zpow_sub₀ hz, zpow_natCast, zpow_natCast, div_eq_mul_inv]
  ring

theorem primitive_half_power {k : ℕ} {ζ : ℂ}
    (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2 * k)) : ζ ^ k = -1 := by
  exact (hζ.pow (by omega) (by omega : 2 * k = k * 2)).eq_neg_one_of_two_right

/-- The Laurent shift contributes exactly the alternating sampling weight. -/
theorem phaseSample_shift {k : ℕ} {ζ : ℂ}
    (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2 * k)) (c : ℕ → ℂ) (j : ℕ) :
    phaseSample k ζ c j =
      (-I) ^ k * (-1 : ℂ) ^ j *
        ∑ r ∈ range (2 * k + 1), c r * (I * ζ ^ j) ^ r := by
  have hh : (ζ ^ j) ^ k = (-1 : ℂ) ^ j := by
    rw [← pow_mul, Nat.mul_comm j k, pow_mul, primitive_half_power hk hζ]
  unfold phaseSample
  congr 1
  simp [mul_pow, hh, ← inv_pow, inv_I, mul_comm]

/-- The alternating sum annihilates all interior Laurent frequencies. -/
theorem alternating_sum {k : ℕ} {ζ : ℂ}
    (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2 * k)) (c : ℕ → ℂ) :
    (∑ j ∈ range (2 * k), (-1 : ℂ) ^ j * phaseSample k ζ c j) =
      ((2 * k : ℕ) : ℂ) * (-I) ^ k *
        (c 0 + c (2 * k) * I ^ (2 * k)) := by
  have hterm : ∀ j : ℕ,
      (-1 : ℂ) ^ j * phaseSample k ζ c j =
        (-I) ^ k * ∑ r ∈ range (2 * k + 1), c r * (I * ζ ^ j) ^ r := by
    intro j
    rw [phaseSample_shift hk hζ]
    have hs : (-1 : ℂ) ^ j * (-1 : ℂ) ^ j = 1 := by
      rw [← mul_pow]
      simp
    calc
      _ = (-I) ^ k * ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) *
          ∑ r ∈ range (2 * k + 1), c r * (I * ζ ^ j) ^ r := by ring
      _ = _ := by rw [hs]; ring
  simp_rw [hterm]
  rw [← mul_sum, sum_polynomial_orbit (by omega) hζ]
  ring

/-- The general common-phase extraction, with the two prescribed extreme coefficients. -/
theorem alternating_average {k : ℕ} {ζ A : ℂ}
    (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2 * k)) (c : ℕ → ℂ)
    (hc0 : c 0 = A) (hcTop : c (2 * k) = (-1 : ℂ) ^ k * A) :
    (∑ j ∈ range (2 * k), (-1 : ℂ) ^ j * phaseSample k ζ c j) /
        ((2 * k : ℕ) : ℂ) = 2 * (-I) ^ k * A := by
  have hn : ((2 * k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2 * k ≠ 0 by omega)
  have hi : I ^ (2 * k) = (-1 : ℂ) ^ k := by rw [pow_mul, I_sq]
  have hs : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    simp
  rw [alternating_sum hk hζ, hc0, hcTop, hi]
  have hb : A + (-1 : ℂ) ^ k * A * (-1 : ℂ) ^ k = 2 * A := by
    calc
      _ = A + ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * A := by ring
      _ = _ := by rw [hs]; ring
  rw [hb]
  field_simp

/-- Bounded samples force twice the norm of the common extreme coefficient
to be bounded by the same M, for every positive k. -/
theorem twice_norm_le {k : ℕ} {ζ A : ℂ} {M : ℝ}
    (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2 * k)) (c : ℕ → ℂ)
    (hc0 : c 0 = A) (hcTop : c (2 * k) = (-1 : ℂ) ^ k * A)
    (hbound : ∀ j ∈ range (2 * k), ‖phaseSample k ζ c j‖ ≤ M) :
    2 * ‖A‖ ≤ M := by
  have havg := alternating_average hk hζ c hc0 hcTop
  have hn : (0 : ℝ) < ((2 * k : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * k by omega)
  have hsum :
      ‖∑ j ∈ range (2 * k), (-1 : ℂ) ^ j * phaseSample k ζ c j‖ ≤
        ((2 * k : ℕ) : ℝ) * M := by
    calc
      _ ≤ ∑ j ∈ range (2 * k), ‖(-1 : ℂ) ^ j * phaseSample k ζ c j‖ :=
        norm_sum_le _ _
      _ = ∑ j ∈ range (2 * k), ‖phaseSample k ζ c j‖ := by simp
      _ ≤ ∑ j ∈ range (2 * k), M := sum_le_sum hbound
      _ = _ := by simp
  have hnorm := congrArg norm havg
  simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_I, one_pow,
    mul_one, norm_ofNat, Complex.norm_natCast] at hnorm
  rw [← hnorm]
  exact (div_le_iff₀ hn).mpr (by simpa [mul_comm] using hsum)

/-- The canonical root gives the equally spaced grid of the short proof. -/
def standardRoot (k : ℕ) : ℂ :=
  exp (2 * (Real.pi : ℂ) * I / ((2 * k : ℕ) : ℂ))

theorem standardRoot_primitive {k : ℕ} (hk : 0 < k) :
    IsPrimitiveRoot (standardRoot k) (2 * k) := by
  exact isPrimitiveRoot_exp (2 * k) (by omega)

/-- These are exactly the phase points `exp(I * (pi/2 + pi*j/k))`. -/
theorem standard_grid {k : ℕ} (hk : 0 < k) (j : ℕ) :
    I * standardRoot k ^ j =
      exp (((Real.pi : ℂ) / 2 + (Real.pi : ℂ) * (j : ℂ) / (k : ℂ)) * I) := by
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  calc
    I * standardRoot k ^ j =
        exp ((Real.pi : ℂ) / 2 * I) *
          exp ((j : ℂ) * (2 * (Real.pi : ℂ) * I / ((2 * k : ℕ) : ℂ))) := by
      rw [exp_pi_div_two_mul_I, exp_nat_mul]
      rfl
    _ = _ := by
      rw [← exp_add]
      congr 1
      push_cast
      field_simp

/-- The canonical-grid form has no root-of-unity premise left to discharge. -/
theorem twice_norm_le_standard {k : ℕ} {A : ℂ} {M : ℝ}
    (hk : 0 < k) (c : ℕ → ℂ)
    (hc0 : c 0 = A) (hcTop : c (2 * k) = (-1 : ℂ) ^ k * A)
    (hbound : ∀ j ∈ range (2 * k), ‖phaseSample k (standardRoot k) c j‖ ≤ M) :
    2 * ‖A‖ ≤ M :=
  twice_norm_le hk (standardRoot_primitive hk) c hc0 hcTop hbound

end

end ApproxDegree.PhaseAverage
end

-- CommonPhaseMatrix.lean
section
/-!
# Common-phase cancellation for matrices

The common phase assigns a logical matrix entry (a,b) the integer frequency
weight(b)-weight(a). This module connects low Hamming-distance support to
the alternating phase filter. The matrix coefficients are arbitrary, so
fixed sign factors and the normalization of the phase state can be absorbed
into them. No operator norm, commutator identity, or endpoint coefficient is
assumed by the cancellation results.
-/

open scoped BigOperators
open Finset Complex

namespace ApproxDegree.CommonPhaseMatrix

noncomputable section

/-- Every strictly interior integer frequency is killed by the signed grid. -/
theorem signed_sum_zpow_interior {k : ℕ} {ζ : ℂ} {l : ℤ}
    (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2 * k))
    (hlo : -(k : ℤ) < l) (hhi : l < (k : ℤ)) :
    (∑ j ∈ range (2 * k),
      (-1 : ℂ) ^ j * (I * ζ ^ j) ^ l) = 0 := by
  let r : ℕ := (l + k).toNat
  have hrZ : (r : ℤ) = l + k := Int.toNat_of_nonneg (by omega)
  have hr0 : 0 < r := by omega
  have hrN : r < 2 * k := by omega
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hterm (j : ℕ) :
      (-1 : ℂ) ^ j * (I * ζ ^ j) ^ l =
        (-I) ^ k * I ^ r * (ζ ^ j) ^ r := by
    have ht : I * ζ ^ j ≠ 0 := mul_ne_zero I_ne_zero (pow_ne_zero j hζ0)
    have hh : (ζ ^ j) ^ k = (-1 : ℂ) ^ j := by
      rw [← pow_mul, Nat.mul_comm j k, pow_mul,
        PhaseAverage.primitive_half_power hk hζ]
    have hI : ((I : ℂ) ^ k)⁻¹ = (-I) ^ k := by rw [← inv_pow, inv_I]
    have hl : l = (r : ℤ) - (k : ℤ) := by omega
    rw [hl, zpow_sub₀ ht, zpow_natCast, zpow_natCast, div_eq_mul_inv,
      mul_pow, mul_pow, hh, mul_inv_rev, hI]
    calc
      _ = ((-1 : ℂ) ^ j * ((-1 : ℂ) ^ j)⁻¹) *
          ((-I) ^ k * I ^ r * (ζ ^ j) ^ r) := by ring
      _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero j (by norm_num))]; ring
  simp_rw [hterm]
  rw [← mul_sum, PhaseAverage.root_sum_interior hζ hr0 hrN, mul_zero]

/-- A matrix phase sum with arbitrary fixed scalar coefficients. -/
def phaseSum {α : Type*} [Fintype α] (w : α → ℤ)
    (C : Matrix α α ℂ) (t : ℂ) : ℂ :=
  ∑ a, ∑ b, C a b * t ^ (w b - w a)

/-- The same equally spaced, signed average as in the manuscript. -/
def signedAverage (k : ℕ) (B : ℂ → ℂ) : ℂ :=
  (∑ j ∈ range (2 * k), (-1 : ℂ) ^ j *
    B (I * PhaseAverage.standardRoot k ^ j)) / ((2 * k : ℕ) : ℂ)

/-- An arbitrary matrix phase sum with only interior frequencies vanishes. -/
theorem signedAverage_phaseSum_eq_zero {α : Type*} [Fintype α]
    {k : ℕ} (hk : 0 < k) (w : α → ℤ) (C : Matrix α α ℂ)
    (hinterior : ∀ a b, C a b ≠ 0 →
      -(k : ℤ) < w b - w a ∧ w b - w a < (k : ℤ)) :
    signedAverage k (phaseSum w C) = 0 := by
  unfold signedAverage phaseSum
  simp_rw [mul_sum]
  rw [sum_comm]
  have hrow (a : α) :
      (∑ j ∈ range (2 * k), ∑ b,
        (-1 : ℂ) ^ j * (C a b *
          (I * PhaseAverage.standardRoot k ^ j) ^ (w b - w a))) = 0 := by
    rw [sum_comm]
    apply sum_eq_zero
    intro b hb
    by_cases hc : C a b = 0
    · simp [hc]
    · have hi := hinterior a b hc
      have hfactor :
          (∑ j ∈ range (2 * k), (-1 : ℂ) ^ j *
            (C a b * (I * PhaseAverage.standardRoot k ^ j) ^ (w b - w a))) =
          C a b * (∑ j ∈ range (2 * k), (-1 : ℂ) ^ j *
            (I * PhaseAverage.standardRoot k ^ j) ^ (w b - w a)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        ring
      rw [hfactor, signed_sum_zpow_interior hk
        (PhaseAverage.standardRoot_primitive hk) hi.1 hi.2, mul_zero]
  simp_rw [hrow]
  simp

/-- Number of one bits, viewed as an integer frequency. -/
def logicalWeight {ι : Type*} [Fintype ι] (a : ι → Bool) : ℤ :=
  ∑ i, if a i then 1 else 0

/-- The Hamming distance between logical labels. -/
def logicalDistance {ι : Type*} [Fintype ι] (a b : ι → Bool) : ℕ :=
  (univ.filter fun i => a i ≠ b i).card

/-- Weight difference is bounded by Hamming distance, for arbitrary labels. -/
theorem abs_weight_sub_le_distance {ι : Type*} [Fintype ι] (a b : ι → Bool) :
    |logicalWeight b - logicalWeight a| ≤ (logicalDistance a b : ℤ) := by
  unfold logicalWeight logicalDistance
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ i, |(if b i then (1 : ℤ) else 0) - (if a i then 1 else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, if a i ≠ b i then (1 : ℤ) else 0 := by
      apply sum_congr rfl
      intro i hi
      cases a i <;> cases b i <;> norm_num
    _ = _ := sum_boole _ _

/-- Low-distance support suffices for cancellation, including on raw point
spaces with more than one point per logical label. -/
theorem signedAverage_lowDistance {α ι : Type*} [Fintype α] [Fintype ι]
    {k : ℕ} (hk : 0 < k) (label : α → (ι → Bool)) (C : Matrix α α ℂ)
    (hsupport : ∀ a b, C a b ≠ 0 → logicalDistance (label a) (label b) < k) :
    signedAverage k (phaseSum (fun a => logicalWeight (label a)) C) = 0 := by
  apply signedAverage_phaseSum_eq_zero hk
  intro a b hc
  have hd : (logicalDistance (label a) (label b) : ℤ) < (k : ℤ) := by
    exact_mod_cast hsupport a b hc
  have hab := abs_weight_sub_le_distance (label a) (label b)
  have hab' := abs_le.mp hab
  omega

theorem phaseSum_sub {α : Type*} [Fintype α] (w : α → ℤ)
    (R S : Matrix α α ℂ) (t : ℂ) :
    phaseSum w (R - S) t = phaseSum w R t - phaseSum w S t := by
  simp only [phaseSum, Matrix.sub_apply, sub_mul, sum_sub_distrib]

theorem signedAverage_sub (k : ℕ) (A B : ℂ → ℂ) :
    signedAverage k (fun t => A t - B t) = signedAverage k A - signedAverage k B := by
  simp only [signedAverage, mul_sub, sum_sub_distrib, sub_div]

/-- The actual entry mask selecting logical distance exactly k. -/
def topDistancePart {α ι : Type*} [Fintype ι]
    (label : α → (ι → Bool)) (k : ℕ) (R : Matrix α α ℂ) : Matrix α α ℂ :=
  fun a b => if logicalDistance (label a) (label b) = k then R a b else 0

/-- On a matrix of logical bandwidth k, the signed phase average depends
only on its distance-k entries. No norm bound on the entry mask is used. -/
theorem signedAverage_eq_topDistancePart {α ι : Type*}
    [Fintype α] [Fintype ι] {k : ℕ} (hk : 0 < k)
    (label : α → (ι → Bool)) (R : Matrix α α ℂ)
    (hband : ∀ a b, k < logicalDistance (label a) (label b) → R a b = 0) :
    signedAverage k (phaseSum (fun a => logicalWeight (label a)) R) =
      signedAverage k (phaseSum (fun a => logicalWeight (label a))
        (topDistancePart label k R)) := by
  have hzero := signedAverage_lowDistance hk label (R - topDistancePart label k R)
    (by
      intro a b hc
      by_contra hn
      have hge : k ≤ logicalDistance (label a) (label b) := Nat.le_of_not_gt hn
      by_cases he : logicalDistance (label a) (label b) = k
      · simp [Matrix.sub_apply, topDistancePart, he] at hc
      · have hgt : k < logicalDistance (label a) (label b) := by omega
        simp [Matrix.sub_apply, topDistancePart, he, hband a b hgt] at hc)
  change signedAverage k (fun t => phaseSum (fun a => logicalWeight (label a))
    (R - topDistancePart label k R) t) = 0 at hzero
  simp_rw [phaseSum_sub] at hzero
  rw [signedAverage_sub] at hzero
  exact sub_eq_zero.mp hzero

end

end ApproxDegree.CommonPhaseMatrix
end


