-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0001
-- name    : PNT_ZeroFree_433_0001
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T11:58:21.800596+00:00
-- url     : https://prove2.me/theorems/81d40365-2082-4f8b-8b59-c1738c5566e6
-- title:
--   Zero-free region foundations: Arithmetic.EisensteinCoordinates [0001]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Arithmetic.EisensteinCoordinates
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinCoordinates.lean#L197-L735

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Multiset.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Geometry.Euclidean.Inversion.Calculus
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.PiLex
import Mathlib.Probability.Moments.Variance
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.PowerBasis
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.ProjIcc

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Arithmetic/EisensteinCoordinates.lean#L197-L735
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Arithmetic.EisensteinCoordinates
section
namespace OAI


open scoped BigOperators

namespace ShortDraft

theorem eisenstein_ring_pid :
    IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) := by
  let : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  exact IsCyclotomicExtension.Rat.three_pid (CyclotomicField 3 ℚ)

abbrev EisensteinCoordinates := ℤ × ℤ

def eisensteinMul (x y : EisensteinCoordinates) : EisensteinCoordinates :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1 - x.2 * y.2)

def eisensteinConj (x : EisensteinCoordinates) : EisensteinCoordinates :=
  (x.1 - x.2, -x.2)

def eisensteinNorm (x : EisensteinCoordinates) : ℤ :=
  x.1 ^ 2 - x.1 * x.2 + x.2 ^ 2

theorem eisenstein_norm_mul (x y : EisensteinCoordinates) :
    eisensteinNorm (eisensteinMul x y) = eisensteinNorm x * eisensteinNorm y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  dsimp [eisensteinNorm, eisensteinMul]
  ring

theorem eisenstein_norm_conj (x : EisensteinCoordinates) :
    eisensteinNorm (eisensteinConj x) = eisensteinNorm x := by
  rcases x with ⟨a, b⟩
  dsimp [eisensteinNorm, eisensteinConj]
  ring

theorem eisenstein_mul_conj (x : EisensteinCoordinates) :
    eisensteinMul x (eisensteinConj x) = (eisensteinNorm x, 0) := by
  rcases x with ⟨a, b⟩
  apply Prod.ext <;> dsimp [eisensteinNorm, eisensteinConj, eisensteinMul] <;> ring

theorem eisenstein_norm_nonneg (x : EisensteinCoordinates) :
    0 ≤ eisensteinNorm x := by
  rcases x with ⟨a, b⟩
  dsimp [eisensteinNorm]
  nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]

theorem eisenstein_norm_eq_zero_iff (x : EisensteinCoordinates) :
    eisensteinNorm x = 0 ↔ x = (0, 0) := by
  rcases x with ⟨a, b⟩
  dsimp [eisensteinNorm]
  constructor
  · intro h
    have hb : b = 0 := by
      nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
    have ha : a = 0 := by
      subst b
      nlinarith [sq_nonneg a]
    simp [ha, hb]
  · intro h
    simp_all

def DirichletTarget : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    (23 / 24 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) →
      DirichletCharacter.LFunction χ s ≠ 0

theorem dirichlet_target_of_one_le_re
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : 1 ≤ s.re) (hprincipal : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hprincipal) hs

theorem dirichletTarget_iff_open_strip :
    DirichletTarget ↔
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
        (23 / 24 : ℝ) < s.re → s.re < 1 →
          DirichletCharacter.LFunction χ s ≠ 0 := by
  constructor
  · intro h q _ χ s h23 _
    apply h q χ s h23
    intro ⟨_, hs⟩
    simp [hs] at *
  · intro h q _ χ s h23 hprincipal
    by_cases hs : s.re < 1
    · exact h q χ s h23 hs
    · exact dirichlet_target_of_one_le_re q χ s (le_of_not_gt hs) hprincipal

theorem cube_index_filter (b : ℕ) :
    (∑ h ∈ b.divisors, (ArithmeticFunction.moebius h : ℤ)) =
      if b = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f b)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  rw [ArithmeticFunction.one_apply] at h
  simpa using h

private lemma square_le_two_squares {x y e : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (he : 0 ≤ e) (h : x ≤ y + e) :
    x ^ 2 ≤ 2 * y ^ 2 + 2 * e ^ 2 := by
  have h₁ : 0 ≤ y + e - x := sub_nonneg.mpr h
  have h₂ : 0 ≤ y + e + x := by nlinarith
  have h₃ := mul_nonneg h₁ h₂
  have h₄ := sq_nonneg (y - e)
  nlinarith

theorem finite_row_extraction {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (a : α → ℝ) (a₀ error bound : ℝ)
    (ha₀ : 0 ≤ a₀) (ha : ∀ u, 0 ≤ a u) (herror : 0 ≤ error)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes, a₀ ≤ a (row p) + error)
    (hmean : (∑ u ∈ rows, (a u) ^ 2) ≤ bound) :
    (primes.card : ℝ) * a₀ ^ 2 ≤
      2 * bound + 2 * (primes.card : ℝ) * error ^ 2 := by
  have hselected : (∑ p ∈ primes, (a (row p)) ^ 2) ≤ bound := by
    calc
      (∑ p ∈ primes, (a (row p)) ^ 2) =
          ∑ u ∈ primes.image row, (a u) ^ 2 := by
            rw [Finset.sum_image hinj]
      _ ≤ ∑ u ∈ rows, (a u) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hrows (by
          intro u _ _
          positivity)
      _ ≤ bound := hmean
  have hpoint (p : β) (hp : p ∈ primes) :
      a₀ ^ 2 ≤ 2 * (a (row p)) ^ 2 + 2 * error ^ 2 :=
    square_le_two_squares ha₀ (ha _) herror (happrox p hp)
  have hsum :
      (∑ p ∈ primes, a₀ ^ 2) ≤
        ∑ p ∈ primes, (2 * (a (row p)) ^ 2 + 2 * error ^ 2) :=
    Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith

theorem complex_row_extraction {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (A : α → ℂ) (untwisted : α) (error bound : ℝ)
    (herror : 0 ≤ error)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes, ‖A untwisted - A (row p)‖ ≤ error)
    (hmean : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤ bound) :
    (primes.card : ℝ) * ‖A untwisted‖ ^ 2 ≤
      2 * bound + 2 * (primes.card : ℝ) * error ^ 2 := by
  apply finite_row_extraction rows primes row (fun u ↦ ‖A u‖)
    ‖A untwisted‖ error bound (norm_nonneg _) (fun u ↦ norm_nonneg _) herror
    hrows hinj ?_ hmean
  intro p hp
  calc
    ‖A untwisted‖ = ‖(A untwisted - A (row p)) + A (row p)‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖A untwisted - A (row p)‖ + ‖A (row p)‖ := norm_add_le _ _
    _ ≤ ‖A (row p)‖ + error := by linarith [happrox p hp]

theorem mean_square_exponent : (21 / 10 : ℚ) - 11 / 60 = 23 / 12 := by
  norm_num

theorem approximation_exponent : (2 : ℚ) - 11 / 30 = 49 / 30 := by
  norm_num

theorem zero_free_of_analytic_identity
    (σ : ℝ) (hσ : σ < 1) (L M W : ℂ → ℂ)
    (hL : AnalyticOnNhd ℂ L {s | σ < s.re})
    (hM : AnalyticOnNhd ℂ M {s | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s | σ < s.re})
    (heq : ∀ s : ℂ, 1 < s.re → L s * M s = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hWρ : W ρ ≠ 0) : L ρ ≠ 0 := by
  have hzeroIn : (2 : ℂ) ∈ {s : ℂ | σ < s.re} := by
    change σ < (2 : ℂ).re
    simpa using lt_trans hσ (show (1 : ℝ) < 2 by norm_num)
  have heventual : (fun s : ℂ => L s * M s) =ᶠ[nhds (2 : ℂ)] W := by
    filter_upwards [((Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (2 : ℂ) ∈
        {s : ℂ | 1 < s.re}))] with s hs
    exact heq s hs
  have hident : Set.EqOn (fun s : ℂ => L s * M s) W {s | σ < s.re} :=
    (hL.mul hM).eqOn_of_preconnected_of_eventuallyEq hW
      ((convex_halfSpace_re_gt σ).isPreconnected) hzeroIn heventual
  intro hLρ
  have hρeq := hident hρ
  change L ρ * M ρ = W ρ at hρeq
  rw [hLρ, zero_mul] at hρeq
  exact hWρ hρeq.symm

theorem zero_free_of_regularized_analytic_identity
    (σ : ℝ) (hσ : σ < 1) (L Lregular M W : ℂ → ℂ)
    (hLregular : AnalyticOnNhd ℂ Lregular {s | σ < s.re})
    (hM : AnalyticOnNhd ℂ M {s | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s | σ < s.re})
    (hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
      Lregular s = (s - 1) * L s)
    (heq : ∀ s : ℂ, 1 < s.re →
      Lregular s * M s = (s - 1) * W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : W ρ ≠ 0) : L ρ ≠ 0 := by
  have hWregular :
      AnalyticOnNhd ℂ (fun s : ℂ => (s - 1) * W s) {s | σ < s.re} :=
    (analyticOnNhd_id.sub analyticOnNhd_const).mul hW
  have hWregularρ : (ρ - 1) * W ρ ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hρone) hWρ
  have hLregularρ := zero_free_of_analytic_identity σ hσ Lregular M
    (fun s : ℂ => (s - 1) * W s) hLregular hM hWregular heq
    ρ hρ hWregularρ
  rw [hregular ρ hρ hρone] at hLregularρ
  exact (mul_ne_zero_iff.mp hLregularρ).2

theorem two_poisson_scale_substitution
    (K X F B L A C d t J Y g e ge v Li K' X' F' Δ : ℝ)
    (hK : K ≠ 0) (hB : B ≠ 0) (hF : F ≠ 0)
    (hA : A ≠ 0) (hC : C ≠ 0) (hd : d ≠ 0)
    (ht : t ≠ 0) (hJ : J ≠ 0) (he : e ≠ 0)
    (hge : ge ≠ 0) (hv : v ≠ 0) (hL0 : L ≠ 0)
    (hL : L = X / B ^ 3)
    (hLi : Li = L / (A * C * t))
    (hg : g = e * ge)
    (hY : Y = L ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J))
    (hK' : K' = d * e ^ 2 * Li ^ 2 / (Y * g ^ 2))
    (hX' : X' = Li / (g * v))
    (hF' : F' = J * C * e * v)
    (hΔ : Δ = B * F * A * t * ge) :
    K' = K * J / (Δ ^ 2 * B ^ 2) ∧
      X' * F' = X * F * J / (Δ * B ^ 2) := by
  constructor
  · rw [hK', hLi, hg, hY, hΔ]
    field_simp
  · rw [hX', hF', hLi, hL, hg, hΔ]
    field_simp

theorem two_poisson_budget
    (K X F R B J Δ K' childColumnMass R' : ℝ)
    (hK : 0 ≤ K) (hX : 0 < X) (hF : 0 < F)
    (hB : 0 < B) (hJpos : 0 < J) (hΔpos : 0 < Δ)
    (hJ : J ≤ B ^ 2) (hΔ : B * F ≤ Δ)
    (hK' : K' = K * J / (Δ ^ 2 * B ^ 2))
    (hM' : childColumnMass = X * F * J / (Δ * B ^ 2))
    (hR' : R' ≤ R * Δ) :
    K' * R' / childColumnMass ≤ K * R / (X * F) ∧
      K' ≤ K / (B * F) ^ 2 ∧
      childColumnMass ≤ X * F / (B * F) ∧
      (Δ * B ^ 2 / J) * childColumnMass = X * F := by
  have hB2 : 0 < B ^ 2 := sq_pos_of_pos hB
  have hBF : 0 < B * F := mul_pos hB hF
  have hXF : 0 < X * F := mul_pos hX hF
  have hMpos : 0 < childColumnMass := by rw [hM']; positivity
  have hK'nonneg : 0 ≤ K' := by rw [hK']; positivity
  constructor
  · have hstep : K' * R' ≤ K' * (R * Δ) :=
      mul_le_mul_of_nonneg_left hR' hK'nonneg
    apply (div_le_div_iff₀ hMpos hXF).2
    calc
      K' * R' * (X * F) ≤ K' * (R * Δ) * (X * F) := by
        gcongr
      _ = (K * R / (X * F)) * childColumnMass * (X * F) := by
        rw [hK', hM']
        field_simp
      _ = K * R * childColumnMass := by field_simp
  constructor
  · rw [hK']
    apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hΔpos) hB2)
      (sq_pos_of_pos hBF)).2
    have hΔ2 : (B * F) ^ 2 ≤ Δ ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hΔ)
        (show 0 ≤ Δ + B * F by positivity)]
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hJ),
      mul_nonneg (mul_nonneg hK (le_of_lt hB2)) (sub_nonneg.mpr hΔ2)]
  constructor
  · rw [hM']
    apply (div_le_div_iff₀ (mul_pos hΔpos hB2) hBF).2
    have hΔBF : B * F ≤ Δ := hΔ
    nlinarith [mul_nonneg (le_of_lt hXF) (sub_nonneg.mpr hJ),
      mul_nonneg (mul_nonneg (le_of_lt hXF) (le_of_lt hB2))
        (sub_nonneg.mpr hΔBF)]
  · rw [hM']
    field_simp

theorem two_poisson_charge
    (R R' b0 B F A t ge Δ : ℝ)
    (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hF : 1 ≤ F) (hA : 1 ≤ A)
    (ht : 0 ≤ t) (hge : 0 ≤ ge)
    (hb0B : b0 ≤ B)
    (hR' : R' ≤ R * b0 * t * ge)
    (hΔ : Δ = B * F * A * t * ge) : R' ≤ R * Δ := by
  calc
    R' ≤ R * b0 * t * ge := hR'
    _ ≤ R * B * t * ge := by gcongr
    _ ≤ R * (B * F * A * t * ge) := by
      have hBA : B ≤ B * F * A := by
        have hBF : B ≤ B * F := by nlinarith
        have hBFA : B * F ≤ B * F * A := by
          nlinarith [mul_nonneg (mul_nonneg hB (le_trans zero_le_one hF))
            (sub_nonneg.mpr hA)]
        exact hBF.trans hBFA
      nlinarith [mul_nonneg (mul_nonneg hR (sub_nonneg.mpr hBA))
        (mul_nonneg ht hge)]
    _ = R * Δ := by rw [hΔ]

theorem two_poisson_cost_identity
    (K A C d L B F c Y g e Li J t ge v X Δ : ℝ)
    (hK : K ≠ 0) (hC : C ≠ 0) (hd : d ≠ 0) (hL : L ≠ 0)
    (hB : B ≠ 0) (hF : F ≠ 0) (hc : 0 < c)
    (hg : g ≠ 0) (he : e ≠ 0) (hLi : Li ≠ 0)
    (hJ : J ≠ 0) (hv : v ≠ 0)
    (hY : Y = L ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J))
    (hM : X = Li / (g * v) * (J * C * e * v))
    (hΔ : Δ = B * F * A * t * ge) :
    (K * A * C / (d * L ^ 2 * B ^ 2 * F * Real.sqrt c)) *
      (Y * g / (e * Li)) *
      ((B * Real.sqrt c / J) * t * ge) * X = Δ * B ^ 2 / J := by
  have hcsqrt : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  rw [hY, hM, hΔ]
  field_simp

end ShortDraft

open MulChar AddChar

namespace ShortDraftLocal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem sextic_character_exponent (χ : MulChar F ℂ) (hχ : χ ^ 6 = 1) :
    χ⁻¹ * χ⁻¹ ^ 2 = χ ^ 3 := by
  calc
    χ⁻¹ * χ⁻¹ ^ 2 = χ ^ (-3 : ℤ) := by group
    _ = χ ^ 3 := by
      calc
        χ ^ (-3 : ℤ) = χ ^ ((-3 : ℤ) + 6) := by
          rw [zpow_add, zpow_ofNat, hχ, mul_one]
        _ = χ ^ 3 := by norm_num

theorem gaussSum_mulShift_any (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (a : F) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : a = 0
  · subst a
    have hshift : ψ.mulShift (0 : F) = 1 := by
      ext x
      simp
    rw [hshift, gaussSum_one_right hχ]
    simp
  · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
    simpa [hu.unit_spec] using gaussSum_mulShift_eq χ ψ hu.unit

theorem gaussSum_eq_units_sum (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    gaussSum χ ψ = ∑ y : Fˣ, χ (y : F) * ψ (y : F) := by
  classical
  have hzero : χ (0 : F) * ψ (0 : F) = 0 := by simp
  calc
    gaussSum χ ψ = ∑ x ∈ (Finset.univ : Finset F).erase 0, χ x * ψ x := by
      simpa only [gaussSum, hzero, add_zero] using
        (Finset.sum_erase_add (Finset.univ : Finset F)
          (fun x => χ x * ψ x) (Finset.mem_univ (0 : F))).symm
    _ = ∑ x : {x : F // x ≠ 0}, χ x * ψ x := by
      apply Finset.sum_subtype
      intro x
      simp
    _ = ∑ y : Fˣ, χ (y : F) * ψ (y : F) := by
      apply (Fintype.sum_equiv (unitsEquivNeZero : Fˣ ≃ {x : F // x ≠ 0})
        (fun y : Fˣ => χ (y : F) * ψ (y : F))
        (fun x : {x : F // x ≠ 0} => χ x * ψ x) ?_).symm
      intro y
      rfl

omit [Fintype F] [DecidableEq F] in
theorem sextic_character_quadratic (χ : MulChar F ℂ) (hχ : χ ^ 6 = 1) :
    (χ ^ 3)⁻¹ = χ ^ 3 := by
  calc
    (χ ^ 3)⁻¹ = χ ^ (-3 : ℤ) := by group
    _ = χ ^ 3 := by
      calc
        χ ^ (-3 : ℤ) = χ ^ ((-3 : ℤ) + 6) := by
          rw [zpow_add, zpow_ofNat, hχ, mul_one]
        _ = χ ^ 3 := by norm_num

theorem sextic_inversion_sum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (a : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) h * ψ (a * ((h⁻¹ : Fˣ) : F))) =
      ∑ y : Fˣ, (χ ^ 3) y * ψ (a * (y : F)) := by
  classical
  calc
    (∑ h : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) h * ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) (y⁻¹) * ψ (a * (y : F)) := by
          apply Fintype.sum_equiv (Equiv.inv Fˣ)
          intro y
          simp
    _ = ∑ y : Fˣ, (χ ^ 3) y * ψ (a * (y : F)) := by
      congr 1
      funext y
      rw [sextic_character_exponent χ hχ]
      have hy := sextic_character_quadratic χ hχ
      have hval : (χ ^ 3) ((y⁻¹ : Fˣ) : F) = (χ ^ 3) (y : F) := by
        calc
          (χ ^ 3) ((y⁻¹ : Fˣ) : F) = (χ ^ 3)⁻¹ (y : F) := by
            rw [MulChar.inv_apply', Units.val_inv_eq_inv_val]
          _ = (χ ^ 3) (y : F) := by rw [hy]
      rw [← Units.val_inv_eq_inv_val y, hval]

theorem sextic_inversion_gaussSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (a : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) h * ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum (χ ^ 3) (ψ.mulShift a) := by
  rw [sextic_inversion_sum χ ψ hχ a, gaussSum_eq_units_sum]
  simp only [AddChar.mulShift_apply]

theorem sextic_local_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (hχ₃ : χ ^ 3 ≠ 1) (ε x : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) h * ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 3) ε * gaussSum (χ ^ 3) ψ * (χ ^ 3) x := by
  rw [sextic_inversion_gaussSum χ ψ hχ (ε * x)]
  rw [gaussSum_mulShift_any (χ ^ 3) ψ hχ₃ (ε * x)]
  rw [sextic_character_quadratic χ hχ, map_mul]
  ring

theorem additive_unit_sum (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (a : F) :
    (∑ y : Fˣ, ψ (a * (y : F))) =
      if a = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  classical
  have hgauss : (∑ y : Fˣ, ψ (a * (y : F))) =
      gaussSum (1 : MulChar F ℂ) (ψ.mulShift a) := by
    rw [gaussSum_eq_units_sum]
    simp only [MulChar.one_apply_coe, one_mul, AddChar.mulShift_apply]
  rw [hgauss]
  split_ifs with ha
  · subst a
    simp only [AddChar.mulShift_zero, gaussSum_one_one]
    exact_mod_cast (Nat.card_eq_fintype_card (α := Fˣ))
  · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
    have hshift : ψ.mulShift a ≠ 1 := by
      intro heq
      exact hψ ((AddChar.mulShift_unit_eq_one_iff ψ hu).mp heq)
    exact gaussSum_one_left hshift

theorem sextic_fourth_mask (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (hψ : ψ ≠ 1) (a : F) :
    (∑ h : Fˣ, ((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) h *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      if a = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  classical
  have hexp : ((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) = 1 := by
    calc
      ((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) = (χ ^ 6)⁻¹ := by group
      _ = 1 := by rw [hχ, inv_one]
  rw [hexp]
  simp only [MulChar.one_apply_coe, one_mul]
  calc
    (∑ h : Fˣ, ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, ψ (a * (y : F)) := by
          apply Fintype.sum_equiv (Equiv.inv Fˣ)
          intro h
          simp
    _ = _ := additive_unit_sum ψ hψ a

theorem active_zero_local_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ₂ : χ ^ 2 ≠ 1) (ε x : F) :
    (∑ h : Fˣ, ((χ⁻¹) ^ 2) (h : F) *
      ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x := by
  classical
  have hquad : ((χ⁻¹) ^ 2)⁻¹ = χ ^ 2 := by group
  calc
    (∑ h : Fˣ, ((χ⁻¹) ^ 2) (h : F) *
      ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, (χ ^ 2) (y : F) * ψ ((ε * x) * (y : F)) := by
          apply Fintype.sum_equiv (Equiv.inv Fˣ)
          intro h
          simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val]
          rw [← hquad, MulChar.inv_apply', inv_inv]
    _ = gaussSum (χ ^ 2) (ψ.mulShift (ε * x)) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]
    _ = (χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x := by
      rw [gaussSum_mulShift_any (χ ^ 2) ψ hχ₂ (ε * x)]
      rw [map_mul]
      ring

theorem nontrivial_fourier_coefficient (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (h : F) :
    (∑ t : F, χ t * ψ (-(h * t))) =
      χ⁻¹ h * gaussSum χ (ψ.mulShift (-1)) := by
  calc
    (∑ t : F, χ t * ψ (-(h * t))) =
        gaussSum χ ((ψ.mulShift (-1)).mulShift h) := by
          simp only [gaussSum, AddChar.mulShift_apply]
          congr 1
          funext t
          congr 1
          ring_nf
    _ = χ⁻¹ h * gaussSum χ (ψ.mulShift (-1)) :=
      gaussSum_mulShift_any χ (ψ.mulShift (-1)) hχ h

theorem trivial_fourier_coefficient (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (h : F) :
    (∑ t : F, (1 : MulChar F ℂ) t * ψ (-(h * t))) =
      if h = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  calc
    (∑ t : F, (1 : MulChar F ℂ) t * ψ (-(h * t))) =
        gaussSum (1 : MulChar F ℂ) (ψ.mulShift (-h)) := by
          simp only [gaussSum, AddChar.mulShift_apply]
          congr 1
          funext t
          congr 1
          ring_nf
    _ = ∑ u : Fˣ, ψ ((-h) * (u : F)) := by
      rw [gaussSum_eq_units_sum]
      simp only [MulChar.one_apply_coe, one_mul, AddChar.mulShift_apply]
    _ = if h = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
      simpa only [neg_eq_zero] using additive_unit_sum ψ hψ (-h)

theorem sextic_fourier_theta_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (hχ₃ : χ ^ 3 ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      ((χ⁻¹) ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum (χ ^ 3) ψ * (χ ^ 3) ε) *
      (χ ^ 3) x := by
  classical
  have hχ₁ : χ ≠ 1 := by
    intro heq
    exact hχ₃ (by simp [heq])
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        ((χ⁻¹) ^ 2) σ * gaussSum χ (ψ.mulShift (-1)) *
          (∑ h : Fˣ,
            (χ⁻¹ * (χ⁻¹) ^ 2) h *
              ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [nontrivial_fourier_coefficient χ ψ hχ₁, map_mul]
    simp only [MulChar.mul_apply]
    ring
  rw [hsum, sextic_local_row χ ψ hχ hχ₃ ε x]
  ring

end ShortDraftLocal


end OAI

end


