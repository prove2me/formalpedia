-- Prove2me | Definitions.Def_ApproxDegCompV1_PolynomialBandwidth
-- name    : ApproxDegCompV1_PolynomialBandwidth
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-13T04:09:14.93132+00:00
-- url     : https://prove2.me/theorems/bf0b8f5c-662b-4b0d-bbbc-3ede138f1739
-- title:
--   Approximate-degree composition: Bandwidth of polynomial multiplication on product spaces
-- statement:
--   This module formalizes bandwidth of polynomial multiplication on product spaces for the Lean proof of the approximate-degree composition lower bound.
-- source:
--   https://prove2.me/theorems/f8385c32-068c-45a1-99ed-f7cf0a99f266

import Definitions.Def_ApproxDegCompV1_SpectralGrading
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

-- AffineApproximation.lean
section
/-!
# Degree-preserving affine changes between bit and sign polynomials

The substitution degree bound is proved from the actual monomial expansion.
Both output rescalings are explicit real multivariate polynomials.
-/

open scoped BigOperators
open Finset

namespace ApproxDegree.AffineApproximation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {σ τ X : Type*}

/-- Substituting affine polynomials cannot increase total degree. This is
proved directly from the finite monomial expansion of the input polynomial. -/
theorem totalDegree_affine_substitution (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ ℝ) :
    (MvPolynomial.eval₂ MvPolynomial.C f p).totalDegree ≤ p.totalDegree := by
  classical
  have hp : MvPolynomial.eval₂ MvPolynomial.C f p =
      ∑ s ∈ p.support, MvPolynomial.eval₂ MvPolynomial.C f
        (MvPolynomial.monomial s (MvPolynomial.coeff s p)) := by
    conv_lhs => rw [p.as_sum]
    rw [MvPolynomial.eval₂_sum]
  rw [hp]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  rw [MvPolynomial.eval₂_monomial]
  change (MvPolynomial.C (MvPolynomial.coeff s p) *
    ∏ i ∈ s.support, f i ^ s i).totalDegree ≤ p.totalDegree
  calc
    _ ≤ (MvPolynomial.C (MvPolynomial.coeff s p) : MvPolynomial τ ℝ).totalDegree +
        (∏ i ∈ s.support, f i ^ s i).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (∏ i ∈ s.support, f i ^ s i).totalDegree := by
      rw [MvPolynomial.totalDegree_C, zero_add]
    _ ≤ ∑ i ∈ s.support, (f i ^ s i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ s.support, s i := by
      apply sum_le_sum
      intro i hi
      exact (MvPolynomial.totalDegree_pow _ _).trans
        (by simpa using Nat.mul_le_mul_left (s i) (hf i))
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hs

def signVariable (i : σ) : MvPolynomial σ ℝ :=
  1 - MvPolynomial.C 2 * MvPolynomial.X i

theorem signVariable_totalDegree_le (i : σ) : (signVariable i).totalDegree ≤ 1 := by
  have hm : (MvPolynomial.C 2 * MvPolynomial.X i : MvPolynomial σ ℝ).totalDegree ≤ 1 := by
    simpa using MvPolynomial.totalDegree_mul
      (MvPolynomial.C (2 : ℝ)) (MvPolynomial.X i)
  exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (by simp) hm)

/-- Substitute the logical sign coordinates `X_i = 1 - 2 bit_i`. -/
def signSubstitution (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  MvPolynomial.eval₂ MvPolynomial.C signVariable p

theorem signSubstitution_totalDegree_le (p : MvPolynomial σ ℝ) :
    (signSubstitution p).totalDegree ≤ p.totalDegree :=
  totalDegree_affine_substitution signVariable signVariable_totalDegree_le p

theorem signSubstitution_eval (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    MvPolynomial.eval z (signSubstitution p) =
      MvPolynomial.eval (fun i => 1 - 2 * z i) p := by
  rw [signSubstitution, ← MvPolynomial.eval_assoc]
  have heval : (MvPolynomial.eval z) ∘ signVariable = (fun i => 1 - 2 * z i) := by
    funext i
    simp [signVariable]
  rw [heval]

theorem one_sub_two_bitValue (b : Bool) :
    1 - 2 * BooleanApproxDegree.bitValue b = FourierTruncation.realSign b := by
  cases b <;> norm_num [BooleanApproxDegree.bitValue, FourierTruncation.realSign]

theorem signSubstitution_eval_bits (p : MvPolynomial σ ℝ) (b : σ → Bool) :
    MvPolynomial.eval (fun i => BooleanApproxDegree.bitValue (b i)) (signSubstitution p) =
      MvPolynomial.eval (fun i => FourierTruncation.realSign (b i)) p := by
  rw [signSubstitution_eval]
  simp only [one_sub_two_bitValue]

/-- Positive-true sign output converted to bit output, after sign input substitution. -/
def positiveSignToBit (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  MvPolynomial.C (1 / 2) * (signSubstitution p + 1)

theorem positiveSignToBit_totalDegree_le (p : MvPolynomial σ ℝ) :
    (positiveSignToBit p).totalDegree ≤ p.totalDegree := by
  calc
    _ ≤ (MvPolynomial.C (1 / 2 : ℝ) : MvPolynomial σ ℝ).totalDegree +
        (signSubstitution p + 1).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (signSubstitution p + 1).totalDegree := by simp
    _ ≤ max (signSubstitution p).totalDegree (1 : MvPolynomial σ ℝ).totalDegree :=
      MvPolynomial.totalDegree_add _ _
    _ = (signSubstitution p).totalDegree := by simp
    _ ≤ p.totalDegree := signSubstitution_totalDegree_le p

theorem positiveSignToBit_eval (p : MvPolynomial σ ℝ) (b : σ → Bool) :
    MvPolynomial.eval (fun i => BooleanApproxDegree.bitValue (b i)) (positiveSignToBit p) =
      (MvPolynomial.eval (fun i => FourierTruncation.realSign (b i)) p + 1) / 2 := by
  simp only [positiveSignToBit, map_mul, MvPolynomial.eval_C, map_add, map_one,
    signSubstitution_eval_bits]
  ring

theorem positiveSign_error_identity (b : Bool) (t : ℝ) :
    |BooleanApproxDegree.bitValue b - (t + 1) / 2| =
      |(if b then (1 : ℝ) else -1) - t| / 2 := by
  have h : BooleanApproxDegree.bitValue b - (t + 1) / 2 =
      ((if b then (1 : ℝ) else -1) - t) / 2 := by
    cases b <;> simp only [BooleanApproxDegree.bitValue, Bool.false_eq_true, if_false, if_true] <;> ring
  rw [h, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Error strictly below `2/3` for a positive-true sign target yields bit
error strictly below `1/3`, with no increase of polynomial degree. -/
theorem positiveSignToBit_approximation (F : (σ → Bool) → Bool) (p : MvPolynomial σ ℝ)
    (happrox : ∀ b, |(if F b then (1 : ℝ) else -1) -
      MvPolynomial.eval (fun i => FourierTruncation.realSign (b i)) p| < 2 / 3) :
    (positiveSignToBit p).totalDegree ≤ p.totalDegree ∧
      ∀ b, |BooleanApproxDegree.bitValue (F b) -
        MvPolynomial.eval (fun i => BooleanApproxDegree.bitValue (b i))
          (positiveSignToBit p)| < 1 / 3 := by
  refine ⟨positiveSignToBit_totalDegree_le p, ?_⟩
  intro b
  rw [positiveSignToBit_eval, positiveSign_error_identity]
  linarith [happrox b]

/-- Negative-true sign output converted to bit output, without changing inputs. -/
def negativeSignToBit (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  MvPolynomial.C (1 / 2) * (1 - p)

theorem negativeSignToBit_totalDegree_le (p : MvPolynomial σ ℝ) :
    (negativeSignToBit p).totalDegree ≤ p.totalDegree := by
  calc
    _ ≤ (MvPolynomial.C (1 / 2 : ℝ) : MvPolynomial σ ℝ).totalDegree +
        (1 - p).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (1 - p).totalDegree := by simp
    _ ≤ max (1 : MvPolynomial σ ℝ).totalDegree p.totalDegree :=
      MvPolynomial.totalDegree_sub _ _
    _ = p.totalDegree := by simp

theorem negativeSignToBit_eval (p : MvPolynomial σ ℝ) (z : σ → ℝ) :
    MvPolynomial.eval z (negativeSignToBit p) = (1 - MvPolynomial.eval z p) / 2 := by
  simp only [negativeSignToBit, map_mul, MvPolynomial.eval_C, map_sub, map_one]
  ring

theorem negativeSign_error_identity (b : Bool) (t : ℝ) :
    |BooleanApproxDegree.bitValue b - (1 - t) / 2| =
      |(if b then (-1 : ℝ) else 1) - t| / 2 := by
  have h : BooleanApproxDegree.bitValue b - (1 - t) / 2 =
      -(((if b then (-1 : ℝ) else 1) - t) / 2) := by
    cases b <;> simp only [BooleanApproxDegree.bitValue, Bool.false_eq_true, if_false, if_true] <;> ring
  rw [h, abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Any inner sign approximant of error at most `2/3` gives a bit approximant
of error at most `1/3` on exactly the same point domain and coordinates. -/
theorem negativeSignToBit_approximation (coords : X → σ → ℝ) (g : X → Bool)
    (p : MvPolynomial σ ℝ)
    (happrox : ∀ x, |DegreeScaleWitness.signTarget g x -
      MvPolynomial.eval (coords x) p| ≤ 2 / 3) :
    (negativeSignToBit p).totalDegree ≤ p.totalDegree ∧
      ∀ x, |BooleanApproxDegree.bitValue (g x) -
        MvPolynomial.eval (coords x) (negativeSignToBit p)| ≤ 1 / 3 := by
  refine ⟨negativeSignToBit_totalDegree_le p, ?_⟩
  intro x
  rw [negativeSignToBit_eval, negativeSign_error_identity]
  have h := happrox x
  unfold DegreeScaleWitness.signTarget at h
  linarith

/-- The exact sign-nonapproximation premise of `DegreeScaleWitness` follows
from positive bit approximate degree at error `1/3`, by a proved affine map. -/
theorem inner_sign_nonapproximation (coords : X → σ → ℝ) (g : X → Bool)
    (hd : 0 < BooleanApproxDegree.approximateDegree coords
      (fun x => BooleanApproxDegree.bitValue (g x)) (1 / 3)) :
    ¬ ∃ p : MvPolynomial σ ℝ,
      p.totalDegree ≤ BooleanApproxDegree.approximateDegree coords
        (fun x => BooleanApproxDegree.bitValue (g x)) (1 / 3) - 1 ∧
      ∀ x, |DegreeScaleWitness.signTarget g x - MvPolynomial.eval (coords x) p| ≤ 2 / 3 := by
  rintro ⟨p, hdegree, happrox⟩
  obtain ⟨hdegree', happrox'⟩ := negativeSignToBit_approximation coords g p happrox
  exact BooleanApproxDegree.no_approximation_below_degree coords
    (fun x => BooleanApproxDegree.bitValue (g x)) (1 / 3) hd
      ⟨negativeSignToBit p, hdegree'.trans hdegree, happrox'⟩

end

end ApproxDegree.AffineApproximation
end

-- WeightedPolynomialAction.lean
section
/-!
# Actual multiplication on the weighted polynomial filtration

All operators act on EuclideanSpace with its Hilbert norm. Multiplication by
an actual real polynomial shifts the complex weighted polynomial span by at
most its total degree, and its adjoint is the same operator.
-/

open scoped BigOperators
open Finset

namespace ApproxDegree.WeightedPolynomialAction

noncomputable section

variable {X σ : Type*} [Fintype X] [DecidableEq X]

def pointMultiplier (p : X → ℂ) : EuclideanSpace ℂ X →L[ℂ] EuclideanSpace ℂ X :=
  (Matrix.toEuclideanLin (Matrix.diagonal p)).toContinuousLinearMap

theorem pointMultiplier_apply (p : X → ℂ) (v : EuclideanSpace ℂ X) (x : X) :
    pointMultiplier p v x = p x * v x := by
  change Matrix.mulVec (Matrix.diagonal p) (fun y => v y) x = _
  exact Matrix.mulVec_diagonal _ _ x

theorem pointMultiplier_norm_le (p : X → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ x, ‖p x‖ ≤ M) (v : EuclideanSpace ℂ X) :
    ‖pointMultiplier p v‖ ≤ M * ‖v‖ := by
  have hs : ‖pointMultiplier p v‖ ^ 2 ≤ M ^ 2 * ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, mul_sum]
    apply sum_le_sum
    intro x hx
    rw [pointMultiplier_apply, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hp x) 2)
      (sq_nonneg _)
  have hprod : 0 ≤ M * ‖v‖ := mul_nonneg hM (norm_nonneg v)
  have hs' : ‖pointMultiplier p v‖ ^ 2 ≤ (M * ‖v‖) ^ 2 := by
    simpa only [mul_pow] using hs
  exact (sq_le_sq₀ (norm_nonneg _) hprod).mp hs'

/-- A pointwise bound controls the genuine Hilbert operator norm. -/
theorem pointMultiplier_opNorm_le (p : X → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ x, ‖p x‖ ≤ M) : ‖pointMultiplier p‖ ≤ M :=
  (pointMultiplier p).opNorm_le_bound hM (pointMultiplier_norm_le p M hM hp)

theorem pointMultiplier_real_isSelfAdjoint (p : X → ℝ) :
    IsSelfAdjoint (pointMultiplier (fun x => (p x : ℂ))) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro x
  simp [IsSelfAdjoint]

def polynomialMultiplier (coords : X → σ → ℝ) (p : MvPolynomial σ ℝ) :
    EuclideanSpace ℂ X →L[ℂ] EuclideanSpace ℂ X :=
  pointMultiplier fun x => (MvPolynomial.eval (coords x) p : ℂ)

theorem polynomialMultiplier_weightedPolynomial (ψ : X → ℝ) (coords : X → σ → ℝ)
    (p q : MvPolynomial σ ℝ) :
    polynomialMultiplier coords p (WeightedDualVectors.weightedPolynomial ψ coords q) =
      WeightedDualVectors.weightedPolynomial ψ coords (p * q) := by
  ext x
  simp only [polynomialMultiplier, pointMultiplier_apply,
    WeightedDualVectors.weightedPolynomial, WeightedDualVectors.weightedPoint,
    PiLp.toLp_apply, MvPolynomial.eval_mul, Complex.ofReal_mul]
  ring

/-- Multiplication shifts the actual weighted polynomial span by at most the
multiplier's total degree. Complex linear combinations are covered. -/
theorem polynomialMultiplier_maps_degree_space (ψ : X → ℝ) (coords : X → σ → ℝ)
    (p : MvPolynomial σ ℝ) (q r : ℕ) (hp : p.totalDegree ≤ r) :
    ∀ v ∈ WeightedDualVectors.polynomialSpace ψ coords q,
      polynomialMultiplier coords p v ∈ WeightedDualVectors.polynomialSpace ψ coords (q + r) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨t, ht, rfl⟩ := hv
      rw [polynomialMultiplier_weightedPolynomial]
      apply Submodule.subset_span
      refine ⟨p * t, ?_, rfl⟩
      exact (MvPolynomial.totalDegree_mul p t).trans (by omega)
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact (WeightedDualVectors.polynomialSpace ψ coords (q + r)).add_mem ihx ihy
  | smul a x hx ih =>
      rw [map_smul]
      exact (WeightedDualVectors.polynomialSpace ψ coords (q + r)).smul_mem a ih

theorem polynomialMultiplier_isSelfAdjoint (coords : X → σ → ℝ)
    (p : MvPolynomial σ ℝ) : IsSelfAdjoint (polynomialMultiplier coords p) :=
  pointMultiplier_real_isSelfAdjoint _

end

end ApproxDegree.WeightedPolynomialAction
end

-- FiltrationBandwidth.lean
section
/-!
# Spectral levels and bandwidth of the actual projection generator

An increasing flag is capped by the full Hilbert space at depth `d`. Differences
of consecutive orthogonal projections give its actual spectral levels.
-/

namespace ApproxDegree.FiltrationBandwidth

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]

/-- Cap a flag at the full space, without changing any degree below `d`. -/
def cappedSpace (d : ℕ) (V : ℕ → Submodule ℂ E) (j : ℕ) : Submodule ℂ E :=
  if j < d then V j else ⊤

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
theorem cappedSpace_monotone (d : ℕ) (V : ℕ → Submodule ℂ E) (hV : Monotone V) :
    Monotone (cappedSpace d V) := by
  intro a b hab
  by_cases hb : b < d
  · have ha : a < d := lt_of_le_of_lt hab hb
    simpa only [cappedSpace, if_pos ha, if_pos hb] using hV hab
  · simp only [cappedSpace, if_neg hb, le_top]

/-- Endomorphism-valued orthogonal projection onto a capped degree space. -/
noncomputable def flagProjection (d : ℕ) (V : ℕ → Submodule ℂ E) (j : ℕ) :
    E →L[ℂ] E := (cappedSpace d V j).starProjection

/-- The actual level projections, including the bottom level. -/
noncomputable def levelProjection (d : ℕ) (V : ℕ → Submodule ℂ E) : ℕ → E →L[ℂ] E
  | 0 => flagProjection d V 0
  | j + 1 => flagProjection d V (j + 1) - flagProjection d V j

theorem levelProjection_isSelfAdjoint (d : ℕ) (V : ℕ → Submodule ℂ E) (j : ℕ) :
    IsSelfAdjoint (levelProjection d V j) := by
  cases j with
  | zero => exact isSelfAdjoint_starProjection _
  | succ j => exact (isSelfAdjoint_starProjection _).sub (isSelfAdjoint_starProjection _)

omit [CompleteSpace E] in
theorem flagProjection_low_high (d : ℕ) (V : ℕ → Submodule ℂ E)
    (hV : Monotone V) {a b : ℕ} (hab : a ≤ b) (x : E) :
    flagProjection d V a (flagProjection d V b x) = flagProjection d V a x := by
  exact congrArg (fun T : E →L[ℂ] E => T x)
    (Submodule.starProjection_comp_starProjection_of_le (cappedSpace_monotone d V hV hab))

omit [CompleteSpace E] in
theorem levelProjection_mem (d : ℕ) (V : ℕ → Submodule ℂ E)
    (hV : Monotone V) (j : ℕ) (x : E) :
    levelProjection d V j x ∈ cappedSpace d V j := by
  cases j with
  | zero => exact (cappedSpace d V 0).starProjection_apply_mem x
  | succ j =>
      apply (cappedSpace d V (j + 1)).sub_mem
      · exact (cappedSpace d V (j + 1)).starProjection_apply_mem x
      · exact cappedSpace_monotone d V hV (Nat.le_succ j)
          ((cappedSpace d V j).starProjection_apply_mem x)

omit [CompleteSpace E] in
theorem flagProjection_level_of_lt (d : ℕ) (V : ℕ → Submodule ℂ E)
    (hV : Monotone V) {a b : ℕ} (hab : a < b) (x : E) :
    flagProjection d V a (levelProjection d V b x) = 0 := by
  cases b with
  | zero => omega
  | succ b =>
      change flagProjection d V a
        (flagProjection d V (b + 1) x - flagProjection d V b x) = 0
      rw [map_sub, flagProjection_low_high d V hV (by omega),
        flagProjection_low_high d V hV (by omega), sub_self]

omit [CompleteSpace E] in
theorem flagProjection_level_of_le (d : ℕ) (V : ℕ → Submodule ℂ E)
    (hV : Monotone V) {a b : ℕ} (hab : b ≤ a) (x : E) :
    flagProjection d V a (levelProjection d V b x) = levelProjection d V b x := by
  exact (cappedSpace d V a).starProjection_eq_self_iff.mpr
    (cappedSpace_monotone d V hV hab (levelProjection_mem d V hV b x))

omit [CompleteSpace E] in
theorem levelProjection_kills_lower (d : ℕ) (V : ℕ → Submodule ℂ E)
    (hV : Monotone V) {a b : ℕ} (hab : b < a) (x : E)
    (hx : x ∈ cappedSpace d V b) : levelProjection d V a x = 0 := by
  cases a with
  | zero => omega
  | succ a =>
      have h₁ : flagProjection d V (a + 1) x = x :=
        (cappedSpace d V (a + 1)).starProjection_eq_self_iff.mpr
          (cappedSpace_monotone d V hV (by omega) hx)
      have h₀ : flagProjection d V a x = x :=
        (cappedSpace d V a).starProjection_eq_self_iff.mpr
          (cappedSpace_monotone d V hV (by omega) hx)
      change flagProjection d V (a + 1) x - flagProjection d V a x = 0
      rw [h₁, h₀, sub_self]

omit [CompleteSpace E] in
theorem sum_levelProjection (d : ℕ) (V : ℕ → Submodule ℂ E) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), levelProjection d V j = flagProjection d V n := by
  induction n with
  | zero => simp [levelProjection]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [levelProjection]
      abel

omit [CompleteSpace E] in
/-- Every vector decomposes into the actual `d+1` spectral levels. -/
theorem sum_levelProjection_eq_one (d : ℕ) (V : ℕ → Submodule ℂ E) :
    ∑ j ∈ Finset.range (d + 1), levelProjection d V j = 1 := by
  rw [sum_levelProjection]
  simp [flagProjection, cappedSpace, Submodule.starProjection_top']

omit [CompleteSpace E] in
theorem levelProjection_mul_eq_zero_of_gt (d : ℕ) (V : ℕ → Submodule ℂ E)
    (hV : Monotone V) {a b : ℕ} (hab : b < a) :
    levelProjection d V a * levelProjection d V b = 0 := by
  ext x
  exact levelProjection_kills_lower d V hV hab _ (levelProjection_mem d V hV b x)

theorem levelProjection_mul_eq_zero (d : ℕ) (V : ℕ → Submodule ℂ E)
    (hV : Monotone V) {a b : ℕ} (hab : a ≠ b) :
    levelProjection d V a * levelProjection d V b = 0 := by
  rcases lt_or_gt_of_ne hab with hab | hab
  · have h := congrArg star (levelProjection_mul_eq_zero_of_gt d V hV hab)
    simpa only [star_mul, (levelProjection_isSelfAdjoint d V a).star_eq,
      (levelProjection_isSelfAdjoint d V b).star_eq, star_zero] using h
  · exact levelProjection_mul_eq_zero_of_gt d V hV hab

omit [CompleteSpace E] in
theorem levelProjection_idempotent (d : ℕ) (V : ℕ → Submodule ℂ E)
    (hV : Monotone V) (j : ℕ) :
    levelProjection d V j * levelProjection d V j = levelProjection d V j := by
  ext x
  cases j with
  | zero => exact flagProjection_level_of_le d V hV le_rfl x
  | succ j =>
      change flagProjection d V (j + 1) (levelProjection d V (j + 1) x) -
        flagProjection d V j (levelProjection d V (j + 1) x) =
          levelProjection d V (j + 1) x
      rw [flagProjection_level_of_le d V hV le_rfl,
        flagProjection_level_of_lt d V hV (Nat.lt_succ_self j), sub_zero]

omit [CompleteSpace E] [FiniteDimensional ℂ E] [InnerProductSpace ℂ E] in
theorem sum_range_threshold (n k : ℕ) (y : E) :
    ∑ j ∈ Finset.range n, (if k ≤ j then y else 0) = (n - k) • y := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hkn : k ≤ n
      · simp [hkn, Nat.succ_sub hkn, succ_nsmul, add_comm]
      · have hn : n ≤ k := by omega
        have hns : n + 1 ≤ k := by omega
        simp [hkn, Nat.sub_eq_zero_of_le hn, Nat.sub_eq_zero_of_le hns]

omit [CompleteSpace E] in
/-- The explicitly defined generator acts at integer eigenvalue `k` on the
actual level projection. This is not an assumed spectral decomposition. -/
theorem generator_level_apply (d : ℕ) (V : ℕ → Submodule ℂ E)
    (hV : Monotone V) {k : ℕ} (hk : k ≤ d) (x : E) :
    FiltrationOperator.generator d (fun j => V j)
      (levelProjection d V k x) = (k : ℝ) • levelProjection d V k x := by
  have hp (j : Fin d) : (V j).starProjection (levelProjection d V k x) =
      if k ≤ j.val then levelProjection d V k x else 0 := by
    have hj : flagProjection d V j.val = (V j).starProjection := by
      simp only [flagProjection, cappedSpace, if_pos j.isLt]
    rw [← hj]
    split_ifs with hkj
    · exact flagProjection_level_of_le d V hV hkj x
    · exact flagProjection_level_of_lt d V hV (by omega) x
  simp only [FiltrationOperator.generator, sub_apply, smul_apply, one_apply_eq_self, sum_apply]
  simp_rw [hp]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => if k ≤ j then levelProjection d V k x else 0) d, sum_range_threshold]
  simp only [Nat.cast_smul_eq_nsmul]
  apply sub_eq_iff_eq_add.mpr
  rw [← add_nsmul]
  congr 1
  omega

omit [CompleteSpace E] in
theorem generator_mul_level (d : ℕ) (V : ℕ → Submodule ℂ E)
    (hV : Monotone V) {k : ℕ} (hk : k ≤ d) :
    FiltrationOperator.generator d (fun j => V j) * levelProjection d V k =
      (k : ℝ) • levelProjection d V k := by
  ext x
  exact generator_level_apply d V hV hk x

omit [CompleteSpace E] in
/-- Exact spectral expansion of the concrete generator. -/
theorem generator_eq_sum_levels (d : ℕ) (V : ℕ → Submodule ℂ E)
    (hV : Monotone V) :
    FiltrationOperator.generator d (fun j => V j) =
      ∑ k ∈ Finset.range (d + 1), (k : ℝ) • levelProjection d V k := by
  calc
    FiltrationOperator.generator d (fun j => V j) =
        FiltrationOperator.generator d (fun j => V j) * 1 := (mul_one _).symm
    _ = FiltrationOperator.generator d (fun j => V j) *
        ∑ k ∈ Finset.range (d + 1), levelProjection d V k := by
          rw [sum_levelProjection_eq_one]
    _ = ∑ k ∈ Finset.range (d + 1),
        FiltrationOperator.generator d (fun j => V j) * levelProjection d V k :=
          Finset.mul_sum _ _ _
    _ = _ := Finset.sum_congr rfl fun k hk =>
      generator_mul_level d V hV (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)

omit [CompleteSpace E] in
/-- A genuine degree-space growth property forces upper spectral bandwidth. -/
theorem level_block_zero_upper (d : ℕ) (V : ℕ → Submodule ℂ E)
    (hV : Monotone V) (B : E →L[ℂ] E) (r : ℕ)
    (hB : ∀ q x, x ∈ V q → B x ∈ V (q + r))
    {a b : ℕ} (ha : a ≤ d) (hab : b + r < a) :
    levelProjection d V a * B * levelProjection d V b = 0 := by
  have hb : b < d := by omega
  have hbr : b + r < d := by omega
  ext x
  change levelProjection d V a (B (levelProjection d V b x)) = 0
  apply levelProjection_kills_lower d V hV hab
  have hx := levelProjection_mem d V hV b x
  simp only [cappedSpace, if_pos hb] at hx
  simpa only [cappedSpace, if_pos hbr] using hB b _ hx

/-- Self-adjointness supplies the opposite bandwidth direction, by adjoints
of the already-proved upper-band identity. -/
theorem level_block_zero_lower (d : ℕ) (V : ℕ → Submodule ℂ E)
    (hV : Monotone V) (B : E →L[ℂ] E) (hBsa : IsSelfAdjoint B) (r : ℕ)
    (hB : ∀ q x, x ∈ V q → B x ∈ V (q + r))
    {a b : ℕ} (hb : b ≤ d) (hab : a + r < b) :
    levelProjection d V a * B * levelProjection d V b = 0 := by
  have h := congrArg star (level_block_zero_upper d V hV B r hB hb hab)
  simpa only [star_mul, (levelProjection_isSelfAdjoint d V a).star_eq,
    (levelProjection_isSelfAdjoint d V b).star_eq, hBsa.star_eq, star_zero,
    mul_assoc] using h

/-- Exact two-sided spectral bandwidth for the actual generator's levels.
The separated-level condition is equivalent to `|a-b| > r` for naturals. -/
theorem level_block_zero_of_separated (d : ℕ) (V : ℕ → Submodule ℂ E)
    (hV : Monotone V) (B : E →L[ℂ] E) (hBsa : IsSelfAdjoint B) (r : ℕ)
    (hB : ∀ q x, x ∈ V q → B x ∈ V (q + r))
    {a b : ℕ} (ha : a ≤ d) (hb : b ≤ d) (hab : a + r < b ∨ b + r < a) :
    levelProjection d V a * B * levelProjection d V b = 0 := by
  rcases hab with hab | hab
  · exact level_block_zero_lower d V hV B hBsa r hB hb hab
  · exact level_block_zero_upper d V hV B r hB ha hab

/-- Integer-distance form of the exact spectral bandwidth statement. -/
theorem level_block_zero_of_int_distance (d : ℕ) (V : ℕ → Submodule ℂ E)
    (hV : Monotone V) (B : E →L[ℂ] E) (hBsa : IsSelfAdjoint B) (r : ℕ)
    (hB : ∀ q x, x ∈ V q → B x ∈ V (q + r))
    {a b : ℕ} (ha : a ≤ d) (hb : b ≤ d)
    (hgap : (r : ℤ) < |(a : ℤ) - (b : ℤ)|) :
    levelProjection d V a * B * levelProjection d V b = 0 := by
  apply level_block_zero_of_separated d V hV B hBsa r hB ha hb
  by_cases hab : a ≤ b
  · left
    have hz : (a : ℤ) - (b : ℤ) ≤ 0 := by omega
    rw [abs_of_nonpos hz] at hgap
    omega
  · right
    have hz : 0 ≤ (a : ℤ) - (b : ℤ) := by omega
    rw [abs_of_nonneg hz] at hgap
    omega

/-- Fully instantiated single-block bandwidth for an actual real polynomial
on the actual weighted polynomial filtration.  The growth and adjoint
properties are discharged by `WeightedPolynomialAction`, not supplied here. -/
theorem polynomialMultiplier_level_bandwidth
    {X σ : Type*} [Fintype X] [DecidableEq X]
    (d : ℕ) (ψ : X → ℝ) (coords : X → σ → ℝ)
    (p : MvPolynomial σ ℝ) (r : ℕ) (hp : p.totalDegree ≤ r)
    (a b : Fin (d + 1)) (hgap : (r : ℤ) < |(a.val : ℤ) - (b.val : ℤ)|) :
    levelProjection d (WeightedDualVectors.polynomialSpace ψ coords) a.val *
      WeightedPolynomialAction.polynomialMultiplier coords p *
      levelProjection d (WeightedDualVectors.polynomialSpace ψ coords) b.val = 0 := by
  apply level_block_zero_of_int_distance d
    (WeightedDualVectors.polynomialSpace ψ coords)
    (fun _ _ hqr => WeightedDualVectors.polynomialSpace_mono ψ coords hqr)
    (WeightedPolynomialAction.polynomialMultiplier coords p)
    (WeightedPolynomialAction.polynomialMultiplier_isSelfAdjoint coords p) r
    (fun q => WeightedPolynomialAction.polynomialMultiplier_maps_degree_space
      ψ coords p q r hp)
    (Nat.le_of_lt_succ a.isLt) (Nat.le_of_lt_succ b.isLt) hgap

end ApproxDegree.FiltrationBandwidth
end

-- FiberIntertwining.lean
section
/-!
# Tensorization of the actual one-block exchange equations

The rectangular product matrices are those constructed in `FiberChannel`.
Their coordinate intertwinings are derived from the one-block exchange
equations, with no tensor intertwining or projection compatibility hypothesis.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace ApproxDegree.FiberIntertwining

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {ι X Y Z : Type*} [Fintype ι] [DecidableEq ι]

/-- A rectangular finite tensor product, given by its actual entries. -/
def tensorRect (A : ι → Matrix X Y ℂ) : Matrix (ι → X) (ι → Y) ℂ :=
  fun a b => ∏ i, A i (a i) (b i)

/-- Rectangular tensor multiplication is the finite product-of-sums identity. -/
theorem tensorRect_mul [Fintype Y] (A : ι → Matrix X Y ℂ)
    (B : ι → Matrix Y Z ℂ) :
    tensorRect A * tensorRect B = tensorRect (fun i => A i * B i) := by
  ext a b
  change (∑ x : ι → Y, (∏ i, A i (a i) (x i)) * (∏ i, B i (x i) (b i))) =
    ∏ i, ∑ x : Y, A i (a i) x * B i x (b i)
  simp_rw [← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => A i (a i) x * B i x (b i))).symm

/-- The concrete coordinate lift is the tensor with identities elsewhere. -/
theorem localLift_eq_tensorRect [Fintype Y] [DecidableEq Y]
    (L : Matrix Y Y ℂ) (i : ι) :
    OperatorGrading.localLift L i = tensorRect (fun j => if j = i then L else 1) := by
  ext a b
  unfold tensorRect
  rw [← mul_prod_erase univ
    (fun j => (if j = i then L else 1) (a j) (b j)) (mem_univ i)]
  simp only
  have hp : (∏ j ∈ univ.erase i, (if j = i then L else 1) (a j) (b j)) =
      if ∀ j, j ≠ i → a j = b j then (1 : ℂ) else 0 := by
    calc
      _ = ∏ j ∈ univ.erase i, if a j = b j then (1 : ℂ) else 0 := by
        apply prod_congr rfl
        intro j hj
        simp only [if_neg (mem_erase.mp hj).1, Matrix.one_apply]
      _ = _ := by simp only [prod_boole, mem_erase, mem_univ, and_true]
  rw [hp]
  by_cases h : ∀ j, j ≠ i → a j = b j <;> simp [OperatorGrading.localLift, h]

/-- Any one-block rectangular intertwining tensorizes to each coordinate. -/
theorem tensorize_intertwining [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (L : Matrix X X ℂ) (U : Matrix X Y ℂ) (B : Matrix Y Y ℂ)
    (h : L * U = U * B) (i : ι) :
    OperatorGrading.localLift L i * tensorRect (fun _ : ι => U) =
      tensorRect (fun _ : ι => U) * OperatorGrading.localLift B i := by
  rw [localLift_eq_tensorRect, localLift_eq_tensorRect, tensorRect_mul, tensorRect_mul]
  congr 1
  funext j
  by_cases hji : j = i
  · simp only [if_pos hji, h]
  · simp only [if_neg hji, Matrix.one_mul, Matrix.mul_one]

/-- The Boolean coordinate lift agrees with the Pauli tensor convention. -/
theorem localLift_pauliX (i : ι) :
    OperatorGrading.localLift TensorPhase.pauliX i = TensorPhase.localX i := by
  rw [localLift_eq_tensorRect]
  rfl

/-- A scalar on the single active coordinate remains a single scalar globally. -/
theorem localLift_smul [Fintype Y] [DecidableEq Y]
    (c : ℂ) (L : Matrix Y Y ℂ) (i : ι) :
    OperatorGrading.localLift (c • L) i = c • OperatorGrading.localLift L i := by
  ext a b
  by_cases h : ∀ j, j ≠ i → a j = b j <;> simp [OperatorGrading.localLift, h]

variable [Fintype Y] [DecidableEq Y]

/-- The one-block column matrix associated to the actual two vectors. -/
def oneBlockV (u : Bool → Y → ℂ) : Matrix Y Bool ℂ := fun y b => u b y

omit [DecidableEq Y] in
/-- The two exchange equations give the actual one-block matrix intertwining. -/
theorem oneBlock_exchange (L : Matrix Y Y ℂ) (u : Bool → Y → ℂ) (κ : ℂ)
    (hexchange : ∀ b x, ∑ y, L x y * u b y = κ * u (!b) x) :
    L * oneBlockV u = oneBlockV u * (κ • TensorPhase.pauliX) := by
  ext x b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  change (∑ y, L x y * u b y) = _
  rw [hexchange]
  cases b <;> simp [oneBlockV, TensorPhase.pauliX, mul_comm]

/-- Right exchange for the constructed product embedding. Neither support nor
normalization is needed for this algebraic identity. -/
theorem productV_right (L : Matrix Y Y ℂ) (u : Bool → Y → ℂ) (κ : ℂ)
    (hexchange : ∀ b x, ∑ y, L x y * u b y = κ * u (!b) x) (i : ι) :
    OperatorGrading.localLift L i * FiberChannel.productV u =
      FiberChannel.productV u * (κ • TensorPhase.localX i) := by
  have h := tensorize_intertwining L (oneBlockV u) (κ • TensorPhase.pauliX)
    (oneBlock_exchange L u κ hexchange) i
  rw [localLift_smul, localLift_pauliX] at h
  exact h

omit [Fintype Y] in
/-- Conjugate transpose commutes with the concrete coordinate lift. -/
theorem localLift_conjTranspose (L : Matrix Y Y ℂ) (i : ι) :
    Matrix.conjTranspose (OperatorGrading.localLift L i) =
      OperatorGrading.localLift (Matrix.conjTranspose L) i := by
  ext a b
  have hs : (∀ j, j ≠ i → b j = a j) ↔ (∀ j, j ≠ i → a j = b j) := by
    constructor <;> intro h j hj <;> exact (h j hj).symm
  change star (if ∀ j, j ≠ i → b j = a j then L (b i) (a i) else 0) =
    if ∀ j, j ≠ i → a j = b j then star (L (b i) (a i)) else 0
  by_cases h : ∀ j, j ≠ i → a j = b j
  · rw [if_pos h, if_pos (hs.mpr h)]
  · have h' : ¬ ∀ j, j ≠ i → b j = a j := fun h' => h (hs.mp h')
    rw [if_neg h, if_neg h', star_zero]

omit [Fintype Y] in
/-- A Hermitian one-block matrix has Hermitian coordinate lifts. -/
theorem localLift_isHermitian (L : Matrix Y Y ℂ) (hL : L.IsHermitian) (i : ι) :
    (OperatorGrading.localLift L i).IsHermitian := by
  change Matrix.conjTranspose (OperatorGrading.localLift L i) = _
  rw [localLift_conjTranspose, hL.eq]

omit [Fintype Y] [DecidableEq Y] in
theorem pauliX_isHermitian : TensorPhase.pauliX.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  cases a <;> cases b <;> simp [TensorPhase.pauliX]

omit [Fintype Y] [DecidableEq Y] in
theorem localX_isHermitian (i : ι) : (TensorPhase.localX i).IsHermitian := by
  rw [← localLift_pauliX]
  exact localLift_isHermitian _ pauliX_isHermitian i

/-- Left exchange for the actual adjoint product embedding, obtained by taking
adjoints of the proved right exchange and using a real exchange scalar. -/
theorem productW_left (L : Matrix Y Y ℂ) (hL : L.IsHermitian)
    (u : Bool → Y → ℂ) (κ : ℝ)
    (hexchange : ∀ b x, ∑ y, L x y * u b y = (κ : ℂ) * u (!b) x) (i : ι) :
    FiberChannel.productW u * OperatorGrading.localLift L i =
      ((κ : ℂ) • TensorPhase.localX i) * FiberChannel.productW u := by
  have h := congrArg Matrix.conjTranspose (productV_right L u (κ : ℂ) hexchange i)
  simpa only [FiberChannel.productW, Matrix.conjTranspose_mul, Matrix.conjTranspose_smul,
    (localLift_isHermitian L hL i).eq, (localX_isHermitian i).eq,
    Complex.star_def, Complex.conj_ofReal] using h

/-- Equivalent scalar-outside-product convention for right exchange. -/
theorem productV_right_smul (L : Matrix Y Y ℂ) (u : Bool → Y → ℂ) (κ : ℂ)
    (hexchange : ∀ b x, ∑ y, L x y * u b y = κ * u (!b) x) (i : ι) :
    OperatorGrading.localLift L i * FiberChannel.productV u =
      κ • (FiberChannel.productV u * TensorPhase.localX i) := by
  rw [productV_right L u κ hexchange i, Matrix.mul_smul]

/-- Equivalent scalar-outside-product convention for left exchange. -/
theorem productW_left_smul (L : Matrix Y Y ℂ) (hL : L.IsHermitian)
    (u : Bool → Y → ℂ) (κ : ℝ)
    (hexchange : ∀ b x, ∑ y, L x y * u b y = (κ : ℂ) * u (!b) x) (i : ι) :
    FiberChannel.productW u * OperatorGrading.localLift L i =
      (κ : ℂ) • (TensorPhase.localX i * FiberChannel.productW u) := by
  rw [productW_left L hL u κ hexchange i, Matrix.smul_mul]

omit [Fintype Y] [DecidableEq Y] in
/-- The actual opposite-fiber mask of a Hermitian matrix is Hermitian. -/
theorem innerCrossing_isHermitian (g : Y → Bool) (K : Matrix Y Y ℂ)
    (hK : K.IsHermitian) : (LocalCommutation.innerCrossing g K).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  change star (if g b ≠ g a then K b a else 0) = if g a ≠ g b then K a b else 0
  by_cases h : g a ≠ g b
  · rw [if_pos h, if_pos (Ne.symm h)]
    exact hK.apply a b
  · have h' : ¬g b ≠ g a := fun h' => h (Ne.symm h')
    rw [if_neg h, if_neg h', star_zero]

/-- The precise two coordinate-crossing inputs used by `OperatorExtraction`,
derived for the constructed product matrices from one-block exchange. -/
theorem crossing_intertwinings (g : Y → Bool) (K : ι → Matrix Y Y ℂ)
    (hK : ∀ i, (K i).IsHermitian) (u : Bool → Y → ℂ) (κ : ℝ)
    (hexchange : ∀ i b x, ∑ y, LocalCommutation.innerCrossing g (K i) x y * u b y =
      (κ : ℂ) * u (!b) x) :
    (∀ i, FiberChannel.productW u *
        OperatorGrading.localLift (LocalCommutation.innerCrossing g (K i)) i =
      ((κ : ℂ) • TensorPhase.localX i) * FiberChannel.productW u) ∧
    (∀ i, OperatorGrading.localLift (LocalCommutation.innerCrossing g (K i)) i *
        FiberChannel.productV u =
      FiberChannel.productV u * ((κ : ℂ) • TensorPhase.localX i)) := by
  constructor
  · intro i
    exact productW_left _ (innerCrossing_isHermitian g (K i) (hK i)) u κ (hexchange i) i
  · intro i
    exact productV_right _ u (κ : ℂ) (hexchange i) i

/-- The same constructed intertwinings in the singleton-grade convention. -/
theorem gradePart_intertwinings (g : Y → Bool) (K : ι → Matrix Y Y ℂ)
    (hK : ∀ i, (K i).IsHermitian) (u : Bool → Y → ℂ) (κ : ℝ)
    (hexchange : ∀ i b x, ∑ y, LocalCommutation.innerCrossing g (K i) x y * u b y =
      (κ : ℂ) * u (!b) x) :
    (∀ i, FiberChannel.productW u * OperatorGrading.gradePart
        (FiberChannel.productLabel g) {i} (OperatorGrading.localLift (K i) i) =
      ((κ : ℂ) • TensorPhase.localX i) * FiberChannel.productW u) ∧
    (∀ i, OperatorGrading.gradePart (FiberChannel.productLabel g) {i}
        (OperatorGrading.localLift (K i) i) * FiberChannel.productV u =
      FiberChannel.productV u * ((κ : ℂ) • TensorPhase.localX i)) := by
  have hc := crossing_intertwinings g K hK u κ hexchange
  constructor
  · intro i
    change FiberChannel.productW u * OperatorGrading.gradePart
      (fun a j => g (a j)) {i} (OperatorGrading.localLift (K i) i) = _
    rw [LocalCommutation.gradePart_localLift]
    exact hc.1 i
  · intro i
    change OperatorGrading.gradePart (fun a j => g (a j)) {i}
      (OperatorGrading.localLift (K i) i) * FiberChannel.productV u = _
    rw [LocalCommutation.gradePart_localLift]
    exact hc.2 i

end

end ApproxDegree.FiberIntertwining
end

-- TensorFiltrationBandwidth.lean
section
/-!
# Product spectral projections and total raw-polynomial bandwidth

All tensor matrices are given by their actual point entries.  They represent
operators on the Euclidean Hilbert space of the full finite product domain.
-/

namespace ApproxDegree.TensorFiltrationBandwidth

open scoped BigOperators ComplexConjugate
open Finset

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {ι Y A : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]

/-- The explicit tensor product of one-block level projections. -/
def productProjection (P : A → Matrix Y Y ℂ) (a : ι → A) : Matrix (ι → Y) (ι → Y) ℂ :=
  FiberIntertwining.tensorRect fun i => P (a i)

omit [DecidableEq ι] [Fintype Y] in
theorem tensorRect_one :
    FiberIntertwining.tensorRect (fun _ : ι => (1 : Matrix Y Y ℂ)) = 1 := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [FiberIntertwining.tensorRect]
  · have hne : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
    obtain ⟨i, hi⟩ := hne
    rw [Matrix.one_apply_ne hxy]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Matrix.one_apply_ne hi

omit [DecidableEq ι] [Fintype Y] [DecidableEq Y] in
theorem tensorRect_zero_of_factor (P : ι → Matrix Y Y ℂ) (i : ι) (hi : P i = 0) :
    FiberIntertwining.tensorRect P = 0 := by
  ext x y
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi]

omit [Fintype Y] [DecidableEq A] in
theorem productProjection_sum (P : A → Matrix Y Y ℂ) (hP : ∑ a, P a = 1) :
    ∑ a : ι → A, productProjection P a = 1 := by
  calc
    _ = FiberIntertwining.tensorRect (fun _ : ι => ∑ a, P a) := by
      ext x y
      simp only [productProjection, Matrix.sum_apply, FiberIntertwining.tensorRect]
      exact (Fintype.prod_sum (fun (i : ι) (a : A) => P a (x i) (y i))).symm
    _ = _ := by simp only [hP, tensorRect_one]

omit [DecidableEq ι] [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A] in
theorem productProjection_isHermitian (P : A → Matrix Y Y ℂ)
    (hP : ∀ a, (P a).IsHermitian) (a : ι → A) : (productProjection P a).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro x y
  change star (∏ i, P (a i) (y i) (x i)) = ∏ i, P (a i) (x i) (y i)
  rw [star_prod]
  exact Finset.prod_congr rfl fun i _ => (hP (a i)).apply (x i) (y i)

omit [DecidableEq Y] [Fintype A] [DecidableEq A] in
theorem productProjection_idempotent (P : A → Matrix Y Y ℂ)
    (hP : ∀ a, P a * P a = P a) (a : ι → A) :
    productProjection P a * productProjection P a = productProjection P a := by
  simp only [productProjection, FiberIntertwining.tensorRect_mul, hP]

omit [DecidableEq Y] [Fintype A] [DecidableEq A] in
theorem productProjection_orthogonal (P : A → Matrix Y Y ℂ)
    (hP : ∀ a b, a ≠ b → P a * P b = 0) {a b : ι → A} (hab : a ≠ b) :
    productProjection P a * productProjection P b = 0 := by
  rw [productProjection, productProjection, FiberIntertwining.tensorRect_mul]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
  exact tensorRect_zero_of_factor _ i (hP _ _ hi)

omit [Fintype Y] [DecidableEq Y] in
theorem tensorRect_one_smul (P : ι → Matrix Y Y ℂ) (i : ι) (c : ℂ) :
    FiberIntertwining.tensorRect (fun j => if j = i then c • P j else P j) =
      c • FiberIntertwining.tensorRect P := by
  ext x y
  change (∏ j, (if j = i then c • P j else P j) (x j) (y j)) =
    c * ∏ j, P j (x j) (y j)
  calc
    _ = ∏ j, (if j = i then c else 1) * P j (x j) (y j) := by
      apply Finset.prod_congr rfl
      intro j _
      split_ifs <;> simp
    _ = (∏ j : ι, if j = i then c else 1) * ∏ j, P j (x j) (y j) :=
      Finset.prod_mul_distrib
    _ = _ := by simp

omit [Fintype A] [DecidableEq A] in
theorem localLift_mul_productProjection (P : A → Matrix Y Y ℂ)
    (H : Matrix Y Y ℂ) (e : A → ℂ) (hH : ∀ a, H * P a = e a • P a)
    (i : ι) (a : ι → A) :
    OperatorGrading.localLift H i * productProjection P a =
      e (a i) • productProjection P a := by
  rw [FiberIntertwining.localLift_eq_tensorRect, productProjection,
    FiberIntertwining.tensorRect_mul]
  have heq : (fun j => (if j = i then H else 1) * P (a j)) =
      (fun j => if j = i then e (a i) • P (a j) else P (a j)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [hH]
    · simp [hji]
  rw [heq, tensorRect_one_smul]

omit [Fintype A] [DecidableEq A] in
theorem sum_localLift_mul_productProjection (P : A → Matrix Y Y ℂ)
    (H : Matrix Y Y ℂ) (e : A → ℂ) (hH : ∀ a, H * P a = e a • P a)
    (a : ι → A) :
    (∑ i : ι, OperatorGrading.localLift H i) * productProjection P a =
      (∑ i, e (a i)) • productProjection P a := by
  rw [Finset.sum_mul]
  simp_rw [localLift_mul_productProjection P H e hH]
  exact Finset.sum_smul.symm

omit [DecidableEq A] in
theorem sum_localLift_eq_spectral_sum (P : A → Matrix Y Y ℂ)
    (hP : ∑ a, P a = 1) (H : Matrix Y Y ℂ) (e : A → ℂ)
    (hH : ∀ a, H * P a = e a • P a) :
    (∑ i : ι, OperatorGrading.localLift H i) =
      ∑ a : ι → A, (∑ i, e (a i)) • productProjection P a := by
  calc
    _ = (∑ i : ι, OperatorGrading.localLift H i) * 1 := (mul_one _).symm
    _ = (∑ i : ι, OperatorGrading.localLift H i) * ∑ a : ι → A, productProjection P a := by
      rw [productProjection_sum P hP]
    _ = ∑ a : ι → A, (∑ i : ι, OperatorGrading.localLift H i) * productProjection P a :=
      Finset.mul_sum _ _ _
    _ = _ := Finset.sum_congr rfl fun a _ => sum_localLift_mul_productProjection P H e hH a

variable {σ : Type*}

/-- Actual point-coordinate matrix of one of the proved local spectral projections. -/
def localLevelMatrix (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ)
    (a : Fin (d + 1)) : Matrix Y Y ℂ :=
  HilbertPointBridge.operatorMatrix
    (FiltrationBandwidth.levelProjection d (WeightedDualVectors.polynomialSpace ψ coords) a.val :
      EuclideanSpace ℂ Y →ₗ[ℂ] EuclideanSpace ℂ Y)

theorem operatorMatrix_one :
    HilbertPointBridge.operatorMatrix (1 : Module.End ℂ (EuclideanSpace ℂ Y)) = 1 :=
  Matrix.toLpLin_symm_id 2

theorem operatorMatrix_zero :
    HilbertPointBridge.operatorMatrix (0 : Module.End ℂ (EuclideanSpace ℂ Y)) = 0 :=
  map_zero Matrix.toEuclideanLin.symm

theorem operatorMatrix_sum {B : Type*} (s : Finset B)
    (L : B → Module.End ℂ (EuclideanSpace ℂ Y)) :
    HilbertPointBridge.operatorMatrix (∑ b ∈ s, L b) =
      ∑ b ∈ s, HilbertPointBridge.operatorMatrix (L b) :=
  map_sum Matrix.toEuclideanLin.symm _ _

theorem localLevelMatrix_sum (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ) :
    ∑ a : Fin (d + 1), localLevelMatrix d ψ coords a = 1 := by
  have h := FiltrationBandwidth.sum_levelProjection_eq_one d
    (WeightedDualVectors.polynomialSpace ψ coords)
  have h' : (∑ a : Fin (d + 1), FiltrationBandwidth.levelProjection d
      (WeightedDualVectors.polynomialSpace ψ coords) a.val) = 1 := by
    simpa only [Fin.sum_univ_eq_sum_range] using h
  have hm := congrArg (fun T : EuclideanSpace ℂ Y →L[ℂ] EuclideanSpace ℂ Y =>
    HilbertPointBridge.operatorMatrix T.toLinearMap) h'
  simpa only [localLevelMatrix, ContinuousLinearMap.toLinearMap_sum,
    ContinuousLinearMap.toLinearMap_one, operatorMatrix_sum, operatorMatrix_one] using hm

theorem localLevelMatrix_isHermitian (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ)
    (a : Fin (d + 1)) : (localLevelMatrix d ψ coords a).IsHermitian :=
  HilbertPointBridge.operatorMatrix_isHermitian _
    (FiltrationBandwidth.levelProjection_isSelfAdjoint d
      (WeightedDualVectors.polynomialSpace ψ coords) a.val).isSymmetric

theorem localLevelMatrix_idempotent (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ)
    (a : Fin (d + 1)) :
    localLevelMatrix d ψ coords a * localLevelMatrix d ψ coords a = localLevelMatrix d ψ coords a := by
  have h := FiltrationBandwidth.levelProjection_idempotent d
    (WeightedDualVectors.polynomialSpace ψ coords)
    (fun _ _ hqr => WeightedDualVectors.polynomialSpace_mono ψ coords hqr) a.val
  have hm := congrArg (fun T : EuclideanSpace ℂ Y →L[ℂ] EuclideanSpace ℂ Y =>
    HilbertPointBridge.operatorMatrix T.toLinearMap) h
  simpa only [localLevelMatrix, ContinuousLinearMap.toLinearMap_mul,
    HilbertPointBridge.operatorMatrix_mul] using hm

theorem localLevelMatrix_orthogonal (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ)
    (a b : Fin (d + 1)) (hab : a ≠ b) :
    localLevelMatrix d ψ coords a * localLevelMatrix d ψ coords b = 0 := by
  have h := FiltrationBandwidth.levelProjection_mul_eq_zero d
    (WeightedDualVectors.polynomialSpace ψ coords)
    (fun _ _ hqr => WeightedDualVectors.polynomialSpace_mono ψ coords hqr)
    (show a.val ≠ b.val from fun h => hab (Fin.ext h))
  have hm := congrArg (fun T : EuclideanSpace ℂ Y →L[ℂ] EuclideanSpace ℂ Y =>
    HilbertPointBridge.operatorMatrix T.toLinearMap) h
  simpa only [localLevelMatrix, ContinuousLinearMap.toLinearMap_mul,
    ContinuousLinearMap.toLinearMap_zero, HilbertPointBridge.operatorMatrix_mul,
    operatorMatrix_zero] using hm

/-- The actual polynomial multiplier matrix, in the original point coordinates. -/
def polynomialMatrix (coords : Y → σ → ℝ) (p : MvPolynomial σ ℝ) : Matrix Y Y ℂ :=
  Matrix.diagonal fun y => (MvPolynomial.eval (coords y) p : ℂ)

theorem operatorMatrix_polynomialMultiplier (coords : Y → σ → ℝ) (p : MvPolynomial σ ℝ) :
    HilbertPointBridge.operatorMatrix
      (WeightedPolynomialAction.polynomialMultiplier coords p).toLinearMap =
        polynomialMatrix coords p :=
  LinearEquiv.symm_apply_apply Matrix.toEuclideanLin _

/-- The already-proved one-block bandwidth in literal point matrices. -/
theorem localLevelMatrix_polynomial_bandwidth (d : ℕ) (ψ : Y → ℝ)
    (coords : Y → σ → ℝ) (p : MvPolynomial σ ℝ) (r : ℕ) (hp : p.totalDegree ≤ r)
    (a b : Fin (d + 1)) (hgap : (r : ℤ) < |(a.val : ℤ) - (b.val : ℤ)|) :
    localLevelMatrix d ψ coords a * polynomialMatrix coords p *
      localLevelMatrix d ψ coords b = 0 := by
  have h := FiltrationBandwidth.polynomialMultiplier_level_bandwidth d ψ coords p r hp a b hgap
  have hm := congrArg (fun T : EuclideanSpace ℂ Y →L[ℂ] EuclideanSpace ℂ Y =>
    HilbertPointBridge.operatorMatrix T.toLinearMap) h
  simpa only [localLevelMatrix, ContinuousLinearMap.toLinearMap_mul,
    ContinuousLinearMap.toLinearMap_zero, HilbertPointBridge.operatorMatrix_mul,
    operatorMatrix_polynomialMultiplier, operatorMatrix_zero] using hm

omit [DecidableEq ι] [Fintype Y] in
theorem tensorRect_diagonal (f : ι → Y → ℂ) :
    FiberIntertwining.tensorRect (fun i => Matrix.diagonal (f i)) =
      Matrix.diagonal (fun x : ι → Y => ∏ i, f i (x i)) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [FiberIntertwining.tensorRect]
  · rw [Matrix.diagonal_apply_ne _ hxy]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Matrix.diagonal_apply_ne _ hi

/-- The integer energy of a product level is the sum of the local energies. -/
def energy {d : ℕ} (a : ι → Fin (d + 1)) : ℤ := ∑ i, (a i).val

theorem witnessMatrix_mul_level (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ)
    (a : Fin (d + 1)) :
    DegreeScaleWitness.witnessMatrix ψ coords d * localLevelMatrix d ψ coords a =
      (a.val : ℂ) • localLevelMatrix d ψ coords a := by
  have h := FiltrationBandwidth.generator_mul_level d
    (WeightedDualVectors.polynomialSpace ψ coords)
    (fun _ _ hqr => WeightedDualVectors.polynomialSpace_mono ψ coords hqr)
    (Nat.le_of_lt_succ a.isLt)
  have hm := congrArg (fun T : EuclideanSpace ℂ Y →L[ℂ] EuclideanSpace ℂ Y =>
    HilbertPointBridge.operatorMatrix T.toLinearMap) h
  have hm' : DegreeScaleWitness.witnessMatrix ψ coords d * localLevelMatrix d ψ coords a =
      (a.val : ℝ) • localLevelMatrix d ψ coords a := by
    simpa only [DegreeScaleWitness.witnessMatrix, DegreeScaleWitness.witnessGenerator,
      localLevelMatrix, ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_smul,
      HilbertPointBridge.operatorMatrix_mul, HilbertPointBridge.operatorMatrix_smul_real] using hm
  rw [hm']
  ext x y
  simp only [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_natCast, smul_eq_mul]

/-- All resolution identities for the actual product projections, with the
one-block hypotheses discharged. -/
theorem actual_product_resolution (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ) :
    (∀ a : ι → Fin (d + 1), (productProjection (localLevelMatrix d ψ coords) a).IsHermitian) ∧
    (∀ a : ι → Fin (d + 1), productProjection (localLevelMatrix d ψ coords) a *
      productProjection (localLevelMatrix d ψ coords) a = productProjection (localLevelMatrix d ψ coords) a) ∧
    (∀ a b : ι → Fin (d + 1), a ≠ b → productProjection (localLevelMatrix d ψ coords) a *
      productProjection (localLevelMatrix d ψ coords) b = 0) ∧
    (∑ a : ι → Fin (d + 1), productProjection (localLevelMatrix d ψ coords) a) = 1 := by
  exact ⟨productProjection_isHermitian _ (localLevelMatrix_isHermitian d ψ coords),
    productProjection_idempotent _ (localLevelMatrix_idempotent d ψ coords),
    fun _ _ hab => productProjection_orthogonal _ (localLevelMatrix_orthogonal d ψ coords) hab,
    productProjection_sum _ (localLevelMatrix_sum d ψ coords)⟩

/-- The exact raw generator used in extraction has the actual product
spectral decomposition at summed integer energies. -/
theorem product_generator_spectral_expansion (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ) :
    (∑ i : ι, OperatorGrading.localLift (DegreeScaleWitness.witnessMatrix ψ coords d) i) =
      ∑ a : ι → Fin (d + 1), (energy a : ℂ) • productProjection (localLevelMatrix d ψ coords) a := by
  have h := sum_localLift_eq_spectral_sum (ι := ι) (localLevelMatrix d ψ coords)
    (localLevelMatrix_sum d ψ coords) (DegreeScaleWitness.witnessMatrix ψ coords d)
    (fun a : Fin (d + 1) => (a.val : ℂ)) (witnessMatrix_mul_level d ψ coords)
  simpa only [energy, Int.cast_sum, Int.cast_natCast] using h

variable [Fintype σ] [DecidableEq σ]

/-- One block's portion of an actual raw multiblock monomial. -/
def blockMonomial (s : (ι × σ) →₀ ℕ) (i : ι) : MvPolynomial σ ℝ :=
  ∏ j : σ, MvPolynomial.X j ^ s (i, j)

def blockDegree (s : (ι × σ) →₀ ℕ) (i : ι) : ℕ := ∑ j : σ, s (i, j)

omit [Fintype ι] [DecidableEq ι] [DecidableEq σ] in
theorem blockMonomial_totalDegree_le (s : (ι × σ) →₀ ℕ) (i : ι) :
    (blockMonomial s i).totalDegree ≤ blockDegree s i := by
  simpa only [blockMonomial, blockDegree, MvPolynomial.totalDegree_X_pow] using
    MvPolynomial.totalDegree_finsetProd Finset.univ
      (fun j : σ => (MvPolynomial.X j : MvPolynomial σ ℝ) ^ s (i, j))

omit [DecidableEq ι] [DecidableEq σ] in
theorem sum_blockDegree (s : (ι × σ) →₀ ℕ) :
    ∑ i : ι, blockDegree s i = s.sum (fun _ n => n) := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]
  rfl

omit [DecidableEq ι] [Fintype Y] [DecidableEq Y] [DecidableEq σ] in
/-- Exact factorization of a raw monomial into one-block monomials. -/
theorem eval_monomial_blocks (coords : Y → σ → ℝ) (s : (ι × σ) →₀ ℕ)
    (c : ℝ) (x : ι → Y) :
    MvPolynomial.eval (fun v : ι × σ => coords (x v.1) v.2) (MvPolynomial.monomial s c) =
      c * ∏ i : ι, MvPolynomial.eval (coords (x i)) (blockMonomial s i) := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type]
  simp [blockMonomial]

omit [DecidableEq ι] [Fintype Y] [DecidableEq σ] in
theorem monomialMatrix_factor (coords : Y → σ → ℝ) (s : (ι × σ) →₀ ℕ) (c : ℝ) :
    polynomialMatrix (fun (x : ι → Y) (v : ι × σ) => coords (x v.1) v.2)
        (MvPolynomial.monomial s c) =
      (c : ℂ) • FiberIntertwining.tensorRect
        (fun i : ι => polynomialMatrix coords (blockMonomial s i)) := by
  unfold polynomialMatrix
  rw [tensorRect_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
    exact_mod_cast eval_monomial_blocks coords s c x
  · simp [Matrix.diagonal_apply_ne _ hxy]

omit [DecidableEq ι] in
theorem energy_sub (d : ℕ) (a b : ι → Fin (d + 1)) :
    energy a - energy b = ∑ i : ι, (((a i).val : ℤ) - ((b i).val : ℤ)) := by
  simp only [energy, Finset.sum_sub_distrib]

omit [DecidableEq ι] [DecidableEq σ] in
/-- A global monomial energy gap forces at least one actual local sandwich
to vanish. The only loss is the exact sum of the monomial's local degrees. -/
theorem monomial_zero_factor (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ)
    (s : (ι × σ) →₀ ℕ) (a b : ι → Fin (d + 1))
    (hgap : (s.sum (fun _ n => n) : ℤ) < |energy a - energy b|) :
    ∃ i : ι, localLevelMatrix d ψ coords (a i) * polynomialMatrix coords (blockMonomial s i) *
      localLevelMatrix d ψ coords (b i) = 0 := by
  by_contra! hnonzero
  have hi (i : ι) : |((a i).val : ℤ) - ((b i).val : ℤ)| ≤ (blockDegree s i : ℤ) := by
    apply le_of_not_gt
    intro h
    exact hnonzero i (localLevelMatrix_polynomial_bandwidth d ψ coords
      (blockMonomial s i) (blockDegree s i) (blockMonomial_totalDegree_le s i) (a i) (b i) h)
  have hsum : |energy a - energy b| ≤ (s.sum (fun _ n => n) : ℤ) := by
    calc
      _ = |∑ i : ι, (((a i).val : ℤ) - ((b i).val : ℤ))| := congrArg abs (energy_sub d a b)
      _ ≤ ∑ i : ι, |((a i).val : ℤ) - ((b i).val : ℤ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : ι, (blockDegree s i : ℤ) := Finset.sum_le_sum fun i _ => hi i
      _ = _ := by exact_mod_cast sum_blockDegree s
  exact (not_lt_of_ge hsum) hgap

omit [DecidableEq σ] in
/-- Exact total-degree bandwidth for a single actual raw monomial. -/
theorem monomial_product_bandwidth (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ)
    (s : (ι × σ) →₀ ℕ) (c : ℝ) (a b : ι → Fin (d + 1))
    (hgap : (s.sum (fun _ n => n) : ℤ) < |energy a - energy b|) :
    productProjection (localLevelMatrix d ψ coords) a *
      polynomialMatrix (fun (x : ι → Y) (v : ι × σ) => coords (x v.1) v.2)
        (MvPolynomial.monomial s c) *
      productProjection (localLevelMatrix d ψ coords) b = 0 := by
  rw [monomialMatrix_factor]
  simp only [productProjection, Matrix.mul_smul, Matrix.smul_mul,
    FiberIntertwining.tensorRect_mul]
  obtain ⟨i, hi⟩ := monomial_zero_factor d ψ coords s a b hgap
  rw [tensorRect_zero_of_factor _ i hi, smul_zero]

omit [Fintype Y] [Fintype σ] [DecidableEq σ] in
theorem polynomialMatrix_as_sum (coords : Y → σ → ℝ) (p : MvPolynomial σ ℝ) :
    polynomialMatrix coords p =
      ∑ s ∈ p.support, polynomialMatrix coords (MvPolynomial.monomial s (p.coeff s)) := by
  ext x y
  have heq : (MvPolynomial.eval (coords x) p : ℂ) =
      ∑ s ∈ p.support, (MvPolynomial.eval (coords x) (MvPolynomial.monomial s (p.coeff s)) : ℂ) := by
    have h := congrArg (fun q : MvPolynomial σ ℝ => (MvPolynomial.eval (coords x) q : ℂ)) p.as_sum
    simpa only [map_sum, Complex.ofReal_sum] using h
  by_cases hxy : x = y
  · subst y
    simpa only [polynomialMatrix, Matrix.sum_apply, Matrix.diagonal_apply_eq] using heq
  · simp only [polynomialMatrix, Matrix.sum_apply, Matrix.diagonal_apply_ne _ hxy,
      sum_const_zero]

omit [DecidableEq σ] in
/-- Actual multiblock raw-polynomial total-degree bandwidth, with no supplied
tensor or polynomial bandwidth premise. -/
theorem rawPolynomial_product_bandwidth (d : ℕ) (ψ : Y → ℝ) (coords : Y → σ → ℝ)
    (p : MvPolynomial (ι × σ) ℝ) (D : ℕ) (hp : p.totalDegree ≤ D)
    (a b : ι → Fin (d + 1)) (hgap : (D : ℤ) < |energy a - energy b|) :
    productProjection (localLevelMatrix d ψ coords) a *
      polynomialMatrix (fun (x : ι → Y) (v : ι × σ) => coords (x v.1) v.2) p *
      productProjection (localLevelMatrix d ψ coords) b = 0 := by
  rw [polynomialMatrix_as_sum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro s hs
  apply monomial_product_bandwidth
  have hsdeg : s.sum (fun _ n => n) ≤ D := (MvPolynomial.le_totalDegree hs).trans hp
  have hsdegZ : (s.sum (fun _ n => n) : ℤ) ≤ (D : ℤ) := by exact_mod_cast hsdeg
  exact lt_of_le_of_lt hsdegZ hgap

end

end ApproxDegree.TensorFiltrationBandwidth
end


