-- Prove2me | Definitions.Def_ApproxDegCompV1_DualWitness
-- name    : ApproxDegCompV1_DualWitness
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-13T04:06:12.596972+00:00
-- url     : https://prove2.me/theorems/61c6f779-c466-4847-86c5-598bdd767da3
-- title:
--   Approximate-degree composition: Finite approximation duality and output-fiber crossing operators
-- statement:
--   This module formalizes finite approximation duality and output-fiber crossing operators for the Lean proof of the approximate-degree composition lower bound.
-- source:
--   https://prove2.me/theorems/f8385c32-068c-45a1-99ed-f7cf0a99f266

import Definitions.Def_ApproxDegCompV1_BooleanPolynomials
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

-- FiniteApproximationDual.lean
section
/-!
# Uniform-approximation duals on an arbitrary finite domain

The norm on real point functions in this file is the uniform norm. We first
construct a separating functional using the normed quotient and Hahn--Banach,
then convert it to explicit real point weights of total absolute mass one.
No off-domain bound or dual witness is assumed.
-/

open scoped BigOperators
open Finset

namespace ApproxDegree.FiniteApproximationDual

noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- The quotient norm is strictly larger than the error if no point of a finite
dimensional subspace attains that uniform error. Attainment of the distance is
proved using closedness and properness, so strictness is not assumed. -/
theorem quotient_norm_gap (V : Submodule ℝ (X → ℝ)) (g : X → ℝ) (ε : ℝ)
    (hgap : ∀ p ∈ V, ε < ‖g - p‖) : ε < ‖V.mkQ g‖ := by
  have hclosed := V.closed_of_finiteDimensional
  obtain ⟨p, hp, heq⟩ := hclosed.exists_infDist_eq_dist ⟨0, V.zero_mem⟩ g
  have hn : ‖V.mkQ g‖ = Metric.infDist g (V : Set (X → ℝ)) :=
    QuotientAddGroup.norm_mk g
  rw [hn, heq, dist_eq_norm]
  exact hgap p hp

/-- Every linear functional on a finite real point space has its literal
coordinate-weight representation. -/
theorem coordinate_representation (φ : (X → ℝ) →L[ℝ] ℝ) (p : X → ℝ) :
    ∑ x, φ (Pi.single x 1) * p x = φ p := by
  calc
    (∑ x, φ (Pi.single x 1) * p x) = ∑ x, φ (Pi.single x (p x)) := by
      apply sum_congr rfl
      intro x hx
      have hs : Pi.single x (p x) = p x • Pi.single x (1 : ℝ) := by
        ext y
        by_cases h : y = x
        · subst y; simp
        · simp [h]
      rw [hs, map_smul]
      simp [mul_comm]
    _ = φ (∑ x, Pi.single x (p x)) := (map_sum φ _ _).symm
    _ = φ p := by rw [univ_sum_single]

/-- The standard finite-domain dual: L1 mass one, exact annihilation of the
approximating subspace, and correlation strictly exceeding the target error. -/
theorem exists_uniform_approximation_dual
    (V : Submodule ℝ (X → ℝ)) (g : X → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hgap : ∀ p ∈ V, ε < ‖g - p‖) :
    ∃ ψ : X → ℝ, (∑ x, |ψ x|) = 1 ∧
      (∀ p ∈ V, ∑ x, ψ x * p x = 0) ∧ ε < ∑ x, ψ x * g x := by
  have hq := quotient_norm_gap V g ε hgap
  obtain ⟨l, hlnorm, hlg⟩ := exists_dual_vector ℝ (V.mkQ g)
    (ne_of_gt (lt_of_le_of_lt hε hq))
  let φ : (X → ℝ) →L[ℝ] ℝ := l.comp V.mkQL
  have hφg : ε < φ g := by
    change ε < l (V.mkQ g)
    rw [hlg]
    exact hq
  have hbound (p : X → ℝ) : |φ p| ≤ ‖p‖ := by
    change ‖l (V.mkQ p)‖ ≤ ‖p‖
    calc
      ‖l (V.mkQ p)‖ ≤ ‖l‖ * ‖V.mkQ p‖ := l.le_opNorm _
      _ = ‖V.mkQ p‖ := by rw [hlnorm, one_mul]
      _ ≤ ‖p‖ := Submodule.Quotient.norm_mk_le V p
  let η : X → ℝ := fun x => φ (Pi.single x 1)
  let s : ℝ := ∑ x, |η x|
  have hrepr (p : X → ℝ) : ∑ x, η x * p x = φ p :=
    coordinate_representation φ p
  have hs0 : 0 ≤ s := sum_nonneg fun x _ => abs_nonneg (η x)
  have hs1 : s ≤ 1 := by
    let signs : X → ℝ := fun x => if 0 ≤ η x then 1 else -1
    have hn : ‖signs‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun x => by
      dsimp [signs]
      split <;> norm_num
    calc
      s = ∑ x, η x * signs x := by
        apply sum_congr rfl
        intro x hx
        dsimp [signs]
        split_ifs with h
        · simp [abs_of_nonneg h]
        · simp [abs_of_neg (lt_of_not_ge h)]
      _ = φ signs := hrepr signs
      _ ≤ |φ signs| := le_abs_self _
      _ ≤ ‖signs‖ := hbound signs
      _ ≤ 1 := hn
  have hspos : 0 < s := by
    by_contra h
    have hs : s = 0 := le_antisymm (le_of_not_gt h) hs0
    have hη : ∀ x, η x = 0 := by
      intro x
      have hle : |η x| ≤ s := single_le_sum (fun y _ => abs_nonneg (η y)) (mem_univ x)
      exact abs_eq_zero.mp (le_antisymm (hs ▸ hle) (abs_nonneg _))
    have hz : φ g = 0 := by rw [← hrepr g]; simp [hη]
    linarith
  refine ⟨fun x => η x / s, ?_, ?_, ?_⟩
  · simp only [abs_div, abs_of_pos hspos, ← sum_div]
    exact div_self (ne_of_gt hspos)
  · intro p hp
    have hz : φ p = 0 := by
      change l (V.mkQ p) = 0
      have hv : V.mkQ p = 0 := by simpa using hp
      rw [hv, map_zero]
    calc
      (∑ x, η x / s * p x) = (∑ x, η x * p x) / s := by
        rw [sum_div]
        apply sum_congr rfl
        intro x hx
        ring
      _ = 0 := by rw [hrepr p, hz, zero_div]
  · have hεs : ε * s ≤ ε := by nlinarith
    have hdiv : ε < φ g / s := (lt_div_iff₀ hspos).2 (lt_of_le_of_lt hεs hφg)
    convert hdiv using 1
    rw [← hrepr g, sum_div]
    apply sum_congr rfl
    intro x hx
    ring

variable {σ : Type*}

/-- Literal evaluation of multivariate real polynomials on the chosen finite
point set. The coordinates need not cover any larger ambient domain. -/
def restrictionMap (coords : X → σ → ℝ) : MvPolynomial σ ℝ →ₗ[ℝ] (X → ℝ) :=
  LinearMap.pi fun x => (MvPolynomial.aeval (coords x)).toLinearMap

/-- The actual restrictions of polynomials of total degree at most q. -/
def polynomialSpace (coords : X → σ → ℝ) (q : ℕ) : Submodule ℝ (X → ℝ) :=
  (MvPolynomial.restrictTotalDegree σ ℝ q).map (restrictionMap coords)

/-- Polynomial duality on an arbitrary finite promise domain, derived from
nonexistence of an approximating polynomial rather than from a supplied dual. -/
theorem exists_polynomial_approximation_dual
    (coords : X → σ → ℝ) (g : X → ℝ) (q : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hno : ¬ ∃ p : MvPolynomial σ ℝ, p.totalDegree ≤ q ∧
      ∀ x, |g x - MvPolynomial.eval (coords x) p| ≤ ε) :
    ∃ ψ : X → ℝ, (∑ x, |ψ x|) = 1 ∧
      (∀ p : MvPolynomial σ ℝ, p.totalDegree ≤ q →
        ∑ x, ψ x * MvPolynomial.eval (coords x) p = 0) ∧
      ε < ∑ x, ψ x * g x := by
  have hgap (v : X → ℝ) (hv : v ∈ polynomialSpace coords q) : ε < ‖g - v‖ := by
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hv
    apply lt_of_not_ge
    intro hle
    apply hno
    refine ⟨p, (MvPolynomial.mem_restrictTotalDegree σ q p).mp hp, ?_⟩
    intro x
    have hx := (pi_norm_le_iff_of_nonneg hε).mp hle x
    exact hx
  obtain ⟨ψ, hnorm, hann, hcorr⟩ :=
    exists_uniform_approximation_dual (polynomialSpace coords q) g ε hε hgap
  refine ⟨ψ, hnorm, ?_, hcorr⟩
  intro p hp
  exact hann (restrictionMap coords p)
    (Submodule.mem_map.mpr ⟨p, (MvPolynomial.mem_restrictTotalDegree σ q p).mpr hp, rfl⟩)

end

end ApproxDegree.FiniteApproximationDual
end

-- WeightedDualVectors.lean
section
/-!
# A polynomial dual realized in a genuine complex Hilbert space

We work directly in EuclideanSpace, multiplying polynomial values by sqrt(abs ψ).
This realizes the weighted point model in the ordinary finite Hilbert norm;
zero weights are allowed and require no division or support restriction.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace ApproxDegree.WeightedDualVectors

noncomputable section

variable {X σ : Type*} [Fintype X]

def rootWeight (ψ : X → ℝ) (x : X) : ℝ := Real.sqrt |ψ x|

def signedRoot (ψ : X → ℝ) (x : X) : ℝ :=
  if 0 ≤ ψ x then rootWeight ψ x else -rootWeight ψ x

def weightedPoint (ψ : X → ℝ) (p : X → ℂ) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 fun x => (rootWeight ψ x : ℂ) * p x

def baseVector (ψ : X → ℝ) : EuclideanSpace ℂ X :=
  weightedPoint ψ (fun _ => 1)

def dualVector (ψ : X → ℝ) : EuclideanSpace ℂ X :=
  WithLp.toLp 2 fun x => (signedRoot ψ x : ℂ)

omit [Fintype X] in
theorem rootWeight_sq (ψ : X → ℝ) (x : X) : rootWeight ψ x ^ 2 = |ψ x| :=
  Real.sq_sqrt (abs_nonneg _)

omit [Fintype X] in
theorem signedRoot_sq (ψ : X → ℝ) (x : X) : signedRoot ψ x ^ 2 = |ψ x| := by
  unfold signedRoot
  split <;> simpa using rootWeight_sq ψ x

omit [Fintype X] in
theorem signedRoot_mul_rootWeight (ψ : X → ℝ) (x : X) :
    signedRoot ψ x * rootWeight ψ x = ψ x := by
  unfold signedRoot
  split_ifs with h
  · rw [← sq, rootWeight_sq, abs_of_nonneg h]
  · rw [neg_mul, ← sq, rootWeight_sq, abs_of_neg (lt_of_not_ge h), neg_neg]

/-- Both explicit vectors have unit Hilbert norm when the dual has L1 mass one. -/
theorem vectors_unit (ψ : X → ℝ) (hmass : ∑ x, |ψ x| = 1) :
    ‖baseVector ψ‖ = 1 ∧ ‖dualVector ψ‖ = 1 := by
  have hb : ‖baseVector ψ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa [baseVector, weightedPoint, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, rootWeight_sq] using hmass
  have hh : ‖dualVector ψ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa [dualVector, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, signedRoot_sq] using hmass
  constructor <;> nlinarith [norm_nonneg (baseVector ψ), norm_nonneg (dualVector ψ)]

/-- The Hilbert inner product recovers the literal dual pairing, for arbitrary
complex point values. -/
theorem inner_dual_weightedPoint (ψ : X → ℝ) (p : X → ℂ) :
    inner ℂ (dualVector ψ) (weightedPoint ψ p) = ∑ x, (ψ x : ℂ) * p x := by
  rw [PiLp.inner_apply]
  apply sum_congr rfl
  intro x hx
  change inner ℂ (signedRoot ψ x : ℂ) ((rootWeight ψ x : ℂ) * p x) = _
  rw [RCLike.inner_apply]
  simp only [Complex.conj_ofReal]
  have h : (signedRoot ψ x : ℂ) * (rootWeight ψ x : ℂ) = (ψ x : ℂ) := by
    exact_mod_cast signedRoot_mul_rootWeight ψ x
  calc
    (rootWeight ψ x : ℂ) * p x * (signedRoot ψ x : ℂ) =
        ((signedRoot ψ x : ℂ) * (rootWeight ψ x : ℂ)) * p x := by ring
    _ = _ := by rw [h]

def weightedPolynomial (ψ : X → ℝ) (coords : X → σ → ℝ)
    (p : MvPolynomial σ ℝ) : EuclideanSpace ℂ X :=
  weightedPoint ψ fun x => (MvPolynomial.eval (coords x) p : ℂ)

/-- Complex span of actual weighted real polynomial restrictions. -/
def polynomialSpace (ψ : X → ℝ) (coords : X → σ → ℝ) (q : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ X) :=
  Submodule.span ℂ {v | ∃ p : MvPolynomial σ ℝ,
    p.totalDegree ≤ q ∧ weightedPolynomial ψ coords p = v}

omit [Fintype X] in
theorem baseVector_mem (ψ : X → ℝ) (coords : X → σ → ℝ) (q : ℕ) :
    baseVector ψ ∈ polynomialSpace ψ coords q := by
  apply Submodule.subset_span
  refine ⟨1, by simp, ?_⟩
  simp [weightedPolynomial, baseVector]

omit [Fintype X] in
theorem polynomialSpace_mono (ψ : X → ℝ) (coords : X → σ → ℝ)
    {q r : ℕ} (hqr : q ≤ r) : polynomialSpace ψ coords q ≤ polynomialSpace ψ coords r := by
  apply Submodule.span_mono
  rintro v ⟨p, hp, rfl⟩
  exact ⟨p, hp.trans hqr, rfl⟩

/-- A real polynomial dual is orthogonal to the entire complex polynomial
space, not merely to individual real polynomial vectors. -/
theorem dualVector_orthogonal (ψ : X → ℝ) (coords : X → σ → ℝ) (q : ℕ)
    (hann : ∀ p : MvPolynomial σ ℝ, p.totalDegree ≤ q →
      ∑ x, ψ x * MvPolynomial.eval (coords x) p = 0) :
    ∀ v ∈ polynomialSpace ψ coords q, inner ℂ (dualVector ψ) v = 0 := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨p, hp, rfl⟩ := hv
      rw [weightedPolynomial, inner_dual_weightedPoint]
      exact_mod_cast hann p hp
  | zero => simp
  | add x y hx hy ihx ihy => simp [inner_add_right, ihx, ihy]
  | smul a x hx ih => simp [inner_smul_right, ih]

/-- Actual polynomial nonapproximation supplies unit Hilbert vectors, a nested
weighted polynomial space containing the base vector, and exact dual correlation. -/
theorem exists_weighted_polynomial_dual [DecidableEq X]
    (coords : X → σ → ℝ) (g : X → ℝ) (q : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hno : ¬ ∃ p : MvPolynomial σ ℝ, p.totalDegree ≤ q ∧
      ∀ x, |g x - MvPolynomial.eval (coords x) p| ≤ ε) :
    ∃ ψ : X → ℝ, (∑ x, |ψ x|) = 1 ∧
      ‖baseVector ψ‖ = 1 ∧ ‖dualVector ψ‖ = 1 ∧
      baseVector ψ ∈ polynomialSpace ψ coords q ∧
      (∀ v ∈ polynomialSpace ψ coords q, inner ℂ (dualVector ψ) v = 0) ∧
      ε < (inner ℂ (dualVector ψ) (weightedPoint ψ (fun x => (g x : ℂ)))).re := by
  obtain ⟨ψ, hmass, hann, hcorr⟩ :=
    FiniteApproximationDual.exists_polynomial_approximation_dual coords g q ε hε hno
  obtain ⟨hv, hh⟩ := vectors_unit ψ hmass
  refine ⟨ψ, hmass, hv, hh, baseVector_mem ψ coords q,
    dualVector_orthogonal ψ coords q hann, ?_⟩
  rw [inner_dual_weightedPoint]
  simpa using hcorr

end

end ApproxDegree.WeightedDualVectors
end

-- ExchangePair.lean
section
/-!
# Construction of a true-fiber exchange pair

All norms in this file are the given complex inner-product-space norms.
No default function-space sup norm or entrywise matrix norm is used.
An eigenvector is input; the exchange pair is explicitly constructed.
-/

namespace ApproxDegree.ExchangePair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- A symmetric involution preserves the actual Hilbert-space norm. -/
theorem symmetric_involution_norm (G : E →ₗ[ℂ] E) (hG : G.IsSymmetric)
    (hGG : ∀ x, G (G x) = x) (x : E) : ‖G x‖ = ‖x‖ := by
  have hi : ⟪G x, G x⟫ = ⟪x, x⟫ := by rw [hG x (G x), hGG x]
  have hs : ‖G x‖ ^ 2 = ‖x‖ ^ 2 := by
    calc
      ‖G x‖ ^ 2 = (⟪G x, G x⟫).re := (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = (⟪x, x⟫).re := congrArg Complex.re hi
      _ = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  nlinarith [norm_nonneg (G x), norm_nonneg x]

/-- Anticommutation sends a real-eigenvalue vector to the opposite eigenvalue. -/
theorem opposite_eigenvector (L G : E →ₗ[ℂ] E)
    (hanti : ∀ x, L (G x) = -G (L x))
    (lam : ℝ) (v : E) (hv : L v = (lam : ℂ) • v) :
    L (G v) = ((-lam : ℝ) : ℂ) • G v := by
  rw [hanti, hv, map_smul]
  simp

/-- The two opposite eigenspaces are orthogonal, proved directly from symmetry. -/
theorem inner_opposite_eq_zero (L G : E →ₗ[ℂ] E) (hL : L.IsSymmetric)
    (hanti : ∀ x, L (G x) = -G (L x))
    (lam : ℝ) (hlam : lam ≠ 0) (v : E) (hv : L v = (lam : ℂ) • v) :
    ⟪v, G v⟫ = 0 := by
  have hs := hL v (G v)
  rw [hv, opposite_eigenvector L G hanti lam v hv] at hs
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    Complex.ofReal_neg, neg_mul] at hs
  have hz : (lam : ℂ) * ⟪v, G v⟫ = 0 := CharZero.eq_neg_self_iff.mp hs
  exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast hlam)

/-- The fixed normalization used for the sum and difference. -/
noncomputable def normalizeSum (w : E) : E :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • w

theorem norm_normalizeSum (w : E) (hw : ‖w‖ = Real.sqrt 2) :
    ‖normalizeSum w‖ = 1 := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [normalizeSum, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg 2)), hw]
  exact inv_mul_cancel₀ hs

/-- Unit sum and difference from a unit vector and its orthogonal involution image. -/
theorem normalized_sum_difference_unit (G : E →ₗ[ℂ] E) (hG : G.IsSymmetric)
    (hGG : ∀ x, G (G x) = x) (v : E) (hv : ‖v‖ = 1)
    (hortho : ⟪v, G v⟫ = 0) :
    ‖normalizeSum (v + G v)‖ = 1 ∧ ‖normalizeSum (v - G v)‖ = 1 := by
  have hGv : ‖G v‖ = 1 := (symmetric_involution_norm G hG hGG v).trans hv
  have hadd := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero v (G v) hortho
  have hsub := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) v (-G v)
    (by simp [hortho])
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : ‖v + G v‖ = Real.sqrt 2 := by
    simp only [hv, hGv] at hadd
    nlinarith [norm_nonneg (v + G v), Real.sqrt_nonneg 2]
  have hm : ‖v - G v‖ = Real.sqrt 2 := by
    simp only [norm_neg, hv, hGv, ← sub_eq_add_neg] at hsub
    nlinarith [norm_nonneg (v - G v), Real.sqrt_nonneg 2]
  exact ⟨norm_normalizeSum _ hp, norm_normalizeSum _ hm⟩

/-- The explicit normalized sum and difference lie in the true involution fibers. -/
theorem normalized_sum_difference_fibers (G : E →ₗ[ℂ] E)
    (hGG : ∀ x, G (G x) = x) (v : E) :
    G (normalizeSum (v + G v)) = normalizeSum (v + G v) ∧
    G (normalizeSum (v - G v)) = -normalizeSum (v - G v) := by
  constructor
  · simp [normalizeSum, map_add, hGG, add_comm]
  · simp [normalizeSum, map_sub, hGG, ← smul_neg, neg_sub]

/-- The explicit pair is exchanged at its input real eigenvalue. -/
theorem normalized_sum_difference_exchange (L G : E →ₗ[ℂ] E)
    (hanti : ∀ x, L (G x) = -G (L x))
    (lam : ℝ) (v : E) (hv : L v = (lam : ℂ) • v) :
    L (normalizeSum (v + G v)) = (lam : ℂ) • normalizeSum (v - G v) ∧
    L (normalizeSum (v - G v)) = (lam : ℂ) • normalizeSum (v + G v) := by
  have ho := opposite_eigenvector L G hanti lam v hv
  constructor
  · simp only [normalizeSum, map_smul, map_add, hv, ho, Complex.ofReal_neg, neg_smul]
    rw [← sub_eq_add_neg, ← smul_sub, smul_comm]
  · simp only [normalizeSum, map_smul, map_sub, hv, ho, Complex.ofReal_neg, neg_smul,
      sub_neg_eq_add]
    rw [← smul_add, smul_comm]

/-- Genuine construction of a unit pair in the two true fibers, exchanging at `|lam|`.
The pair is obtained from the normalized sum/difference of a supplied eigenvector;
for negative `lam` we first replace that vector by its involution image. -/
theorem exists_exchange_pair (L G : E →ₗ[ℂ] E)
    (hL : L.IsSymmetric) (hG : G.IsSymmetric)
    (hGG : ∀ x, G (G x) = x)
    (hanti : ∀ x, L (G x) = -G (L x))
    (lam : ℝ) (hlam : lam ≠ 0) (v : E) (hvnorm : ‖v‖ = 1)
    (hveig : L v = (lam : ℂ) • v) :
    ∃ u₀ u₁ : E, ‖u₀‖ = 1 ∧ ‖u₁‖ = 1 ∧
      G u₀ = u₀ ∧ G u₁ = -u₁ ∧
      L u₀ = ((|lam| : ℝ) : ℂ) • u₁ ∧ L u₁ = ((|lam| : ℝ) : ℂ) • u₀ := by
  have positive_case (μ : ℝ) (hμ : 0 < μ) (w : E) (hwnorm : ‖w‖ = 1)
      (hweig : L w = (μ : ℂ) • w) :
      ∃ u₀ u₁ : E, ‖u₀‖ = 1 ∧ ‖u₁‖ = 1 ∧
        G u₀ = u₀ ∧ G u₁ = -u₁ ∧
        L u₀ = (μ : ℂ) • u₁ ∧ L u₁ = (μ : ℂ) • u₀ := by
    have hn := normalized_sum_difference_unit G hG hGG w hwnorm
      (inner_opposite_eq_zero L G hL hanti μ (ne_of_gt hμ) w hweig)
    have hf := normalized_sum_difference_fibers G hGG w
    have he := normalized_sum_difference_exchange L G hanti μ w hweig
    exact ⟨normalizeSum (w + G w), normalizeSum (w - G w),
      hn.1, hn.2, hf.1, hf.2, he.1, he.2⟩
  by_cases hpos : 0 < lam
  · simpa only [abs_of_pos hpos] using positive_case lam hpos v hvnorm hveig
  · have hneg : lam < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hlam
    have hnorm : ‖G v‖ = 1 := (symmetric_involution_norm G hG hGG v).trans hvnorm
    simpa only [abs_of_neg hneg] using positive_case (-lam) (neg_pos.mpr hneg)
      (G v) hnorm (opposite_eigenvector L G hanti lam v hveig)

/-- The true positive and negative fibers of a symmetric involution are orthogonal. -/
theorem opposite_fibers_orthogonal (G : E →ₗ[ℂ] E) (hG : G.IsSymmetric)
    (u₀ u₁ : E) (h₀ : G u₀ = u₀) (h₁ : G u₁ = -u₁) :
    ⟪u₀, u₁⟫ = 0 := by
  have h := hG u₀ u₁
  rw [h₀, h₁, inner_neg_right] at h
  exact CharZero.eq_neg_self_iff.mp h

/-- Operator-norm-scale interface, using the genuine continuous-operator norm.
The spectral norm-attainment equality is an explicit input, not inferred here. -/
theorem exists_exchange_pair_at_opNorm (L G : E →L[ℂ] E)
    (hL : (L : E →ₗ[ℂ] E).IsSymmetric) (hG : (G : E →ₗ[ℂ] E).IsSymmetric)
    (hGG : ∀ x, G (G x) = x) (hanti : ∀ x, L (G x) = -G (L x))
    (lam : ℝ) (hlam : lam ≠ 0) (v : E) (hvnorm : ‖v‖ = 1)
    (hveig : L v = (lam : ℂ) • v) (hscale : |lam| = ‖L‖) :
    ∃ u₀ u₁ : E, ‖u₀‖ = 1 ∧ ‖u₁‖ = 1 ∧
      G u₀ = u₀ ∧ G u₁ = -u₁ ∧
      L u₀ = (‖L‖ : ℂ) • u₁ ∧ L u₁ = (‖L‖ : ℂ) • u₀ := by
  simpa only [hscale, ContinuousLinearMap.coe_coe] using
    exists_exchange_pair (L : E →ₗ[ℂ] E) (G : E →ₗ[ℂ] E)
      hL hG hGG hanti lam hlam v hvnorm hveig

/-- Literal self-adjoint-operator interface on a complex Hilbert space. -/
theorem exists_exchange_pair_of_selfAdjoint [CompleteSpace E] (L G : E →L[ℂ] E)
    (hL : IsSelfAdjoint L) (hG : IsSelfAdjoint G)
    (hGG : ∀ x, G (G x) = x) (hanti : ∀ x, L (G x) = -G (L x))
    (lam : ℝ) (hlam : lam ≠ 0) (v : E) (hvnorm : ‖v‖ = 1)
    (hveig : L v = (lam : ℂ) • v) :
    ∃ u₀ u₁ : E, ‖u₀‖ = 1 ∧ ‖u₁‖ = 1 ∧
      G u₀ = u₀ ∧ G u₁ = -u₁ ∧
      L u₀ = ((|lam| : ℝ) : ℂ) • u₁ ∧ L u₁ = ((|lam| : ℝ) : ℂ) • u₀ := by
  simpa only [ContinuousLinearMap.coe_coe] using
    exists_exchange_pair (L : E →ₗ[ℂ] E) (G : E →ₗ[ℂ] E)
      hL.isSymmetric hG.isSymmetric hGG hanti lam hlam v hvnorm hveig

end ApproxDegree.ExchangePair
end

-- FiltrationOperator.lean
section
/-!
# A concrete finite projection-filtration generator and its crossing strip

The generator is defined from actual orthogonal projections.  Its self-adjointness,
its action on common and orthogonal vectors, and the norm lower bound for its
true-fiber strip are proved.  Nestedness is not needed for these particular facts;
polynomial bandwidth and its use of nestedness are separate application steps.
-/

namespace ApproxDegree.FiltrationOperator

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- `d I` minus the sum of the projections onto the first `d` subspaces.
`starProjection` is the orthogonal projection regarded as an endomorphism of E. -/
noncomputable def generator (d : ℕ) (V : Fin d → Submodule ℂ E) : E →L[ℂ] E :=
  (d : ℝ) • (1 : E →L[ℂ] E) - ∑ j, (V j).starProjection

theorem generator_isSelfAdjoint (d : ℕ) (V : Fin d → Submodule ℂ E) :
    IsSelfAdjoint (generator d V) := by
  apply IsSelfAdjoint.sub
  · exact (IsSelfAdjoint.all (d : ℝ)).smul (IsSelfAdjoint.one _)
  · exact isSelfAdjoint_sum _ (fun j _ => isSelfAdjoint_starProjection (V j))

omit [CompleteSpace E] in
/-- A vector belonging to every projected subspace is in the kernel. -/
theorem generator_apply_of_mem (d : ℕ) (V : Fin d → Submodule ℂ E)
    (v : E) (hv : ∀ j, v ∈ V j) : generator d V v = 0 := by
  have hp : ∀ j, (V j).starProjection v = v :=
    fun j => (V j).starProjection_eq_self_iff.mpr (hv j)
  simp [generator, hp, Nat.cast_smul_eq_nsmul]

omit [CompleteSpace E] in
/-- A vector orthogonal to every projected subspace is a `d`-eigenvector. -/
theorem generator_apply_of_orthogonal (d : ℕ) (V : Fin d → Submodule ℂ E)
    (h : E) (hh : ∀ j, h ∈ (V j)ᗮ) : generator d V h = (d : ℝ) • h := by
  have hp : ∀ j, (V j).starProjection h = 0 :=
    fun j => (V j).starProjection_apply_eq_zero_iff.mpr (hh j)
  simp [generator, hp]

/-- The actual off-fiber strip with respect to an involution. -/
noncomputable def crossingStrip (H G : E →L[ℂ] E) : E →L[ℂ] E :=
  (1 / 2 : ℝ) • (H - G * H * G)

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
theorem crossingStrip_apply (H G : E →L[ℂ] E) (x : E) :
    crossingStrip H G x = (1 / 2 : ℝ) • (H x - G (H (G x))) := by
  simp [crossingStrip]

omit [FiniteDimensional ℂ E] in
theorem crossingStrip_isSelfAdjoint (H G : E →L[ℂ] E)
    (hH : IsSelfAdjoint H) (hG : IsSelfAdjoint G) :
    IsSelfAdjoint (crossingStrip H G) := by
  exact (IsSelfAdjoint.all (1 / 2 : ℝ)).smul (hH.sub (hH.conjugate_self hG))

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
theorem crossingStrip_anticommutes (H G : E →L[ℂ] E)
    (hGG : ∀ x, G (G x) = x) (x : E) :
    crossingStrip H G (G x) = -G (crossingStrip H G x) := by
  simp only [crossingStrip_apply, ContinuousLinearMap.map_smul_of_tower, map_sub, hGG]
  rw [← smul_neg, neg_sub]

omit [FiniteDimensional ℂ E] in
/-- The pairing identity responsible for the degree-scale lower bound. -/
theorem crossingStrip_pairing (H G : E →L[ℂ] E)
    (hH : IsSelfAdjoint H) (hGG : ∀ x, G (G x) = x)
    (a : ℝ) (v h : E) (hv : H v = 0) (hh : H h = a • h) :
    ⟪h, crossingStrip H G (G v)⟫ = (a / 2 : ℝ) • ⟪h, G v⟫ := by
  have hs : ⟪H h, G v⟫ = ⟪h, H (G v)⟫ := hH.isSymmetric h (G v)
  rw [crossingStrip_apply, hGG, hv, map_zero, sub_zero,
    inner_smul_right_eq_smul, ← hs, hh,
    inner_smul_left_eq_star_smul]
  simp only [starRingEnd_apply, star_trivial, smul_smul]
  congr 1
  ring

omit [FiniteDimensional ℂ E] in
/-- Unit test vectors give an exact operator-norm lower bound; no sign
assumption on their real correlation is needed for this non-strict inequality. -/
theorem crossingStrip_norm_lower_bound (H G : E →L[ℂ] E)
    (hH : IsSelfAdjoint H) (hG : IsSelfAdjoint G)
    (hGG : ∀ x, G (G x) = x) (a : ℝ) (v h : E)
    (hvnorm : ‖v‖ = 1) (hhnorm : ‖h‖ = 1)
    (hv : H v = 0) (hh : H h = a • h) :
    a * (⟪h, G v⟫).re ≤ 2 * ‖crossingStrip H G‖ := by
  have hGv : ‖G v‖ = 1 :=
    (ExchangePair.symmetric_involution_norm
      (G : E →ₗ[ℂ] E) hG.isSymmetric hGG v).trans hvnorm
  have hp := congrArg Complex.re (crossingStrip_pairing H G hH hGG a v h hv hh)
  simp only [Complex.smul_re, smul_eq_mul] at hp
  have hi : (⟪h, crossingStrip H G (G v)⟫).re ≤
      ‖h‖ * ‖crossingStrip H G (G v)‖ := re_inner_le_norm (𝕜 := ℂ) _ _
  have hb := (crossingStrip H G).le_opNorm (G v)
  rw [hhnorm, one_mul, hp] at hi
  rw [hGv, mul_one] at hb
  nlinarith

/-- The concrete projection generator's strip has at least `d ρ / 2` norm. -/
theorem generator_crossing_norm_lower_bound (d : ℕ) (V : Fin d → Submodule ℂ E)
    (G : E →L[ℂ] E) (hG : IsSelfAdjoint G) (hGG : ∀ x, G (G x) = x)
    (v h : E) (hvnorm : ‖v‖ = 1) (hhnorm : ‖h‖ = 1)
    (hv : ∀ j, v ∈ V j) (hh : ∀ j, h ∈ (V j)ᗮ) :
    (d : ℝ) * (⟪h, G v⟫).re ≤ 2 * ‖crossingStrip (generator d V) G‖ := by
  exact crossingStrip_norm_lower_bound (generator d V) G
    (generator_isSelfAdjoint d V) hG hGG d v h hvnorm hhnorm
    (generator_apply_of_mem d V v hv) (generator_apply_of_orthogonal d V h hh)

/-- With positive `d`, a strict dual correlation gives a strict degree-scale
bound. Positivity of `d` is explicit, since the statement fails for `d = 0`. -/
theorem generator_crossing_norm_gt (d : ℕ) (hd : 0 < d)
    (V : Fin d → Submodule ℂ E) (G : E →L[ℂ] E)
    (hG : IsSelfAdjoint G) (hGG : ∀ x, G (G x) = x)
    (v h : E) (hvnorm : ‖v‖ = 1) (hhnorm : ‖h‖ = 1)
    (hv : ∀ j, v ∈ V j) (hh : ∀ j, h ∈ (V j)ᗮ)
    (eps : ℝ) (hcorr : eps < (⟪h, G v⟫).re) :
    eps * (d : ℝ) / 2 < ‖crossingStrip (generator d V) G‖ := by
  have hb := generator_crossing_norm_lower_bound d V G hG hGG v h hvnorm hhnorm hv hh
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hc := mul_lt_mul_of_pos_left hcorr hdR
  nlinarith

/-- Positive correlation at positive depth certifies a nonzero strip,
discharging the nonzero premise of `SpectralExchange`. -/
theorem generator_crossing_ne_zero (d : ℕ) (hd : 0 < d)
    (V : Fin d → Submodule ℂ E) (G : E →L[ℂ] E)
    (hG : IsSelfAdjoint G) (hGG : ∀ x, G (G x) = x)
    (v h : E) (hvnorm : ‖v‖ = 1) (hhnorm : ‖h‖ = 1)
    (hv : ∀ j, v ∈ V j) (hh : ∀ j, h ∈ (V j)ᗮ)
    (hcorr : 0 < (⟪h, G v⟫).re) :
    crossingStrip (generator d V) G ≠ 0 := by
  apply norm_pos_iff.mp
  simpa only [zero_mul, zero_div] using
    generator_crossing_norm_gt d hd V G hG hGG v h hvnorm hhnorm hv hh 0 hcorr

end ApproxDegree.FiltrationOperator
end

-- SpectralExchange.lean
section
/-!
# Norm-scale exchange pairs from finite-dimensional spectral theory

The norms here are the given complex Hilbert norm and its continuous-linear-map
operator norm.  No matrix or function-space norm is substituted.  In finite
dimension, a self-adjoint operator has a real eigenvalue whose absolute value
is its operator norm.  We obtain this from spectral-radius attainment and the
finite-dimensional equivalence of spectral values and eigenvalues, normalize
the resulting vector, and invoke the explicit `ExchangePair` construction.
-/

namespace ApproxDegree.SpectralExchange

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]

/-- A nonzero self-adjoint operator on a finite-dimensional complex Hilbert
space has a unit eigenvector at a nonzero real eigenvalue of absolute value
equal to its genuine operator norm.  No eigendata is assumed. -/
theorem exists_unit_eigenvector_at_opNorm (L : E →L[ℂ] E)
    (hL : IsSelfAdjoint L) (hLne : L ≠ 0) :
    ∃ (lam : ℝ) (v : E), lam ≠ 0 ∧ ‖v‖ = 1 ∧
      L v = (lam : ℂ) • v ∧ |lam| = ‖L‖ := by
  let : Nontrivial (E →L[ℂ] E) := ⟨⟨L, 0, hLne⟩⟩
  obtain ⟨z, hzspec, hzradius⟩ := spectrum.exists_nnnorm_eq_spectralRadius L
  have hzscale : ‖z‖ = ‖L‖ := by
    have h := congrArg ENNReal.toReal hzradius
    simpa only [ENNReal.coe_toReal, coe_nnnorm,
      hL.toReal_spectralRadius_complex_eq_norm] using h
  have hzreal : z = (z.re : ℂ) := hL.mem_spectrum_eq_re hzspec
  have hrscale : |z.re| = ‖L‖ := by
    calc
      |z.re| = ‖(z.re : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ = ‖z‖ := congrArg norm hzreal.symm
      _ = ‖L‖ := hzscale
  have hrne : z.re ≠ 0 := by
    intro hr
    have : ‖L‖ = 0 := by simpa [hr] using hrscale.symm
    exact hLne (norm_eq_zero.mp this)
  have hzeig : Module.End.HasEigenvalue (L : E →ₗ[ℂ] E) z := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    simpa only [ContinuousLinearMap.spectrum_eq] using hzspec
  obtain ⟨w, hweigen⟩ := hzeig.exists_hasEigenvector
  have hweq : L w = (z.re : ℂ) • w := by
    rw [← hzreal]
    exact hweigen.apply_eq_smul
  have hwnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hweigen.2
  let v : E := (((‖w‖)⁻¹ : ℝ) : ℂ) • w
  have hvnorm : ‖v‖ = 1 := by
    dsimp only [v]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w))]
    exact inv_mul_cancel₀ hwnorm
  have hveq : L v = (z.re : ℂ) • v := by
    dsimp only [v]
    rw [map_smul, hweq, smul_comm]
  exact ⟨z.re, v, hrne, hvnorm, hveq, hrscale⟩

/-- A nonzero self-adjoint operator anticommuting with a self-adjoint
involution has a normalized pair in the true positive and negative fibers,
exchanged at the operator norm.  The pair is derived rather than supplied. -/
theorem exists_true_fiber_exchange_pair (L G : E →L[ℂ] E)
    (hL : IsSelfAdjoint L) (hLne : L ≠ 0) (hG : IsSelfAdjoint G)
    (hGG : ∀ x, G (G x) = x) (hanti : ∀ x, L (G x) = -G (L x)) :
    ∃ u₀ u₁ : E, ‖u₀‖ = 1 ∧ ‖u₁‖ = 1 ∧
      G u₀ = u₀ ∧ G u₁ = -u₁ ∧
      L u₀ = (‖L‖ : ℂ) • u₁ ∧ L u₁ = (‖L‖ : ℂ) • u₀ := by
  obtain ⟨lam, v, hlam, hvnorm, hveig, hscale⟩ :=
    exists_unit_eigenvector_at_opNorm L hL hLne
  exact ExchangePair.exists_exchange_pair_at_opNorm L G
    hL.isSymmetric hG.isSymmetric hGG hanti lam hlam v hvnorm hveig hscale

/-- The constructed exchange pair is orthonormal for the Hilbert inner
product, with the same exact norm-scale exchange identities. -/
theorem exists_orthonormal_true_fiber_exchange_pair (L G : E →L[ℂ] E)
    (hL : IsSelfAdjoint L) (hLne : L ≠ 0) (hG : IsSelfAdjoint G)
    (hGG : ∀ x, G (G x) = x) (hanti : ∀ x, L (G x) = -G (L x)) :
    ∃ u₀ u₁ : E, ‖u₀‖ = 1 ∧ ‖u₁‖ = 1 ∧ inner ℂ u₀ u₁ = 0 ∧
      G u₀ = u₀ ∧ G u₁ = -u₁ ∧
      L u₀ = (‖L‖ : ℂ) • u₁ ∧ L u₁ = (‖L‖ : ℂ) • u₀ := by
  obtain ⟨u₀, u₁, hn₀, hn₁, hf₀, hf₁, he₀, he₁⟩ :=
    exists_true_fiber_exchange_pair L G hL hLne hG hGG hanti
  exact ⟨u₀, u₁, hn₀, hn₁,
    ExchangePair.opposite_fibers_orthogonal
      (G : E →ₗ[ℂ] E) hG.isSymmetric u₀ u₁ hf₀ hf₁,
    hf₀, hf₁, he₀, he₁⟩

end ApproxDegree.SpectralExchange
end

-- ProtectedCrossings.lean
section
/-!
# The combinatorial core of protected distinct crossings

`none` is a step preserving logical parity, and `some i` toggles block `i`.
The theorems below are general in the index type and word length. They are
not a formalization of the analytic composition theorem: the operator-word
expansion and its actual logical block grading must still be connected.
-/

namespace ApproxDegree.ProtectedCrossings

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- Toggle membership of one block in a logical parity support. -/
def toggle (i : ι) (s : Finset ι) : Finset ι :=
  if i ∈ s then s.erase i else insert i s

/-- The parity support of a word; even steps leave it unchanged. -/
def paritySupport : List (Option ι) → Finset ι
  | [] => ∅
  | none :: w => paritySupport w
  | some i :: w => toggle i (paritySupport w)

theorem card_toggle_le (i : ι) (s : Finset ι) :
    (toggle i s).card ≤ s.card + 1 := by
  by_cases h : i ∈ s
  · simp only [toggle, if_pos h]
    exact (Finset.card_le_card (Finset.erase_subset i s)).trans (Nat.le_succ _)
  · simp [toggle, h]

/-- No word can cross more logical blocks than its number of steps. -/
theorem card_paritySupport_le (w : List (Option ι)) :
    (paritySupport w).card ≤ w.length := by
  induction w with
  | nil => simp [paritySupport]
  | cons a w ih =>
    cases a with
    | none => simpa [paritySupport] using Nat.le_succ_of_le ih
    | some i =>
      exact (card_toggle_le i (paritySupport w)).trans (Nat.succ_le_succ ih)

/-- A word of pairwise distinct odd steps has precisely its usual support. -/
theorem paritySupport_map_some_of_nodup (l : List ι) (hl : l.Nodup) :
    paritySupport (l.map some) = l.toFinset := by
  induction l with
  | nil => simp [paritySupport]
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hl
    simp [paritySupport, ih hl, toggle, ha]

/-- Maximal logical distance forces every step odd and all block indices distinct. -/
theorem maximal_paritySupport_iff (w : List (Option ι)) :
    (paritySupport w).card = w.length ↔
      ∃ l : List ι, l.Nodup ∧ w = l.map some := by
  constructor
  · intro hw
    induction w with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons a w ih =>
      have hbound := card_paritySupport_le w
      cases a with
      | none =>
        simp only [paritySupport, List.length_cons] at hw
        omega
      | some i =>
        have hi : i ∉ paritySupport w := by
          intro hi
          have he := Finset.card_le_card (Finset.erase_subset i (paritySupport w))
          simp only [paritySupport, toggle, if_pos hi, List.length_cons] at hw
          omega
        have htail : (paritySupport w).card = w.length := by
          simpa [paritySupport, toggle, hi] using hw
        obtain ⟨l, hl, hw'⟩ := ih htail
        have hin : i ∉ l := by
          rw [hw', paritySupport_map_some_of_nodup l hl] at hi
          simpa using hi
        exact ⟨i :: l, List.nodup_cons.mpr ⟨hin, hl⟩, by simp [hw']⟩
  · rintro ⟨l, hl, rfl⟩
    rw [paritySupport_map_some_of_nodup l hl]
    simpa using List.toFinset_card_of_nodup hl

/-- The different orders of a finite set of crossing indices. -/
noncomputable def orderings (s : Finset ι) : Finset (List ι) :=
  s.toList.permutations.toFinset

theorem mem_orderings_iff (s : Finset ι) (l : List ι) :
    l ∈ orderings s ↔ l.Perm s.toList := by
  simp [orderings, List.mem_permutations]

/-- There are exactly `k!` distinct words ordering a set of `k` blocks. -/
theorem card_orderings (s : Finset ι) :
    (orderings s).card = s.card.factorial := by
  rw [orderings, List.toFinset_card_of_nodup
    (List.nodup_permutations s.toList (Finset.nodup_toList s))]
  simp [List.length_permutations]

/-- The general maximal-word characterization, with its precise support fixed. -/
theorem maximal_word_iff_ordering (w : List (Option ι)) (s : Finset ι) :
    paritySupport w = s ∧ w.length = s.card ↔
      ∃ l ∈ orderings s, w = l.map some := by
  constructor
  · rintro ⟨hs, hw⟩
    have hmax : (paritySupport w).card = w.length := by rw [hs, hw]
    obtain ⟨l, hl, rfl⟩ := (maximal_paritySupport_iff w).mp hmax
    have hsupport : l.toFinset = s := by
      simpa [paritySupport_map_some_of_nodup l hl] using hs
    refine ⟨l, (mem_orderings_iff s l).mpr ?_, rfl⟩
    apply (List.perm_ext_iff_of_nodup hl (Finset.nodup_toList s)).mpr
    intro a
    simp [← hsupport]
  · rintro ⟨l, hl, rfl⟩
    have hp := (mem_orderings_iff s l).mp hl
    have hn : l.Nodup := hp.nodup_iff.mpr (Finset.nodup_toList s)
    constructor
    · rw [paritySupport_map_some_of_nodup l hn]
      ext a
      simpa using hp.mem_iff
    · simpa using hp.length_eq

/-- All words whose logical distance reaches their length, with support `s`. -/
noncomputable def maximalWords (s : Finset ι) : Finset (List (Option ι)) :=
  (orderings s).image (List.map some)

theorem mem_maximalWords_iff (w : List (Option ι)) (s : Finset ι) :
    w ∈ maximalWords s ↔ paritySupport w = s ∧ w.length = s.card := by
  rw [maximal_word_iff_ordering]
  simp only [maximalWords, Finset.mem_image]
  constructor
  · rintro ⟨l, hl, h⟩
    exact ⟨l, hl, h.symm⟩
  · rintro ⟨l, hl, h⟩
    exact ⟨l, hl, h.symm⟩

/-- The exact factorial count of maximal-distance even/odd words. -/
theorem card_maximalWords (s : Finset ι) :
    (maximalWords s).card = s.card.factorial := by
  rw [maximalWords, Finset.card_image_of_injective]
  · exact card_orderings s
  · exact List.map_injective_iff.mpr (fun _ _ h => Option.some.inj h)

section CommutingMaps

variable {M : Type*}

/-- Apply a word of local maps, with the leftmost map applied last. -/
def applyWord (f : ι → M → M) (l : List ι) (x : M) : M :=
  l.foldr f x

omit [DecidableEq ι] in
/-- Commuting local maps make the value independent of word order. -/
theorem applyWord_perm (f : ι → M → M)
    (hcomm : ∀ i j x, f i (f j x) = f j (f i x))
    {l₁ l₂ : List ι} (h : l₁.Perm l₂) (x : M) :
    applyWord f l₁ x = applyWord f l₂ x := by
  unfold applyWord
  induction h with
  | nil => rfl
  | cons a h ih => exact congrArg (f a) ih
  | swap a b l => exact hcomm b a (l.foldr f x)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

variable [AddCommMonoid M]

/-- The factorial multiplicity identity for a fixed set of distinct crossings. -/
theorem sum_orderings_applyWord (f : ι → M → M)
    (hcomm : ∀ i j x, f i (f j x) = f j (f i x))
    (s : Finset ι) (x : M) :
    (∑ l ∈ orderings s, applyWord f l x) =
      s.card.factorial • applyWord f s.toList x := by
  calc
    (∑ l ∈ orderings s, applyWord f l x) =
        (orderings s).card • applyWord f s.toList x := by
      apply Finset.sum_eq_card_nsmul
      intro l hl
      exact applyWord_perm f hcomm ((mem_orderings_iff s l).mp hl) x
    _ = _ := by rw [card_orderings]

end CommutingMaps

section Commutators

variable {A : Type*} [Ring A]

/-- The associative-ring commutator acting as a local derivation. -/
def commutator (a x : A) : A := a * x - x * a

omit [DecidableEq ι] in
/-- Commuting ring elements induce commuting commutator maps. -/
theorem commutator_maps_commute (a b : A) (hab : a * b = b * a) (x : A) :
    commutator a (commutator b x) = commutator b (commutator a x) := by
  have hJacobi : commutator a (commutator b x) - commutator b (commutator a x) =
      commutator (commutator a b) x := by
    unfold commutator
    noncomm_ring
  have hz : commutator a b = 0 := sub_eq_zero.mpr hab
  apply sub_eq_zero.mp
  rw [hJacobi, hz]
  simp [commutator]

/-- Factorial multiplicity for distinct-block commutators in any associative ring. -/
theorem sum_orderings_commutator (L : ι → A)
    (hcomm : ∀ i j, i ≠ j → L i * L j = L j * L i)
    (s : Finset ι) (P : A) :
    (∑ l ∈ orderings s, applyWord (fun i => commutator (L i)) l P) =
      s.card.factorial • applyWord (fun i => commutator (L i)) s.toList P := by
  apply sum_orderings_applyWord
  intro i j x
  by_cases hij : i = j
  · subst j
    rfl
  · exact commutator_maps_commute (L i) (L j) (hcomm i j hij) x

end Commutators

end ApproxDegree.ProtectedCrossings

-- Dependency audit: these should list only Lean's standard logical axioms,
-- never `sorryAx` or a project-specific mathematical axiom.
end


