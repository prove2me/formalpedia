-- Prove2me | Definitions.Def_ApproxDegCompV1_BooleanPolynomials
-- name    : ApproxDegCompV1_BooleanPolynomials
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-13T04:05:32.007709+00:00
-- url     : https://prove2.me/theorems/48fa38f2-155e-4477-a419-2bbd249ffb46
-- title:
--   Approximate-degree composition: Boolean interpolation, error reduction, and Fourier truncation
-- statement:
--   This module formalizes boolean interpolation, error reduction, and Fourier truncation for the Lean proof of the approximate-degree composition lower bound.
-- source:
--   https://prove2.me/theorems/f8385c32-068c-45a1-99ed-f7cf0a99f266

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

-- BooleanApproxDegree.lean
section
/-!
# Approximate degree on finite Boolean promise domains

Coordinates are an injective map from an arbitrary finite promise type to a
Boolean cube. Explicit Boolean interpolation proves that every real target has
an exact polynomial representation. Approximate degree is therefore an attained
minimum for every nonnegative error, with no off-promise bounds.
-/

open scoped BigOperators
open Finset

namespace ApproxDegree.BooleanApproxDegree

noncomputable section

variable {X σ : Type*} [Fintype X] [DecidableEq X] [Fintype σ]

def bitValue (b : Bool) : ℝ := if b then 1 else 0

def realCoords (coords : X → σ → Bool) (x : X) (i : σ) : ℝ := bitValue (coords x i)

def indicator (coords : X → σ → Bool) (x : X) : MvPolynomial σ ℝ :=
  ∏ i, if coords x i then MvPolynomial.X i else 1 - MvPolynomial.X i

omit [Fintype X] in
theorem eval_indicator (coords : X → σ → Bool) (hinj : Function.Injective coords)
    (x y : X) : MvPolynomial.eval (realCoords coords y) (indicator coords x) =
      if y = x then 1 else 0 := by
  unfold indicator
  rw [MvPolynomial.eval_prod]
  by_cases hyx : y = x
  · subst y
    rw [if_pos rfl]
    apply prod_eq_one
    intro i hi
    cases hb : coords x i <;> simp [realCoords, bitValue, hb]
  · rw [if_neg hyx]
    have hne : coords y ≠ coords x := fun h => hyx (hinj h)
    obtain ⟨i, hi⟩ : ∃ i, coords y i ≠ coords x i := by
      by_contra h
      apply hne
      funext i
      exact not_ne_iff.mp (not_exists.mp h i)
    apply prod_eq_zero (mem_univ i)
    cases hx : coords x i <;> cases hy : coords y i <;>
      simp_all [realCoords, bitValue]

omit [Fintype X] [DecidableEq X] in
theorem indicator_degree_le (coords : X → σ → Bool) (x : X) :
    (indicator coords x).totalDegree ≤ Fintype.card σ := by
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    (∑ i, (if coords x i then MvPolynomial.X i else
      (1 : MvPolynomial σ ℝ) - MvPolynomial.X i).totalDegree) ≤ ∑ _ : σ, 1 := by
        apply sum_le_sum
        intro i hi
        cases coords x i
        · exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)
        · simp
    _ = Fintype.card σ := by simp

def interpolation (coords : X → σ → Bool) (f : X → ℝ) : MvPolynomial σ ℝ :=
  ∑ x, MvPolynomial.C (f x) * indicator coords x

theorem eval_interpolation (coords : X → σ → Bool) (hinj : Function.Injective coords)
    (f : X → ℝ) (x : X) :
    MvPolynomial.eval (realCoords coords x) (interpolation coords f) = f x := by
  simp [interpolation, eval_indicator coords hinj]

omit [DecidableEq X] in
theorem interpolation_degree_le (coords : X → σ → Bool) (f : X → ℝ) :
    (interpolation coords f).totalDegree ≤ Fintype.card σ := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro x hx
  calc
    _ ≤ (MvPolynomial.C (f x) : MvPolynomial σ ℝ).totalDegree +
        (indicator coords x).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (indicator coords x).totalDegree := by simp
    _ ≤ _ := indicator_degree_le coords x

def Admissible (coords : X → σ → ℝ) (f : X → ℝ) (ε : ℝ) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial σ ℝ, p.totalDegree ≤ d ∧
    ∀ x, |f x - MvPolynomial.eval (coords x) p| ≤ ε

/-- Unrestricted-off-promise approximate degree. The next theorems justify
attainment for injective Boolean coordinates and nonnegative error. -/
def approximateDegree (coords : X → σ → ℝ) (f : X → ℝ) (ε : ℝ) : ℕ :=
  sInf {d | Admissible coords f ε d}

theorem admissible_nonempty (coords : X → σ → Bool) (hinj : Function.Injective coords)
    (f : X → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    {d | Admissible (realCoords coords) f ε d}.Nonempty := by
  refine ⟨Fintype.card σ, interpolation coords f, interpolation_degree_le coords f, ?_⟩
  intro x
  simpa [eval_interpolation coords hinj] using hε

theorem exists_approximation_at_degree (coords : X → σ → Bool) (hinj : Function.Injective coords)
    (f : X → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    Admissible (realCoords coords) f ε (approximateDegree (realCoords coords) f ε) :=
  csInf_mem (admissible_nonempty coords hinj f ε hε)

omit [Fintype X] [DecidableEq X] [Fintype σ] in
theorem approximateDegree_le {coords : X → σ → ℝ} {f : X → ℝ} {ε : ℝ} {d : ℕ}
    (h : Admissible coords f ε d) : approximateDegree coords f ε ≤ d :=
  csInf_le' h

omit [Fintype X] [DecidableEq X] [Fintype σ] in
/-- The precise nonapproximation premise used by the dual construction follows
from positive approximate degree; it is not an additional assumption. -/
theorem no_approximation_below_degree (coords : X → σ → ℝ) (f : X → ℝ) (ε : ℝ)
    (hd : 0 < approximateDegree coords f ε) :
    ¬ ∃ p : MvPolynomial σ ℝ, p.totalDegree ≤ approximateDegree coords f ε - 1 ∧
      ∀ x, |f x - MvPolynomial.eval (coords x) p| ≤ ε := by
  intro h
  have hle := approximateDegree_le h
  omega

end

end ApproxDegree.BooleanApproxDegree
end

-- ErrorReduction.lean
section
/-!
# Constant-error adjustment

The exact scalar cubic amplifier used by the bit-valued composition proof,
and its construction as a multivariate polynomial with at most nine times
the original total degree. The promise set is arbitrary. These results do
not establish the final approximate-degree composition implication.
-/

namespace ApproxDegree.ErrorReduction

noncomputable def cubic (x : ℝ) : ℝ := (3 * x - x ^ 3) / 2

theorem cubic_neg (x : ℝ) : cubic (-x) = -cubic x := by
  unfold cubic
  ring

theorem cubic_mono {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    cubic a ≤ cubic b := by
  have ha2 : a ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - a by linarith) (show 0 ≤ 1 + a by linarith)]
  have hb2 : b ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - b by linarith) (show 0 ≤ 1 + b by linarith)]
  have hab1 : a * b ≤ 1 := by nlinarith [sq_nonneg (a - b)]
  have hfactor : 0 ≤ (b - a) * (3 - a ^ 2 - a * b - b ^ 2) / 2 := by
    apply div_nonneg
    · exact mul_nonneg (sub_nonneg.mpr hab) (by linarith)
    · norm_num
  have hdiff : cubic b - cubic a =
      (b - a) * (3 - a ^ 2 - a * b - b ^ 2) / 2 := by
    unfold cubic
    ring
  linarith

theorem double_cubic_range {y : ℝ} (hy0 : 1 / 5 ≤ y) (hy1 : y ≤ 1) :
    841861 / 1953125 ≤ cubic (cubic y) ∧ cubic (cubic y) ≤ 1 := by
  have hlo : (37 / 125 : ℝ) ≤ cubic y := by
    have h := cubic_mono (by norm_num : (-1 : ℝ) ≤ 1 / 5) hy0 hy1
    norm_num [cubic] at h ⊢
    exact h
  have hhi : cubic y ≤ 1 := by
    have h := cubic_mono (show -1 ≤ y by linarith) hy1 (le_refl (1 : ℝ))
    norm_num [cubic] at h ⊢
    exact h
  constructor
  · have h := cubic_mono (by norm_num : (-1 : ℝ) ≤ 37 / 125) hlo hhi
    norm_num [cubic] at h ⊢
    exact h
  · have h := cubic_mono (show -1 ≤ cubic y by linarith) hhi (le_refl (1 : ℝ))
    norm_num [cubic] at h ⊢
    exact h

noncomputable def bitAmplifier (p : ℝ) : ℝ := cubic (cubic ((3 / 5) * (2 * p - 1)))

theorem bitAmplifier_reflect (p : ℝ) : bitAmplifier (1 - p) = -bitAmplifier p := by
  unfold bitAmplifier
  have h : (3 / 5 : ℝ) * (2 * (1 - p) - 1) = -((3 / 5) * (2 * p - 1)) := by ring
  rw [h, cubic_neg, cubic_neg]

theorem bitAmplifier_accepting {p : ℝ} (hp0 : 2 / 3 ≤ p) (hp1 : p ≤ 4 / 3) :
    |bitAmplifier p| ≤ 1 ∧ |bitAmplifier p - 1| < 3 / 5 := by
  have h := double_cubic_range (y := (3 / 5) * (2 * p - 1))
    (by linarith) (by linarith)
  change 841861 / 1953125 ≤ bitAmplifier p ∧ bitAmplifier p ≤ 1 at h
  constructor
  · apply abs_le.mpr
    constructor <;> linarith
  · apply abs_lt.mpr
    constructor <;> linarith

theorem bitAmplifier_rejecting {p : ℝ} (hp0 : -1 / 3 ≤ p) (hp1 : p ≤ 1 / 3) :
    |bitAmplifier p| ≤ 1 ∧ |bitAmplifier p + 1| < 3 / 5 := by
  have h := bitAmplifier_accepting (p := 1 - p) (by linarith) (by linarith)
  rw [bitAmplifier_reflect] at h
  constructor
  · simpa using h.1
  · have he : -bitAmplifier p - 1 = -(bitAmplifier p + 1) := by ring
    simpa only [he, abs_neg] using h.2

/-- The pointwise bit-to-sign improvement used on every promised input. -/
theorem bitAmplifier_error (b : Bool) {p : ℝ}
    (hp : |p - (if b then (1 : ℝ) else 0)| ≤ 1 / 3) :
    |bitAmplifier p| ≤ 1 ∧
      |bitAmplifier p - (if b then (1 : ℝ) else -1)| < 3 / 5 := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, sub_zero] at hp ⊢
    have hb := abs_le.mp hp
    simpa only [sub_neg_eq_add] using bitAmplifier_rejecting (by linarith) (by linarith)
  · simp only [↓reduceIte] at hp ⊢
    have hb := abs_le.mp hp
    exact bitAmplifier_accepting (by linarith) (by linarith)

open MvPolynomial

variable {σ : Type*}

/-- Apply the scalar cubic to a genuine multivariate polynomial. -/
noncomputable def cubicPolynomial (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  C (1 / 2) * (C 3 * p - p ^ 3)

/-- Affine normalization before the two cubics. -/
noncomputable def bitNormalizePolynomial (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  C (3 / 5) * (C 2 * p - C 1)

/-- The double cubic amplifier as a multivariate polynomial. -/
noncomputable def bitAmplifierPolynomial (p : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  cubicPolynomial (cubicPolynomial (bitNormalizePolynomial p))

theorem eval_cubicPolynomial (p : MvPolynomial σ ℝ) (x : σ → ℝ) :
    eval x (cubicPolynomial p) = cubic (eval x p) := by
  simp only [cubicPolynomial, map_mul, map_sub, map_pow, eval_C, cubic]
  ring

theorem eval_bitNormalizePolynomial (p : MvPolynomial σ ℝ) (x : σ → ℝ) :
    eval x (bitNormalizePolynomial p) = (3 / 5) * (2 * eval x p - 1) := by
  simp [bitNormalizePolynomial]

theorem eval_bitAmplifierPolynomial (p : MvPolynomial σ ℝ) (x : σ → ℝ) :
    eval x (bitAmplifierPolynomial p) = bitAmplifier (eval x p) := by
  simp only [bitAmplifierPolynomial, eval_cubicPolynomial,
    eval_bitNormalizePolynomial, bitAmplifier]

theorem totalDegree_C_mul_le (c : ℝ) (p : MvPolynomial σ ℝ) :
    (C c * p).totalDegree ≤ p.totalDegree := by
  simpa only [totalDegree_C, zero_add] using totalDegree_mul (C c) p

theorem totalDegree_cubicPolynomial (p : MvPolynomial σ ℝ) :
    (cubicPolynomial p).totalDegree ≤ 3 * p.totalDegree := by
  calc
    (cubicPolynomial p).totalDegree ≤ (C 3 * p - p ^ 3).totalDegree :=
      totalDegree_C_mul_le _ _
    _ ≤ max (C 3 * p).totalDegree (p ^ 3).totalDegree := totalDegree_sub _ _
    _ ≤ max p.totalDegree (3 * p.totalDegree) :=
      max_le_max (totalDegree_C_mul_le _ _) (totalDegree_pow p 3)
    _ = 3 * p.totalDegree := max_eq_right (by omega)

theorem totalDegree_bitNormalizePolynomial (p : MvPolynomial σ ℝ) :
    (bitNormalizePolynomial p).totalDegree ≤ p.totalDegree := by
  calc
    (bitNormalizePolynomial p).totalDegree ≤ (C 2 * p - C 1).totalDegree :=
      totalDegree_C_mul_le _ _
    _ ≤ (C 2 * p).totalDegree := totalDegree_sub_C_le _ _
    _ ≤ p.totalDegree := totalDegree_C_mul_le _ _

theorem totalDegree_bitAmplifierPolynomial (p : MvPolynomial σ ℝ) :
    (bitAmplifierPolynomial p).totalDegree ≤ 9 * p.totalDegree := by
  have h₁ := totalDegree_cubicPolynomial (cubicPolynomial (bitNormalizePolynomial p))
  have h₂ := totalDegree_cubicPolynomial (bitNormalizePolynomial p)
  have h₃ := totalDegree_bitNormalizePolynomial p
  change (cubicPolynomial (cubicPolynomial (bitNormalizePolynomial p))).totalDegree ≤
    9 * p.totalDegree
  omega

/-- Degree and pointwise bounds on an arbitrary promise set, with no requirement
on the starting polynomial or the constructed polynomial off that set. -/
theorem exists_bit_to_sign_polynomial (Ω : Set (σ → ℝ)) (b : (σ → ℝ) → Bool)
    (p : MvPolynomial σ ℝ) {D : ℕ} (hdegree : p.totalDegree ≤ D)
    (herror : ∀ x ∈ Ω, |eval x p - (if b x then (1 : ℝ) else 0)| ≤ 1 / 3) :
    ∃ q : MvPolynomial σ ℝ, q.totalDegree ≤ 9 * D ∧
      (∀ x, eval x q = bitAmplifier (eval x p)) ∧
      (∀ x ∈ Ω, |eval x q| ≤ 1 ∧
        |eval x q - (if b x then (1 : ℝ) else -1)| < 3 / 5) := by
  refine ⟨bitAmplifierPolynomial p, ?_, eval_bitAmplifierPolynomial p, ?_⟩
  · exact (totalDegree_bitAmplifierPolynomial p).trans (Nat.mul_le_mul_left 9 hdegree)
  · intro x hx
    rw [eval_bitAmplifierPolynomial]
    exact bitAmplifier_error (b x) (herror x hx)

end ApproxDegree.ErrorReduction
end

-- CompositionDefinitions.lean
section
/-!
# Boolean composition and the polynomial used in the lower bound

The outer function is total on its Boolean cube. The inner domain is any finite
type injected into a Boolean cube, and composition uses its full product domain.
-/

namespace ApproxDegree.CompositionDefinitions

noncomputable section

variable {Y σ ι : Type*}

def bitDegree (coords : Y → σ → Bool) (g : Y → Bool) : ℕ :=
  BooleanApproxDegree.approximateDegree (BooleanApproxDegree.realCoords coords)
    (fun y => BooleanApproxDegree.bitValue (g y)) (1 / 3)

def productCoords (coords : Y → σ → Bool) (x : ι → Y) (j : ι × σ) : Bool :=
  coords (x j.1) j.2

def blockCompose (f : (ι → Bool) → Bool) (g : Y → Bool) (x : ι → Y) : Bool :=
  f fun i => g (x i)

def outerSign (f : (ι → Bool) → Bool) (b : ι → Bool) : ℝ := if f b then 1 else -1

theorem productCoords_injective (coords : Y → σ → Bool) (hinj : Function.Injective coords) :
    Function.Injective (productCoords (ι := ι) coords) := by
  intro x y h
  funext i
  apply hinj
  funext j
  exact congrFun h (i, j)

theorem real_productCoords (coords : Y → σ → Bool) (x : ι → Y) (j : ι × σ) :
    BooleanApproxDegree.realCoords (productCoords coords) x j =
      BooleanApproxDegree.realCoords coords (x j.1) j.2 := rfl

variable [Fintype Y] [DecidableEq Y] [Fintype σ] [Fintype ι] [DecidableEq ι]

/-- Choose an actual minimum-degree approximant on the entire product promise. -/
theorem exists_minimal_composite_polynomial (coords : Y → σ → Bool)
    (hinj : Function.Injective coords) (f : (ι → Bool) → Bool) (g : Y → Bool) :
    ∃ p : MvPolynomial (ι × σ) ℝ,
      p.totalDegree ≤ bitDegree (productCoords coords) (blockCompose f g) ∧
      ∀ x : ι → Y,
        |BooleanApproxDegree.bitValue (blockCompose f g x) -
          MvPolynomial.eval (BooleanApproxDegree.realCoords (productCoords coords) x) p| ≤ 1 / 3 :=
  BooleanApproxDegree.exists_approximation_at_degree (productCoords coords)
    (productCoords_injective coords hinj)
    (fun x => BooleanApproxDegree.bitValue (blockCompose f g x)) (1 / 3) (by norm_num)

omit [Fintype Y] [DecidableEq Y] [Fintype σ] [Fintype ι] [DecidableEq ι] in
/-- The actual double-cubic polynomial has degree at most nine times the
starting degree, norm at most one, and sign error strictly below three fifths. -/
theorem amplified_composite_bounds (coords : Y → σ → Bool)
    (f : (ι → Bool) → Bool) (g : Y → Bool) (p : MvPolynomial (ι × σ) ℝ)
    {D : ℕ} (hdeg : p.totalDegree ≤ D)
    (herr : ∀ x : ι → Y,
      |BooleanApproxDegree.bitValue (blockCompose f g x) -
        MvPolynomial.eval (BooleanApproxDegree.realCoords (productCoords coords) x) p| ≤ 1 / 3) :
    (ErrorReduction.bitAmplifierPolynomial p).totalDegree ≤ 9 * D ∧
      ∀ x : ι → Y,
        |MvPolynomial.eval (BooleanApproxDegree.realCoords (productCoords coords) x)
          (ErrorReduction.bitAmplifierPolynomial p)| ≤ 1 ∧
        |MvPolynomial.eval (BooleanApproxDegree.realCoords (productCoords coords) x)
          (ErrorReduction.bitAmplifierPolynomial p) - outerSign f (fun i => g (x i))| < 3 / 5 := by
  constructor
  · exact (ErrorReduction.totalDegree_bitAmplifierPolynomial p).trans
      (Nat.mul_le_mul_left 9 hdeg)
  · intro x
    rw [ErrorReduction.eval_bitAmplifierPolynomial]
    apply ErrorReduction.bitAmplifier_error (blockCompose f g x)
    simpa only [BooleanApproxDegree.bitValue, abs_sub_comm] using herr x

end

end ApproxDegree.CompositionDefinitions
end

-- Compression.lean
section
/-!
# Compression of mixed commutators

The manuscript compresses through a subspace that reduces each crossing
operator. It does not assume that the polynomial multiplier preserves the
subspace. This module proves the relevant algebra for arbitrary rectangular
matrices and arbitrary words of operators, over any ring.

The two intertwining hypotheses must still be supplied by the singular-pair
construction. No claim about their existence or an operator norm is made here.
-/

namespace ApproxDegree

variable {R n m ι : Type*} [Ring R] [Fintype n] [Fintype m]

def matrixCommutator (A T : Matrix n n R) : Matrix n n R := A * T - T * A

theorem compress_commutator
    (W : Matrix m n R) (V : Matrix n m R)
    (A : Matrix n n R) (B : Matrix m m R) (T : Matrix n n R)
    (hleft : W * A = B * W) (hright : A * V = V * B) :
    W * matrixCommutator A T * V = matrixCommutator B (W * T * V) := by
  unfold matrixCommutator
  calc
    W * (A * T - T * A) * V = W * (A * T) * V - W * (T * A) * V := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    _ = (W * A) * T * V - (W * T) * (A * V) := by
      simp only [Matrix.mul_assoc]
    _ = (B * W) * T * V - (W * T) * (V * B) := by rw [hleft, hright]
    _ = B * (W * T * V) - (W * T * V) * B := by
      simp only [Matrix.mul_assoc]

def mixedMatrixCommutator (A : ι → Matrix n n R) (word : List ι)
    (T : Matrix n n R) : Matrix n n R :=
  word.foldr (fun i U => matrixCommutator (A i) U) T

theorem compress_mixed_commutators
    (W : Matrix m n R) (V : Matrix n m R)
    (A : ι → Matrix n n R) (B : ι → Matrix m m R)
    (hleft : ∀ i, W * A i = B i * W)
    (hright : ∀ i, A i * V = V * B i)
    (word : List ι) (T : Matrix n n R) :
    W * mixedMatrixCommutator A word T * V =
      mixedMatrixCommutator B word (W * T * V) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    change W * matrixCommutator (A i) (mixedMatrixCommutator A word T) * V =
      matrixCommutator (B i) (mixedMatrixCommutator B word (W * T * V))
    rw [compress_commutator W V (A i) (B i) _ (hleft i) (hright i), ih]

section Scalar

variable {K : Type*} [CommRing K]

theorem matrixCommutator_smul_left (c : K) (A T : Matrix n n K) :
    matrixCommutator (c • A) T = c • matrixCommutator A T := by
  simp only [matrixCommutator, Matrix.smul_mul, Matrix.mul_smul, smul_sub]

theorem matrixCommutator_smul_right (c : K) (A T : Matrix n n K) :
    matrixCommutator A (c • T) = c • matrixCommutator A T := by
  simp only [matrixCommutator, Matrix.smul_mul, Matrix.mul_smul, smul_sub]

/-- Scaling each local crossing by c contributes exactly c to the power of
the number of crossings. The word need not have distinct indices. -/
theorem mixedMatrixCommutator_smul (c : K) (A : ι → Matrix n n K)
    (word : List ι) (T : Matrix n n K) :
    mixedMatrixCommutator (fun i => c • A i) word T =
      c ^ word.length • mixedMatrixCommutator A word T := by
  induction word with
  | nil => simp [mixedMatrixCommutator]
  | cons i word ih =>
    change matrixCommutator (c • A i)
      (mixedMatrixCommutator (fun i => c • A i) word T) =
        c ^ (word.length + 1) • matrixCommutator (A i)
          (mixedMatrixCommutator A word T)
    rw [ih, matrixCommutator_smul_left, matrixCommutator_smul_right,
      smul_smul, pow_succ']

end Scalar

end ApproxDegree
end

-- TensorPhase.lean
section
/-!
# Pauli commutators and the whole Fourier level

All block sets are arbitrary finite types. Matrices use Boolean logical strings
as indices. The reciprocal-bra phase functional is an algebraic Laurent
extension of the normalized physical expectation on the unit circle.
-/

open scoped BigOperators
open Finset

namespace ApproxDegree.TensorPhase

noncomputable section

set_option backward.isDefEq.respectTransparency false

abbrev Bits (ι : Type*) := ι → Bool
abbrev LocalMatrix := Matrix Bool Bool ℂ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tensorMatrix (A : ι → LocalMatrix) : Matrix (Bits ι) (Bits ι) ℂ :=
  fun a b => ∏ i, A i (a i) (b i)

theorem tensorMatrix_mul (A B : ι → LocalMatrix) :
    tensorMatrix A * tensorMatrix B = tensorMatrix (fun i => A i * B i) := by
  ext a b
  change (∑ x : Bits ι, (∏ i, A i (a i) (x i)) * (∏ i, B i (x i) (b i))) =
    ∏ i, ∑ x : Bool, A i (a i) x * B i x (b i)
  simp_rw [← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => A i (a i) x * B i x (b i))).symm

theorem tensorMatrix_update_entry (A : ι → LocalMatrix) (i : ι)
    (B : LocalMatrix) (a b : Bits ι) :
    tensorMatrix (Function.update A i B) a b =
      B (a i) (b i) * ∏ j ∈ univ.erase i, A j (a j) (b j) := by
  unfold tensorMatrix
  rw [← mul_prod_erase univ (fun j => Function.update A i B j (a j) (b j)) (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (mem_erase.mp hj).1]

theorem tensorMatrix_update_sub (A : ι → LocalMatrix) (i : ι) (B C : LocalMatrix) :
    tensorMatrix (Function.update A i B) - tensorMatrix (Function.update A i C) =
      tensorMatrix (Function.update A i (B - C)) := by
  ext a b
  simp only [Matrix.sub_apply, tensorMatrix_update_entry]
  ring

def localLift (i : ι) (B : LocalMatrix) : Matrix (Bits ι) (Bits ι) ℂ :=
  tensorMatrix (fun j => if j = i then B else 1)

theorem localLift_commutator (A : ι → LocalMatrix) (i : ι) (B : LocalMatrix) :
    matrixCommutator (localLift i B) (tensorMatrix A) =
      tensorMatrix (Function.update A i (matrixCommutator B (A i))) := by
  have hleft : (fun j => (if j = i then B else 1) * A j) =
      Function.update A i (B * A i) := by
    funext j
    by_cases h : j = i <;> simp [h]
  have hright : (fun j => A j * (if j = i then B else 1)) =
      Function.update A i (A i * B) := by
    funext j
    by_cases h : j = i <;> simp [h]
  unfold matrixCommutator localLift
  rw [tensorMatrix_mul, tensorMatrix_mul, hleft, hright, tensorMatrix_update_sub]

def pauliX : LocalMatrix := fun a b => if a = b then 0 else 1
def pauliZ : LocalMatrix := fun a b => if a = b then (if a then -1 else 1) else 0
def localX (i : ι) : Matrix (Bits ι) (Bits ι) ℂ := localLift i pauliX

/-- Distinct local X commutators act on exactly their own tensor factors. -/
theorem mixed_commutator_tensor (A : ι → LocalMatrix) (word : List ι)
    (hword : word.Nodup) :
    mixedMatrixCommutator localX word (tensorMatrix A) =
      tensorMatrix (fun i => if i ∈ word then matrixCommutator pauliX (A i) else A i) := by
  induction word with
  | nil => simp [mixedMatrixCommutator]
  | cons i word ih =>
    obtain ⟨hin, hn⟩ := List.nodup_cons.mp hword
    change matrixCommutator (localX i)
      (mixedMatrixCommutator localX word (tensorMatrix A)) = _
    rw [ih hn]
    unfold localX
    rw [localLift_commutator]
    congr 1
    funext j
    by_cases hji : j = i
    · subst j
      simp [hin]
    · simp [hji]

def localBra (z t : ℂ) (a : Bool) : ℂ := if a then z * t⁻¹ else 1
def localKet (z t : ℂ) (b : Bool) : ℂ := if b then z * t else 1
def phaseBra (z : ι → ℂ) (t : ℂ) (a : Bits ι) : ℂ := ∏ i, localBra (z i) t (a i)
def phaseKet (z : ι → ℂ) (t : ℂ) (b : Bits ι) : ℂ := ∏ i, localKet (z i) t (b i)

def phaseExpectation (z : ι → ℂ) (t : ℂ) :
    Matrix (Bits ι) (Bits ι) ℂ →ₗ[ℂ] ℂ where
  toFun T := ((2 : ℂ) ^ Fintype.card ι)⁻¹ *
    ∑ a, ∑ b, phaseBra z t a * T a b * phaseKet z t b
  map_add' T U := by
    simp only [Matrix.add_apply, mul_add, add_mul, sum_add_distrib]
  map_smul' c T := by
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [show ∀ a b, phaseBra z t a * (c * T a b) * phaseKet z t b =
        c * (phaseBra z t a * T a b * phaseKet z t b) by intros; ring]
    simp_rw [← mul_sum]
    ring

def localExpectation (z t : ℂ) (A : LocalMatrix) : ℂ :=
  (2 : ℂ)⁻¹ * ∑ a, ∑ b, localBra z t a * A a b * localKet z t b

theorem phaseExpectation_tensor (z : ι → ℂ) (t : ℂ) (A : ι → LocalMatrix) :
    phaseExpectation z t (tensorMatrix A) = ∏ i, localExpectation (z i) t (A i) := by
  have hraw :
      (∑ a : Bits ι, ∑ b : Bits ι,
        phaseBra z t a * tensorMatrix A a b * phaseKet z t b) =
      ∏ i, ∑ a : Bool, ∑ b : Bool, localBra (z i) t a * A i a b * localKet (z i) t b := by
    simp only [phaseBra, phaseKet, tensorMatrix]
    simp_rw [← prod_mul_distrib]
    calc
      _ = ∑ a : Bits ι, ∏ i, ∑ b : Bool,
          localBra (z i) t (a i) * A i (a i) b * localKet (z i) t b := by
        apply sum_congr rfl
        intro a ha
        exact (Fintype.prod_sum (fun i b =>
          localBra (z i) t (a i) * A i (a i) b * localKet (z i) t b)).symm
      _ = _ := (Fintype.prod_sum (fun i a =>
        ∑ b : Bool, localBra (z i) t a * A i a b * localKet (z i) t b)).symm
  change ((2 : ℂ) ^ Fintype.card ι)⁻¹ * _ = _
  rw [hraw]
  simp only [localExpectation, prod_mul_distrib, prod_const, card_univ, inv_pow]

theorem localExpectation_one {z t : ℂ} (hz : z * z = 1) (ht : t ≠ 0) :
    localExpectation z t 1 = 1 := by
  simp [localExpectation, localBra, localKet, Matrix.one_apply]
  field_simp
  linear_combination hz

theorem localExpectation_Z {z t : ℂ} (hz : z * z = 1) (ht : t ≠ 0) :
    localExpectation z t pauliZ = 0 := by
  simp [localExpectation, localBra, localKet, pauliZ]
  field_simp
  linear_combination -hz

theorem localExpectation_commutator_XZ (z t : ℂ) :
    localExpectation z t (matrixCommutator pauliX pauliZ) = z * (t⁻¹ - t) := by
  simp [localExpectation, localBra, localKet, pauliX, pauliZ,
    matrixCommutator, Matrix.mul_apply]
  ring

theorem localExpectation_commutator_Xone (z t : ℂ) :
    localExpectation z t (matrixCommutator pauliX 1) = 0 := by
  simp [matrixCommutator, localExpectation]

def walshMatrix (T : Finset ι) : Matrix (Bits ι) (Bits ι) ℂ :=
  tensorMatrix (fun i => if i ∈ T then pauliZ else 1)

def mixedSet (S : Finset ι) (T : Matrix (Bits ι) (Bits ι) ℂ) :=
  mixedMatrixCommutator localX S.toList T

/-- A single tensor Walsh term survives exactly when its support is the crossing set. -/
theorem expectation_mixed_walsh (z : ι → ℂ) {t : ℂ}
    (hz : ∀ i, z i * z i = 1) (ht : t ≠ 0) (S T : Finset ι) :
    phaseExpectation z t (mixedSet S (walshMatrix T)) =
      if S = T then (t⁻¹ - t) ^ S.card * ∏ i ∈ S, z i else 0 := by
  unfold mixedSet walshMatrix
  rw [mixed_commutator_tensor _ _ (nodup_toList S), phaseExpectation_tensor]
  simp only [mem_toList]
  have hlocal : ∀ i,
      localExpectation (z i) t
        (if i ∈ S then matrixCommutator pauliX (if i ∈ T then pauliZ else 1)
          else if i ∈ T then pauliZ else 1) =
      if i ∈ S then (if i ∈ T then z i * (t⁻¹ - t) else 0)
        else if i ∈ T then 0 else 1 := by
    intro i
    by_cases hs : i ∈ S <;> by_cases hT : i ∈ T <;>
      simp [hs, hT, localExpectation_commutator_XZ,
        localExpectation_commutator_Xone, localExpectation_Z (hz i) ht,
        localExpectation_one (hz i) ht]
  simp_rw [hlocal]
  by_cases hST : S = T
  · subst T
    simp only [if_true]
    have hfac : ∀ i, (if i ∈ S then if i ∈ S then z i * (t⁻¹ - t) else 0
        else if i ∈ S then 0 else 1) = if i ∈ S then z i * (t⁻¹ - t) else 1 := by
      intro i
      split_ifs <;> rfl
    simp_rw [hfac]
    rw [Fintype.prod_ite_mem]
    simp [prod_mul_distrib, mul_comm]
  · rw [if_neg hST]
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      exact not_forall.mp (fun h => hST (Finset.ext h))
    apply prod_eq_zero (mem_univ i)
    by_cases hs : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

def commutatorMap (A : Matrix (Bits ι) (Bits ι) ℂ) :
    Matrix (Bits ι) (Bits ι) ℂ →ₗ[ℂ] Matrix (Bits ι) (Bits ι) ℂ where
  toFun := matrixCommutator A
  map_add' T U := by
    simp only [matrixCommutator, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c T := matrixCommutator_smul_right c A T

def mixedMap : List ι → Matrix (Bits ι) (Bits ι) ℂ →ₗ[ℂ] Matrix (Bits ι) (Bits ι) ℂ
  | [] => LinearMap.id
  | i :: word => (commutatorMap (localX i)).comp (mixedMap word)

theorem mixedMap_apply (word : List ι) (T : Matrix (Bits ι) (Bits ι) ℂ) :
    mixedMap word T = mixedMatrixCommutator localX word T := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    change matrixCommutator (localX i) (mixedMap word T) =
      matrixCommutator (localX i) (mixedMatrixCommutator localX word T)
    rw [ih]

/-- An arbitrary finite Walsh expansion as its actual diagonal tensor matrix. -/
def fourierMatrix (c : Finset ι → ℂ) : Matrix (Bits ι) (Bits ι) ℂ :=
  ∑ T : Finset ι, c T • walshMatrix T

def bitSign (a : Bool) : ℂ := if a then -1 else 1

omit [DecidableEq ι] in
theorem tensorMatrix_diagonal (f : ι → Bool → ℂ) :
    tensorMatrix (fun i => Matrix.diagonal (f i)) =
      Matrix.diagonal (fun a : Bits ι => ∏ i, f i (a i)) := by
  ext a b
  by_cases hab : a = b
  · subst b
    simp [tensorMatrix]
  · simp only [tensorMatrix, Matrix.diagonal_apply, if_neg hab]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i :=
      not_forall.mp (fun h => hab (funext h))
    apply prod_eq_zero (mem_univ i)
    simp [hi]

theorem walshMatrix_diagonal (T : Finset ι) :
    walshMatrix T = Matrix.diagonal (fun a : Bits ι => ∏ i ∈ T, bitSign (a i)) := by
  have hf : (fun i => if i ∈ T then pauliZ else (1 : LocalMatrix)) =
      (fun i => Matrix.diagonal (fun a => if i ∈ T then bitSign a else 1)) := by
    funext i
    ext a b
    by_cases hi : i ∈ T <;> cases a <;> cases b <;>
      simp [hi, pauliZ, bitSign]
  unfold walshMatrix
  rw [hf, tensorMatrix_diagonal]
  congr 1
  funext a
  exact Fintype.prod_ite_mem T (fun i => bitSign (a i))

/-- The arbitrary Walsh expansion is genuinely the diagonal multiplier of
the corresponding function on the logical Boolean cube. -/
theorem fourierMatrix_diagonal (c : Finset ι → ℂ) :
    fourierMatrix c = Matrix.diagonal
      (fun a : Bits ι => ∑ T : Finset ι, c T * ∏ i ∈ T, bitSign (a i)) := by
  ext a b
  by_cases hab : a = b <;>
    simp [fourierMatrix, walshMatrix_diagonal,
      Matrix.sum_apply, Matrix.smul_apply, hab]

def fourierLevel (k : ℕ) (c : Finset ι → ℂ) (z : ι → ℂ) : ℂ :=
  ∑ S ∈ univ.filter (fun S : Finset ι => S.card = k), c S * ∏ i ∈ S, z i

/-- Exact extraction for one fixed crossing set from arbitrary Walsh coefficients. -/
theorem expectation_mixed_fourier (z : ι → ℂ) {t : ℂ}
    (hz : ∀ i, z i * z i = 1) (ht : t ≠ 0)
    (c : Finset ι → ℂ) (S : Finset ι) :
    phaseExpectation z t (mixedSet S (fourierMatrix c)) =
      (t⁻¹ - t) ^ S.card * (c S * ∏ i ∈ S, z i) := by
  unfold mixedSet fourierMatrix
  rw [← mixedMap_apply, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul, mixedMap_apply]
  change (∑ T : Finset ι, c T * phaseExpectation z t (mixedSet S (walshMatrix T))) = _
  simp_rw [expectation_mixed_walsh z hz ht]
  rw [sum_eq_single S]
  · simp
    ring
  · intro T hT hTS
    simp [Ne.symm hTS]
  · intro hS
    exact (hS (mem_univ S)).elim

/-- The whole homogeneous Fourier level, with no hypothesis on its coefficients.
This holds for every finite block type and every natural k, including k=0
and k larger than the number of blocks. -/
theorem expectation_mixed_fourier_level (z : ι → ℂ) {t : ℂ}
    (hz : ∀ i, z i * z i = 1) (ht : t ≠ 0)
    (c : Finset ι → ℂ) (k : ℕ) :
    phaseExpectation z t
      (∑ S ∈ univ.filter (fun S : Finset ι => S.card = k),
        mixedSet S (fourierMatrix c)) =
      (t⁻¹ - t) ^ k * fourierLevel k c z := by
  rw [map_sum]
  unfold fourierLevel
  rw [mul_sum]
  apply sum_congr rfl
  intro S hS
  rw [expectation_mixed_fourier z hz ht, (mem_filter.mp hS).2]

def bitWeight (a : Bits ι) : ℕ := (univ.filter (fun i => a i = true)).card
def phaseSign (z : ι → ℂ) (a : Bits ι) : ℂ := ∏ i, if a i then z i else 1

omit [DecidableEq ι] in
theorem phaseBra_eq (z : ι → ℂ) (t : ℂ) (a : Bits ι) :
    phaseBra z t a = phaseSign z a * (t⁻¹) ^ bitWeight a := by
  have hfac : ∀ i, localBra (z i) t (a i) =
      (if a i then z i else 1) * (if a i then t⁻¹ else 1) := by
    intro i
    cases a i <;> simp [localBra]
  unfold phaseBra
  simp_rw [hfac]
  rw [prod_mul_distrib]
  simp [phaseSign, bitWeight, prod_ite]

omit [DecidableEq ι] in
theorem phaseKet_eq (z : ι → ℂ) (t : ℂ) (a : Bits ι) :
    phaseKet z t a = phaseSign z a * t ^ bitWeight a := by
  have hfac : ∀ i, localKet (z i) t (a i) =
      (if a i then z i else 1) * (if a i then t else 1) := by
    intro i
    cases a i <;> simp [localKet]
  unfold phaseKet
  simp_rw [hfac]
  rw [prod_mul_distrib]
  simp [phaseSign, bitWeight, prod_ite]

def phaseCoefficient (z : ι → ℂ) (T : Matrix (Bits ι) (Bits ι) ℂ)
    (a b : Bits ι) : ℂ :=
  ((2 : ℂ) ^ Fintype.card ι)⁻¹ * phaseSign z a * phaseSign z b * T a b

/-- The t-independent coefficient form needed to connect logical distance
to the frequency bound in the common-phase remainder argument. -/
theorem phaseExpectation_eq_weight_sum (z : ι → ℂ) {t : ℂ} (ht : t ≠ 0)
    (T : Matrix (Bits ι) (Bits ι) ℂ) :
    phaseExpectation z t T =
      ∑ a : Bits ι, ∑ b : Bits ι, phaseCoefficient z T a b *
        t ^ ((bitWeight b : ℤ) - (bitWeight a : ℤ)) := by
  change ((2 : ℂ) ^ Fintype.card ι)⁻¹ *
    (∑ a : Bits ι, ∑ b : Bits ι, phaseBra z t a * T a b * phaseKet z t b) = _
  rw [mul_sum]
  apply sum_congr rfl
  intro a ha
  rw [mul_sum]
  apply sum_congr rfl
  intro b hb
  rw [phaseBra_eq, phaseKet_eq, zpow_sub₀ ht, zpow_natCast, zpow_natCast]
  unfold phaseCoefficient
  rw [div_eq_mul_inv, inv_pow]
  ring

end

end ApproxDegree.TensorPhase
end

-- FiberChannel.lean
section
/-!
# The positive exact-fiber product channel

The embedding is constructed from actual normalized vectors on the two fibers.
The channel weights are actual squared complex norms. No matrix operator-norm
convention or bound is used in this module.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace ApproxDegree.FiberChannel

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Y ι : Type*} [Fintype Y] [Fintype ι] [DecidableEq Y] [DecidableEq ι]

abbrev Raw (ι Y : Type*) := ι → Y
abbrev Bits (ι : Type*) := ι → Bool

def productLabel (g : Y → Bool) (x : Raw ι Y) : Bits ι := fun i => g (x i)

def productV (u : Bool → Y → ℂ) : Matrix (Raw ι Y) (Bits ι) ℂ :=
  fun x b => ∏ i, u (b i) (x i)

def productW (u : Bool → Y → ℂ) : Matrix (Bits ι) (Raw ι Y) ℂ :=
  Matrix.conjTranspose (productV (ι := ι) u)

def weights (u : Bool → Y → ℂ) (b : Bits ι) (x : Raw ι Y) : ℝ :=
  ∏ i, ‖u (b i) (x i)‖ ^ 2

def channelQ (u : Bool → Y → ℂ) (p : Raw ι Y → ℂ) (b : Bits ι) : ℂ :=
  ∑ x, p x * (weights u b x : ℂ)

omit [Fintype Y] [DecidableEq Y] [DecidableEq ι] in
/-- The product embedding is supported on exactly its indicated logical fiber. -/
theorem productV_support (g : Y → Bool) (u : Bool → Y → ℂ)
    (hsupport : ∀ b y, u b y ≠ 0 → g y = b)
    (x : Raw ι Y) (b : Bits ι) (h : productV u x b ≠ 0) :
    productLabel g x = b := by
  funext i
  apply hsupport (b i) (x i)
  exact (prod_ne_zero_iff.mp h) i (mem_univ i)

omit [Fintype Y] [DecidableEq Y] [DecidableEq ι] in
/-- The adjoint embedding has the matching row-fiber support. -/
theorem productW_support (g : Y → Bool) (u : Bool → Y → ℂ)
    (hsupport : ∀ b y, u b y ≠ 0 → g y = b)
    (b : Bits ι) (x : Raw ι Y) (h : productW u b x ≠ 0) :
    productLabel g x = b := by
  apply productV_support g u hsupport x b
  intro hv
  apply h
  simp [productW, hv]

omit [Fintype Y] [DecidableEq Y] [DecidableEq ι] in
theorem weights_nonnegative (u : Bool → Y → ℂ) (b : Bits ι) (x : Raw ι Y) :
    0 ≤ weights u b x :=
  prod_nonneg (fun _ _ => sq_nonneg _)

omit [Fintype Y] [DecidableEq Y] [DecidableEq ι] in
theorem weights_eq_norm_sq (u : Bool → Y → ℂ) (b : Bits ι) (x : Raw ι Y) :
    weights u b x = ‖productV u x b‖ ^ 2 := by
  simp only [weights, productV, Complex.norm_prod, prod_pow]

omit [Fintype Y] [DecidableEq Y] [DecidableEq ι] in
/-- Positive-weight samples lie in the exact product fiber. -/
theorem weights_support (g : Y → Bool) (u : Bool → Y → ℂ)
    (hsupport : ∀ b y, u b y ≠ 0 → g y = b)
    (b : Bits ι) (x : Raw ι Y) (h : weights u b x ≠ 0) :
    productLabel g x = b := by
  apply productV_support g u hsupport x b
  intro hv
  apply h
  rw [weights_eq_norm_sq, hv]
  simp

omit [DecidableEq Y] in
/-- The weights of every logical product fiber sum to one. -/
theorem weights_sum_one (u : Bool → Y → ℂ)
    (hnorm : ∀ b, ∑ y, ‖u b y‖ ^ 2 = 1) (b : Bits ι) :
    ∑ x : Raw ι Y, weights u b x = 1 := by
  unfold weights
  calc
    (∑ x : Raw ι Y, ∏ i, ‖u (b i) (x i)‖ ^ 2) =
        ∏ i, ∑ y : Y, ‖u (b i) y‖ ^ 2 :=
      (Fintype.prod_sum (fun i y => ‖u (b i) y‖ ^ 2)).symm
    _ = 1 := by simp only [hnorm, prod_const_one]

omit [Fintype Y] [DecidableEq Y] [DecidableEq ι] in
/-- A diagonal entry of the Gram matrix is its actual norm-square weight. -/
theorem adjoint_product_eq_weight (u : Bool → Y → ℂ) (b : Bits ι) (x : Raw ι Y) :
    productW u b x * productV u x b = (weights u b x : ℂ) := by
  simp only [productW, Matrix.conjTranspose_apply, Complex.star_def]
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, weights_eq_norm_sq]

/-- Actual matrix compression equals the positive exact-fiber expectation. -/
theorem compress_diagonal (g : Y → Bool) (u : Bool → Y → ℂ)
    (hsupport : ∀ b y, u b y ≠ 0 → g y = b) (p : Raw ι Y → ℂ) :
    productW u * Matrix.diagonal p * productV u = Matrix.diagonal (channelQ u p) := by
  classical
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  by_cases hab : a = b
  · subst b
    simp only [Matrix.diagonal_apply_eq, channelQ]
    apply sum_congr rfl
    intro x hx
    calc
      productW u a x * p x * productV u x a =
          p x * (productW u a x * productV u x a) := by ring
      _ = _ := by rw [adjoint_product_eq_weight]
  · simp only [Matrix.diagonal_apply, if_neg hab]
    apply sum_eq_zero
    intro x hx
    by_cases hw : productW u a x = 0
    · simp [hw]
    by_cases hv : productV u x b = 0
    · simp [hv]
    exact (hab ((productW_support g u hsupport a x hw).symm.trans
      (productV_support g u hsupport x b hv))).elim

omit [DecidableEq Y] in
theorem channelQ_one (u : Bool → Y → ℂ)
    (hnorm : ∀ b, ∑ y, ‖u b y‖ ^ 2 = 1) (b : Bits ι) :
    channelQ u (fun _ => 1) b = 1 := by
  unfold channelQ
  simp only [one_mul]
  calc
    (∑ x, (weights u b x : ℂ)) = Complex.ofRealHom (∑ x, weights u b x) :=
      (map_sum Complex.ofRealHom (fun x => weights u b x) univ).symm
    _ = 1 := by rw [weights_sum_one u hnorm]; rfl

/-- Normalized disjoint-fiber vectors give an actual orthonormal product code.
This is a Gram-matrix identity, not a default matrix norm assertion. -/
theorem productW_mul_productV (g : Y → Bool) (u : Bool → Y → ℂ)
    (hsupport : ∀ b y, u b y ≠ 0 → g y = b)
    (hnorm : ∀ b, ∑ y, ‖u b y‖ ^ 2 = 1) :
    productW (ι := ι) u * productV (ι := ι) u = 1 := by
  classical
  have h := compress_diagonal (ι := ι) g u hsupport (fun _ => 1)
  have hQ : channelQ u (fun _ : Raw ι Y => 1) = fun _ : Bits ι => 1 := by
    funext b
    exact channelQ_one u hnorm b
  rw [hQ] at h
  simpa only [Matrix.diagonal_one, Matrix.mul_one] using h

end

end ApproxDegree.FiberChannel
end

-- WalshReconstruction.lean
section
/-!
# Exact Walsh reconstruction of an arbitrary logical function

The coefficients are constructed by finite averaging, and their matrix
representation is proved using the full character inversion kernel.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace ApproxDegree.WalshReconstruction

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def character (S : Finset ι) (a : TensorPhase.Bits ι) : ℂ :=
  ∏ i ∈ S, TensorPhase.bitSign (a i)

/-- The normalized finite Walsh transform of an arbitrary function. -/
def coefficient (Q : TensorPhase.Bits ι → ℂ) (S : Finset ι) : ℂ :=
  ((2 : ℂ) ^ Fintype.card ι)⁻¹ * ∑ a, Q a * character S a

/-- Summing all Walsh characters gives the exact delta kernel. -/
theorem character_kernel (a b : TensorPhase.Bits ι) :
    ∑ S : Finset ι, character S a * character S b =
      if a = b then (2 : ℂ) ^ Fintype.card ι else 0 := by
  have hp : (∑ S : Finset ι, character S a * character S b) =
      ∏ i, (TensorPhase.bitSign (a i) * TensorPhase.bitSign (b i) + 1) := by
    simp only [character, ← prod_mul_distrib]
    symm
    simpa only [prod_const_one, mul_one] using
      Fintype.prod_add (fun i => TensorPhase.bitSign (a i) * TensorPhase.bitSign (b i))
        (fun _ => (1 : ℂ))
  rw [hp]
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    have hlocal : ∀ i, TensorPhase.bitSign (a i) * TensorPhase.bitSign (a i) + 1 = 2 := by
      intro i
      cases a i <;> norm_num [TensorPhase.bitSign]
    simp only [hlocal, prod_const, card_univ]
  · rw [if_neg hab]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := not_forall.mp (fun h => hab (funext h))
    apply prod_eq_zero (mem_univ i)
    cases ha : a i <;> cases hb : b i <;> simp_all [TensorPhase.bitSign]

/-- Exact Walsh inversion on every finite Boolean cube, including dimension zero. -/
theorem reconstruct (Q : TensorPhase.Bits ι → ℂ) (b : TensorPhase.Bits ι) :
    ∑ S : Finset ι, coefficient Q S * character S b = Q b := by
  have heach : ∀ S, coefficient Q S * character S b =
      ((2 : ℂ) ^ Fintype.card ι)⁻¹ * ∑ a, Q a * (character S a * character S b) := by
    intro S
    simp only [coefficient, mul_assoc, sum_mul]
  simp_rw [heach]
  rw [← mul_sum, sum_comm]
  simp_rw [← mul_sum, character_kernel]
  simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
  rw [mul_left_comm, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)), mul_one]

/-- The constructed Walsh coefficients represent the actual diagonal matrix. -/
theorem fourierMatrix_coefficient (Q : TensorPhase.Bits ι → ℂ) :
    TensorPhase.fourierMatrix (coefficient Q) = Matrix.diagonal Q := by
  rw [TensorPhase.fourierMatrix_diagonal]
  congr 1
  funext b
  exact reconstruct Q b

omit [Fintype ι] [DecidableEq ι] in
/-- The real sign characters are fixed by complex conjugation. -/
theorem character_conj (S : Finset ι) (a : TensorPhase.Bits ι) :
    conj (character S a) = character S a := by
  unfold character
  rw [map_prod]
  apply prod_congr rfl
  intro i hi
  cases a i <;> simp [TensorPhase.bitSign]

/-- Fourier transformation preserves conjugation. -/
theorem coefficient_conj (Q : TensorPhase.Bits ι → ℂ) (S : Finset ι) :
    conj (coefficient Q S) = coefficient (fun a => conj (Q a)) S := by
  have htwo : conj (2 : ℂ) = 2 := Complex.conj_ofReal 2
  simp [coefficient, character_conj, htwo]

/-- In particular the coefficient of a real-valued function is real. -/
theorem coefficient_real (Q : TensorPhase.Bits ι → ℂ)
    (hQ : ∀ a, conj (Q a) = Q a) (S : Finset ι) :
    conj (coefficient Q S) = coefficient Q S := by
  rw [coefficient_conj]
  congr 1
  funext a
  exact hQ a

theorem coefficient_im_eq_zero (Q : TensorPhase.Bits ι → ℂ)
    (hQ : ∀ a, (Q a).im = 0) (S : Finset ι) : (coefficient Q S).im = 0 :=
  Complex.conj_eq_iff_im.mp
    (coefficient_real Q (fun a => Complex.conj_eq_iff_im.mpr (hQ a)) S)

/-- The actual multivariate polynomial obtained by retaining Walsh supports
of cardinality at most `r`. Its variables are logical sign coordinates. -/
def truncation (r : ℕ) (Q : TensorPhase.Bits ι → ℂ) : MvPolynomial ι ℂ :=
  ∑ S ∈ univ.filter (fun S : Finset ι => S.card ≤ r),
    MvPolynomial.C (coefficient Q S) * ∏ i ∈ S, MvPolynomial.X i

/-- The truncation is an actual polynomial of raw total degree at most `r`. -/
theorem truncation_totalDegree_le (r : ℕ) (Q : TensorPhase.Bits ι → ℂ) :
    (truncation r Q).totalDegree ≤ r := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro S hS
  have hcard : S.card ≤ r := (mem_filter.mp hS).2
  calc
    (MvPolynomial.C (coefficient Q S) * ∏ i ∈ S, MvPolynomial.X i).totalDegree ≤
        (MvPolynomial.C (coefficient Q S) : MvPolynomial ι ℂ).totalDegree +
          (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial ι ℂ)).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial ι ℂ)).totalDegree := by
      rw [MvPolynomial.totalDegree_C, zero_add]
    _ ≤ ∑ i ∈ S, (MvPolynomial.X i : MvPolynomial ι ℂ).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ = S.card := by simp
    _ ≤ r := hcard

/-- Evaluation agrees with the retained finite Walsh sum at every input,
and is not restricted to Boolean sign values. -/
theorem truncation_eval (r : ℕ) (Q : TensorPhase.Bits ι → ℂ) (z : ι → ℂ) :
    MvPolynomial.eval z (truncation r Q) =
      ∑ S ∈ univ.filter (fun S : Finset ι => S.card ≤ r),
        coefficient Q S * ∏ i ∈ S, z i := by
  simp [truncation, MvPolynomial.eval_mul]

/-- Retaining all possible support sizes reconstructs the arbitrary function. -/
theorem truncation_eval_eq_of_card_le (r : ℕ) (hr : Fintype.card ι ≤ r)
    (Q : TensorPhase.Bits ι → ℂ) (b : TensorPhase.Bits ι) :
    MvPolynomial.eval (fun i => TensorPhase.bitSign (b i)) (truncation r Q) = Q b := by
  rw [truncation_eval]
  have hfilter : univ.filter (fun S : Finset ι => S.card ≤ r) = univ := by
    apply filter_eq_self.mpr
    intro S hS
    exact (card_le_univ S).trans hr
  rw [hfilter]
  exact reconstruct Q b

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- Actual fiber compression supplies its own Fourier coefficients. This
discharges the compressed-multiplier representation input of extraction. -/
theorem channel_compression (g : Y → Bool) (u : Bool → Y → ℂ)
    (hsupport : ∀ b y, u b y ≠ 0 → g y = b) (p : (ι → Y) → ℂ) :
    FiberChannel.productW u * Matrix.diagonal p * FiberChannel.productV u =
      TensorPhase.fourierMatrix (coefficient (FiberChannel.channelQ u p)) := by
  rw [FiberChannel.compress_diagonal g u hsupport, fourierMatrix_coefficient]

end

end ApproxDegree.WalshReconstruction
end

-- FactorialTail.lean
section
/-!
# Finite factorial tails for the composition candidate

The proof uses `Real.sum_le_exp_of_nonneg`, not an assumed Stirling bound.
Rescaling the exponential series by `8 * exp 1` gives a finite tail at
most `8⁻ʳ`; hence its half is at most `1/16 < 1/15` when `r ≥ 1`.
No Fourier-level or operator hypotheses are assumed in the numerical bound.
-/

namespace ApproxDegree.FactorialTail

open scoped BigOperators
open Finset

/-- A finite interval of nonnegative exponential-series terms is at most
the full exponential, using Mathlib's proved finite-series bound. -/
theorem sum_Ico_le_exp {x : ℝ} (hx : 0 ≤ x) (r N : ℕ) :
    (∑ k ∈ Ico r N, x ^ k / (k.factorial : ℝ)) ≤ Real.exp x := by
  calc
    (∑ k ∈ Ico r N, x ^ k / (k.factorial : ℝ)) ≤
        ∑ k ∈ range N, x ^ k / (k.factorial : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact mem_range.mpr (mem_Ico.mp hk).2
      · intro k _ _
        positivity
    _ ≤ Real.exp x := Real.sum_le_exp_of_nonneg hx N

/-- A finite exponential-series Chernoff estimate. -/
theorem scaled_finite_tail_le_exp {a b : ℝ} (ha : 0 ≤ a) (hb : 1 ≤ b)
    (r N : ℕ) :
    b ^ r * (∑ k ∈ Ico r N, a ^ k / (k.factorial : ℝ)) ≤
      Real.exp (b * a) := by
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb
  calc
    b ^ r * (∑ k ∈ Ico r N, a ^ k / (k.factorial : ℝ)) =
        ∑ k ∈ Ico r N, b ^ r * (a ^ k / (k.factorial : ℝ)) := by
      rw [mul_sum]
    _ ≤ ∑ k ∈ Ico r N, (b * a) ^ k / (k.factorial : ℝ) := by
      apply sum_le_sum
      intro k hk
      have hp : b ^ r ≤ b ^ k := pow_le_pow_right₀ hb (mem_Ico.mp hk).1
      calc
        b ^ r * (a ^ k / (k.factorial : ℝ)) ≤
            b ^ k * (a ^ k / (k.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
        _ = (b * a) ^ k / (k.factorial : ℝ) := by
          rw [mul_pow, mul_div_assoc]
    _ ≤ Real.exp (b * a) := sum_Ico_le_exp (mul_nonneg hb0 ha) r N

/-- The manuscript's cutoff implies a stronger finite-tail bound than its
geometric-ratio calculation requires. The upper endpoint may be arbitrary. -/
theorem finite_tail_le_eighth_pow {a : ℝ} (ha : 0 ≤ a) {r : ℕ}
    (hcut : 8 * Real.exp 1 * a ≤ (r : ℝ)) (N : ℕ) :
    (∑ k ∈ Ico r N, a ^ k / (k.factorial : ℝ)) ≤ (1 / 8 : ℝ) ^ r := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hb : 1 ≤ 8 * Real.exp 1 := by
    have := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
    linarith
  have hscaled := scaled_finite_tail_le_exp ha hb r N
  have hExp : Real.exp (8 * Real.exp 1 * a) ≤ Real.exp (r : ℝ) :=
    Real.exp_le_exp.mpr hcut
  have hden : 0 < (8 * Real.exp 1) ^ r := by positivity
  calc
    (∑ k ∈ Ico r N, a ^ k / (k.factorial : ℝ)) ≤
        Real.exp (r : ℝ) / (8 * Real.exp 1) ^ r := by
      apply (le_div_iff₀ hden).mpr
      simpa only [mul_comm] using hscaled.trans hExp
    _ = (1 / 8 : ℝ) ^ r := by
      have hexp : Real.exp (r : ℝ) = Real.exp 1 ^ r := by
        simp [← Real.exp_nat_mul]
      rw [hexp, ← div_pow]
      congr 1
      field_simp

/-- A universal finite-tail bound sufficient for Fourier truncation. -/
theorem half_finite_tail_le_one_sixteenth {a : ℝ} (ha : 0 ≤ a) {r : ℕ}
    (hcut : 8 * Real.exp 1 * a ≤ (r : ℝ)) (hr : 1 ≤ r) (N : ℕ) :
    (1 / 2 : ℝ) * (∑ k ∈ Ico r N, a ^ k / (k.factorial : ℝ)) ≤ 1 / 16 := by
  have ht := finite_tail_le_eighth_pow ha hcut N
  have hp : (1 / 8 : ℝ) ^ r ≤ 1 / 8 := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
      (by norm_num : (1 / 8 : ℝ) ≤ 1) hr
  linarith

/-- The strict `1/15` estimate in the manuscript, for every finite endpoint. -/
theorem half_finite_tail_lt_one_fifteenth {a : ℝ} (ha : 0 ≤ a) {r : ℕ}
    (hcut : 8 * Real.exp 1 * a ≤ (r : ℝ)) (hr : 1 ≤ r) (N : ℕ) :
    (1 / 2 : ℝ) * (∑ k ∈ Ico r N, a ^ k / (k.factorial : ℝ)) < 1 / 15 := by
  exact (half_finite_tail_le_one_sixteenth ha hcut hr N).trans_lt (by norm_num)

end ApproxDegree.FactorialTail
end

-- FourierTruncation.lean
section
/-!
# A real low-degree approximant from uniform factorial Fourier bounds

The real polynomial, its degree bound, and its omitted-level remainder are
constructed explicitly. The finite tail allows cutoffs beyond the full cube
dimension without a separate nonempty-tail assumption.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace ApproxDegree.FourierTruncation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realSign (b : Bool) : ℝ := if b then -1 else 1
def complexFunction (Q : TensorPhase.Bits ι → ℝ) : TensorPhase.Bits ι → ℂ :=
  fun b => (Q b : ℂ)
def realCoefficient (Q : TensorPhase.Bits ι → ℝ) (S : Finset ι) : ℝ :=
  (WalshReconstruction.coefficient (complexFunction Q) S).re

theorem ofReal_realSign (b : Bool) : (realSign b : ℂ) = TensorPhase.bitSign b := by
  cases b <;> simp [realSign, TensorPhase.bitSign]

/-- Taking the real part loses nothing: the constructed coefficients are real. -/
theorem ofReal_realCoefficient (Q : TensorPhase.Bits ι → ℝ) (S : Finset ι) :
    (realCoefficient Q S : ℂ) = WalshReconstruction.coefficient (complexFunction Q) S := by
  apply Complex.conj_eq_iff_re.mp
  exact WalshReconstruction.coefficient_real _ (fun b => Complex.conj_ofReal (Q b)) S

/-- The actual real polynomial retaining precisely the supports of size below `r`. -/
def realTruncation (r : ℕ) (Q : TensorPhase.Bits ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ S ∈ univ.filter (fun S : Finset ι => S.card < r),
    MvPolynomial.C (realCoefficient Q S) * ∏ i ∈ S, MvPolynomial.X i

theorem realTruncation_totalDegree_lt (r : ℕ) (hr : 1 ≤ r)
    (Q : TensorPhase.Bits ι → ℝ) : (realTruncation r Q).totalDegree < r := by
  have hdegree : (realTruncation r Q).totalDegree ≤ r - 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro S hS
    have hcard : S.card ≤ r - 1 := by have := (mem_filter.mp hS).2; omega
    calc
      (MvPolynomial.C (realCoefficient Q S) * ∏ i ∈ S, MvPolynomial.X i).totalDegree ≤
          (MvPolynomial.C (realCoefficient Q S) : MvPolynomial ι ℝ).totalDegree +
            (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial ι ℝ)).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ = (∏ i ∈ S, (MvPolynomial.X i : MvPolynomial ι ℝ)).totalDegree := by
        rw [MvPolynomial.totalDegree_C, zero_add]
      _ ≤ ∑ i ∈ S, (MvPolynomial.X i : MvPolynomial ι ℝ).totalDegree :=
        MvPolynomial.totalDegree_finsetProd _ _
      _ = S.card := by simp
      _ ≤ r - 1 := hcard
  omega

/-- Its real evaluation embeds as the literal retained complex Walsh sum. -/
theorem realTruncation_eval_cast (r : ℕ) (Q : TensorPhase.Bits ι → ℝ)
    (b : TensorPhase.Bits ι) :
    (MvPolynomial.eval (fun i => realSign (b i)) (realTruncation r Q) : ℂ) =
      ∑ S ∈ univ.filter (fun S : Finset ι => S.card < r),
        WalshReconstruction.coefficient (complexFunction Q) S *
          WalshReconstruction.character S b := by
  simp only [realTruncation, map_sum, map_mul, map_prod, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod,
    ofReal_realCoefficient, ofReal_realSign, WalshReconstruction.character]

omit [DecidableEq ι] in
/-- Grouping omitted supports by their actual cardinalities gives precisely
the homogeneous levels. The identity includes the case `r > card ι`. -/
theorem omitted_supports_eq_levels (c : Finset ι → ℂ) (r : ℕ) (z : ι → ℂ) :
    (∑ S ∈ univ.filter (fun S : Finset ι => r ≤ S.card), c S * ∏ i ∈ S, z i) =
      ∑ k ∈ Ico r (Fintype.card ι + 1), TensorPhase.fourierLevel k c z := by
  symm
  unfold TensorPhase.fourierLevel
  rw [sum_fiberwise_eq_sum_filter]
  have hfilter : univ.filter (fun S : Finset ι => S.card ∈ Ico r (Fintype.card ι + 1)) =
      univ.filter (fun S : Finset ι => r ≤ S.card) := by
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_Ico]
    exact and_iff_left (Nat.lt_succ_of_le (card_le_univ S))
  rw [hfilter]

/-- The remainder is derived from exact reconstruction and the disjoint
partition of all supports into sizes below and above the cutoff. -/
theorem realTruncation_remainder (r : ℕ) (Q : TensorPhase.Bits ι → ℝ)
    (b : TensorPhase.Bits ι) :
    ((Q b - MvPolynomial.eval (fun i => realSign (b i)) (realTruncation r Q) : ℝ) : ℂ) =
      ∑ k ∈ Ico r (Fintype.card ι + 1), TensorPhase.fourierLevel k
        (WalshReconstruction.coefficient (complexFunction Q))
        (fun i => TensorPhase.bitSign (b i)) := by
  rw [Complex.ofReal_sub, realTruncation_eval_cast, ← omitted_supports_eq_levels]
  have hs := sum_filter_add_sum_filter_not (univ : Finset (Finset ι))
    (fun S => S.card < r)
    (fun S => WalshReconstruction.coefficient (complexFunction Q) S *
      WalshReconstruction.character S b)
  simp only [not_lt] at hs
  rw [WalshReconstruction.reconstruct] at hs
  change (Q b : ℂ) - _ = _
  change _ + _ = (Q b : ℂ) at hs
  simp only [WalshReconstruction.character] at hs ⊢
  linear_combination -hs

/-- Beyond the full Fourier degree the tail is empty and reconstruction is exact. -/
theorem realTruncation_exact_of_card_lt (r : ℕ) (hr : Fintype.card ι < r)
    (Q : TensorPhase.Bits ι → ℝ) (b : TensorPhase.Bits ι) :
    Q b = MvPolynomial.eval (fun i => realSign (b i)) (realTruncation r Q) := by
  have h := realTruncation_remainder r Q b
  rw [Ico_eq_empty_of_le (by omega : Fintype.card ι + 1 ≤ r), sum_empty] at h
  exact sub_eq_zero.mp (Complex.ofReal_eq_zero.mp h)

/-- Triangle inequality and the assumed level estimates bound the actual
polynomial remainder by the proved finite factorial tail. -/
theorem realTruncation_error_le_tail (Q : TensorPhase.Bits ι → ℝ) (a : ℝ)
    (r : ℕ) (hr : 1 ≤ r)
    (hlevel : ∀ (b : TensorPhase.Bits ι) (k : ℕ), 1 ≤ k →
      ‖TensorPhase.fourierLevel k (WalshReconstruction.coefficient (complexFunction Q))
        (fun i => TensorPhase.bitSign (b i))‖ ≤ a ^ k / (2 * (k.factorial : ℝ)))
    (b : TensorPhase.Bits ι) :
    |Q b - MvPolynomial.eval (fun i => realSign (b i)) (realTruncation r Q)| ≤
      (1 / 2 : ℝ) * ∑ k ∈ Ico r (Fintype.card ι + 1), a ^ k / (k.factorial : ℝ) := by
  calc
    _ = ‖((Q b - MvPolynomial.eval (fun i => realSign (b i))
        (realTruncation r Q) : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖∑ k ∈ Ico r (Fintype.card ι + 1), TensorPhase.fourierLevel k
        (WalshReconstruction.coefficient (complexFunction Q))
        (fun i => TensorPhase.bitSign (b i))‖ := by rw [realTruncation_remainder]
    _ ≤ ∑ k ∈ Ico r (Fintype.card ι + 1), ‖TensorPhase.fourierLevel k
        (WalshReconstruction.coefficient (complexFunction Q))
        (fun i => TensorPhase.bitSign (b i))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Ico r (Fintype.card ι + 1), a ^ k / (2 * (k.factorial : ℝ)) := by
      apply sum_le_sum
      intro k hk
      exact hlevel b k (hr.trans (mem_Ico.mp hk).1)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k hk
      ring

/-- A real polynomial of degree strictly below `r` approximates the whole
logical cube within `1/15` under the uniform factorial level estimates. -/
theorem exists_real_approximant (Q : TensorPhase.Bits ι → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (r : ℕ) (hr : 1 ≤ r) (hcut : 8 * Real.exp 1 * a ≤ (r : ℝ))
    (hlevel : ∀ (b : TensorPhase.Bits ι) (k : ℕ), 1 ≤ k →
      ‖TensorPhase.fourierLevel k (WalshReconstruction.coefficient (complexFunction Q))
        (fun i => TensorPhase.bitSign (b i))‖ ≤ a ^ k / (2 * (k.factorial : ℝ))) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree < r ∧
      ∀ b : TensorPhase.Bits ι,
        |Q b - MvPolynomial.eval (fun i => realSign (b i)) p| < 1 / 15 := by
  refine ⟨realTruncation r Q, realTruncation_totalDegree_lt r hr Q, ?_⟩
  intro b
  exact (realTruncation_error_le_tail Q a r hr hlevel b).trans_lt
    (FactorialTail.half_finite_tail_lt_one_fifteenth ha hcut hr (Fintype.card ι + 1))

end

end ApproxDegree.FourierTruncation
end


