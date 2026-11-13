-- Prove2me | Definitions.Def_ApproxDegCompV1_FourierExtraction
-- name    : ApproxDegCompV1_FourierExtraction
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-13T04:11:52.049479+00:00
-- url     : https://prove2.me/theorems/629b7ef5-230a-48d9-995e-2d1f4ebfe91c
-- title:
--   Approximate-degree composition: Exact Fourier extraction from fiber compression
-- statement:
--   This module formalizes exact Fourier extraction from fiber compression for the Lean proof of the approximate-degree composition lower bound.
-- source:
--   https://prove2.me/theorems/f8385c32-068c-45a1-99ed-f7cf0a99f266

import Definitions.Def_ApproxDegCompV1_CommutatorBounds
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

-- FiberCompression.lean
section
/-!
# Fiber-supported compression and logical masks

Rectangular matrices supported on their indicated logical fibers intertwine
all entry masks depending only on the two logical labels. This is proved by
expanding their actual matrix product, rather than assumed as a projection
compatibility property. No norm, positivity, or isometry assumption is used.
-/

open scoped BigOperators
open Finset

namespace ApproxDegree.FiberCompression

open CommonPhaseMatrix

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {X ι : Type*} [Fintype X] [Fintype ι]

abbrev B (ι : Type*) := ι → Bool

omit [Fintype ι] in
theorem compression_entry (W : Matrix (B ι) X ℂ) (R : Matrix X X ℂ)
    (V : Matrix X (B ι) ℂ) (a b : B ι) :
    (W * R * V) a b = ∑ x : X, ∑ y : X, W a x * R x y * V y b := by
  simp only [Matrix.mul_apply, sum_mul]
  rw [sum_comm]

/-- An entry mask depending on the logical labels of its row and column. -/
def labelMask (label : X → B ι) (p : B ι → B ι → Prop) [DecidableRel p]
    (R : Matrix X X ℂ) : Matrix X X ℂ :=
  fun x y => if p (label x) (label y) then R x y else 0

omit [Fintype ι] in
/-- Actual label-supported compression commutes with every logical entry mask. -/
theorem compress_labelMask (label : X → B ι)
    (W : Matrix (B ι) X ℂ) (V : Matrix X (B ι) ℂ)
    (hW : ∀ a x, W a x ≠ 0 → label x = a)
    (hV : ∀ x b, V x b ≠ 0 → label x = b)
    (p : B ι → B ι → Prop) [DecidableRel p] (R : Matrix X X ℂ) :
    labelMask id p (W * R * V) = W * labelMask label p R * V := by
  ext a b
  change (if p a b then (W * R * V) a b else 0) =
    (W * labelMask label p R * V) a b
  rw [compression_entry, compression_entry]
  have hterm (x y : X) :
      W a x * labelMask label p R x y * V y b =
        if p a b then W a x * R x y * V y b else 0 := by
    by_cases hw : W a x = 0
    · simp [hw]
    by_cases hv : V y b = 0
    · simp [hv]
    simp [labelMask, hW a x hw, hV y b hv, mul_ite, ite_mul]
  simp_rw [hterm]
  by_cases hp : p a b <;> simp [hp]

/-- Exact logical-distance masks are a special case of the label-mask theorem. -/
theorem compress_topDistancePart (label : X → B ι)
    (W : Matrix (B ι) X ℂ) (V : Matrix X (B ι) ℂ)
    (hW : ∀ a x, W a x ≠ 0 → label x = a)
    (hV : ∀ x b, V x b ≠ 0 → label x = b)
    (k : ℕ) (R : Matrix X X ℂ) :
    topDistancePart id k (W * R * V) = W * topDistancePart label k R * V := by
  exact compress_labelMask label W V hW hV
    (fun a b => logicalDistance a b = k) R

/-- No logical bandwidth is introduced by supported compression. -/
theorem compression_preserves_bandwidth (label : X → B ι)
    (W : Matrix (B ι) X ℂ) (V : Matrix X (B ι) ℂ)
    (hW : ∀ a x, W a x ≠ 0 → label x = a)
    (hV : ∀ x b, V x b ≠ 0 → label x = b)
    (k : ℕ) (R : Matrix X X ℂ)
    (hband : ∀ x y, k < logicalDistance (label x) (label y) → R x y = 0) :
    ∀ a b, k < logicalDistance a b → (W * R * V) a b = 0 := by
  intro a b hab
  rw [compression_entry]
  apply sum_eq_zero
  intro x hx
  apply sum_eq_zero
  intro y hy
  by_cases hw : W a x = 0
  · simp [hw]
  by_cases hv : V y b = 0
  · simp [hv]
  have hr : R x y = 0 := hband x y (by simpa only [hW a x hw, hV y b hv] using hab)
  simp [hr]

def compressionMap (W : Matrix (B ι) X ℂ) (V : Matrix X (B ι) ℂ) :
    Matrix X X ℂ →ₗ[ℂ] Matrix (B ι) (B ι) ℂ where
  toFun R := W * R * V
  map_add' R S := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c R := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

variable [DecidableEq ι]

omit [DecidableEq ι] in
theorem powersetCard_univ_eq_filter (k : ℕ) :
    (univ : Finset ι).powersetCard k =
      univ.filter (fun S : Finset ι => S.card = k) := by
  ext S
  simp

omit [DecidableEq ι] in
/-- Translate the raw regrouping theorem's natural scalar and powerset-card
notation to the complex scalar and filtered-Fourier convention. -/
theorem factorial_sum_conventions {M : Type*} [AddCommMonoid M] [Module ℂ M]
    (k : ℕ) (F : Finset ι → M) :
    k.factorial • (∑ S ∈ (univ : Finset ι).powersetCard k, F S) =
      (k.factorial : ℂ) •
        ∑ S ∈ univ.filter (fun S : Finset ι => S.card = k), F S := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, powersetCard_univ_eq_filter]

/-- Transport the supplied raw factorial crossing identity through actual
fiber-supported compression and supplied two-sided intertwinings. -/
theorem compress_factorial_top_identity (label : X → B ι)
    (W : Matrix (B ι) X ℂ) (V : Matrix X (B ι) ℂ)
    (hW : ∀ a x, W a x ≠ 0 → label x = a)
    (hV : ∀ x b, V x b ≠ 0 → label x = b)
    (L : ι → Matrix X X ℂ) (A : ι → Matrix (B ι) (B ι) ℂ)
    (hleft : ∀ i, W * L i = A i * W)
    (hright : ∀ i, L i * V = V * A i)
    (k : ℕ) (P R : Matrix X X ℂ)
    (htop : topDistancePart label k R =
      (k.factorial : ℂ) •
        ∑ S ∈ univ.filter (fun S : Finset ι => S.card = k),
          mixedMatrixCommutator L S.toList P) :
    topDistancePart id k (W * R * V) =
      (k.factorial : ℂ) •
        ∑ S ∈ univ.filter (fun S : Finset ι => S.card = k),
          mixedMatrixCommutator A S.toList (W * P * V) := by
  rw [compress_topDistancePart label W V hW hV, htop]
  change compressionMap W V ((k.factorial : ℂ) • _) = _
  rw [map_smul, map_sum]
  congr 1
  apply sum_congr rfl
  intro S hS
  exact compress_mixed_commutators W V L A hleft hright S.toList P

/-- A common scale on the compressed local operators contributes κ^k,
because every surviving crossing set has exactly k distinct indices. -/
theorem compress_scaled_factorial_top_identity (label : X → B ι)
    (W : Matrix (B ι) X ℂ) (V : Matrix X (B ι) ℂ)
    (hW : ∀ a x, W a x ≠ 0 → label x = a)
    (hV : ∀ x b, V x b ≠ 0 → label x = b)
    (L : ι → Matrix X X ℂ) (A : ι → Matrix (B ι) (B ι) ℂ) (κ : ℂ)
    (hleft : ∀ i, W * L i = (κ • A i) * W)
    (hright : ∀ i, L i * V = V * (κ • A i))
    (k : ℕ) (P R : Matrix X X ℂ)
    (htop : topDistancePart label k R =
      (k.factorial : ℂ) •
        ∑ S ∈ univ.filter (fun S : Finset ι => S.card = k),
          mixedMatrixCommutator L S.toList P) :
    topDistancePart id k (W * R * V) =
      ((k.factorial : ℂ) * κ ^ k) •
        ∑ S ∈ univ.filter (fun S : Finset ι => S.card = k),
          mixedMatrixCommutator A S.toList (W * P * V) := by
  rw [compress_factorial_top_identity label W V hW hV L (fun i => κ • A i)
    hleft hright k P R htop]
  have hsum :
      (∑ S ∈ univ.filter (fun S : Finset ι => S.card = k),
        mixedMatrixCommutator (fun i => κ • A i) S.toList (W * P * V)) =
      κ ^ k • ∑ S ∈ univ.filter (fun S : Finset ι => S.card = k),
        mixedMatrixCommutator A S.toList (W * P * V) := by
    rw [smul_sum]
    apply sum_congr rfl
    intro S hS
    rw [mixedMatrixCommutator_smul]
    simp only [length_toList, (mem_filter.mp hS).2]
  rw [hsum, smul_smul]

/-- The precise top-distance identity consumed by PhaseExtraction, now
obtained from raw fiber data rather than assumed on the logical matrix. -/
theorem compress_top_fourier_identity (label : X → B ι)
    (W : Matrix (B ι) X ℂ) (V : Matrix X (B ι) ℂ)
    (hW : ∀ a x, W a x ≠ 0 → label x = a)
    (hV : ∀ x b, V x b ≠ 0 → label x = b)
    (L : ι → Matrix X X ℂ) (κ : ℂ)
    (hleft : ∀ i, W * L i = (κ • TensorPhase.localX i) * W)
    (hright : ∀ i, L i * V = V * (κ • TensorPhase.localX i))
    (k : ℕ) (P R : Matrix X X ℂ) (c : Finset ι → ℂ)
    (hQ : W * P * V = TensorPhase.fourierMatrix c)
    (htop : topDistancePart label k R =
      (k.factorial : ℂ) •
        ∑ S ∈ univ.filter (fun S : Finset ι => S.card = k),
          mixedMatrixCommutator L S.toList P) :
    topDistancePart id k (W * R * V) =
      ((k.factorial : ℂ) * κ ^ k) •
        ∑ S ∈ univ.filter (fun S : Finset ι => S.card = k),
          TensorPhase.mixedSet S (TensorPhase.fourierMatrix c) := by
  simpa only [hQ, TensorPhase.mixedSet] using
    compress_scaled_factorial_top_identity label W V hW hV L TensorPhase.localX κ
      hleft hright k P R htop

end

end ApproxDegree.FiberCompression
end

-- PhasePower.lean
section
/-!
# Extracting a power of the common-phase difference

The actual binomial expansion of `(t⁻¹ - t)^k` has frequencies `k - 2*m`.
The signed grid removes all terms except `m = 0` and `m = k`. Thus this
module proves the common-phase power identity without assuming endpoint
coefficients or an abstract coefficient array.
-/

open scoped BigOperators
open Finset Complex

namespace ApproxDegree.PhasePower

open CommonPhaseMatrix

noncomputable section

/-- Explicit binomial Laurent expansion, valid at every nonzero point. -/
theorem inverse_sub_pow_eq_sum (t : ℂ) (ht : t ≠ 0) (k : ℕ) :
    (t⁻¹ - t) ^ k = ∑ m ∈ range (k + 1),
      ((-1 : ℂ) ^ (m + k) * (k.choose m : ℂ)) *
        t ^ ((k : ℤ) - 2 * (m : ℤ)) := by
  rw [sub_pow]
  apply sum_congr rfl
  intro m hm
  have hmle : m ≤ k := by simpa using mem_range.mp hm
  have hp : (t⁻¹) ^ m * t ^ (k - m) = t ^ ((k : ℤ) - 2 * (m : ℤ)) := by
    calc
      (t⁻¹) ^ m * t ^ (k - m) =
          t ^ (-(m : ℤ)) * t ^ ((k - m : ℕ) : ℤ) := by
        rw [zpow_neg, zpow_natCast, zpow_natCast, inv_pow]
      _ = t ^ (-(m : ℤ) + ((k - m : ℕ) : ℤ)) := (zpow_add₀ ht _ _).symm
      _ = _ := by congr 1; omega
  calc
    (-1 : ℂ) ^ (m + k) * (t⁻¹) ^ m * t ^ (k - m) * (k.choose m : ℂ) =
        ((-1 : ℂ) ^ (m + k) * (k.choose m : ℂ)) *
          ((t⁻¹) ^ m * t ^ (k - m)) := by ring
    _ = _ := by rw [hp]

/-- The signed positive endpoint is constant over the grid. -/
theorem signed_sum_positive_endpoint {k : ℕ} {ζ : ℂ}
    (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2 * k)) :
    (∑ j ∈ range (2 * k), (-1 : ℂ) ^ j * (I * ζ ^ j) ^ (k : ℤ)) =
      ((2 * k : ℕ) : ℂ) * I ^ k := by
  have hterm (j : ℕ) : (-1 : ℂ) ^ j * (I * ζ ^ j) ^ (k : ℤ) = I ^ k := by
    have hh : (ζ ^ j) ^ k = (-1 : ℂ) ^ j := by
      rw [← pow_mul, Nat.mul_comm j k, pow_mul, PhaseAverage.primitive_half_power hk hζ]
    rw [zpow_natCast, mul_pow, hh]
    calc
      _ = I ^ k * ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) := by ring
      _ = _ := by rw [← mul_pow]; simp
  simp_rw [hterm]
  simp

/-- The signed negative endpoint is constant over the grid. -/
theorem signed_sum_negative_endpoint {k : ℕ} {ζ : ℂ}
    (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2 * k)) :
    (∑ j ∈ range (2 * k), (-1 : ℂ) ^ j * (I * ζ ^ j) ^ (-(k : ℤ))) =
      ((2 * k : ℕ) : ℂ) * (-I) ^ k := by
  have hterm (j : ℕ) :
      (-1 : ℂ) ^ j * (I * ζ ^ j) ^ (-(k : ℤ)) = (-I) ^ k := by
    have hh : (ζ ^ j) ^ k = (-1 : ℂ) ^ j := by
      rw [← pow_mul, Nat.mul_comm j k, pow_mul, PhaseAverage.primitive_half_power hk hζ]
    have hI : (I ^ k)⁻¹ = (-I : ℂ) ^ k := by rw [← inv_pow, inv_I]
    rw [zpow_neg, zpow_natCast, mul_pow, hh, mul_inv_rev, hI]
    calc
      _ = ((-1 : ℂ) ^ j * ((-1 : ℂ) ^ j)⁻¹) * (-I) ^ k := by ring
      _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero j (by norm_num))]; ring
  simp_rw [hterm]
  simp

/-- Genuine binomial extraction for an arbitrary primitive grid. -/
theorem signed_sum_inverse_sub_pow {k : ℕ} {ζ : ℂ}
    (hk : 0 < k) (hζ : IsPrimitiveRoot ζ (2 * k)) :
    (∑ j ∈ range (2 * k), (-1 : ℂ) ^ j *
      ((I * ζ ^ j)⁻¹ - I * ζ ^ j) ^ k) =
      ((2 * k : ℕ) : ℂ) * (2 * (-I) ^ k) := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hexpand (j : ℕ) := inverse_sub_pow_eq_sum (I * ζ ^ j)
    (mul_ne_zero I_ne_zero (pow_ne_zero j hζ0)) k
  simp_rw [hexpand, mul_sum]
  rw [sum_comm]
  have hfactor (m : ℕ) :
      (∑ j ∈ range (2 * k), (-1 : ℂ) ^ j *
        (((-1 : ℂ) ^ (m + k) * (k.choose m : ℂ)) *
          (I * ζ ^ j) ^ ((k : ℤ) - 2 * (m : ℤ)))) =
      ((-1 : ℂ) ^ (m + k) * (k.choose m : ℂ)) *
        (∑ j ∈ range (2 * k), (-1 : ℂ) ^ j *
          (I * ζ ^ j) ^ ((k : ℤ) - 2 * (m : ℤ))) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    ring
  simp_rw [hfactor]
  rw [sum_range_succ]
  have hlower :
      (∑ m ∈ range k, ((-1 : ℂ) ^ (m + k) * (k.choose m : ℂ)) *
        (∑ j ∈ range (2 * k), (-1 : ℂ) ^ j *
          (I * ζ ^ j) ^ ((k : ℤ) - 2 * (m : ℤ)))) =
      (-1 : ℂ) ^ k * (((2 * k : ℕ) : ℂ) * I ^ k) := by
    rw [sum_eq_single 0]
    · simp only [Nat.zero_add, Nat.choose_zero_right, Nat.cast_one, mul_one,
        Int.natCast_zero, mul_zero, sub_zero]
      rw [signed_sum_positive_endpoint hk hζ]
    · intro m hm hm0
      have hmk : m < k := mem_range.mp hm
      rw [signed_sum_zpow_interior hk hζ (by omega) (by omega)]
      simp
    · intro hn
      exact (hn (mem_range.mpr hk)).elim
  rw [hlower]
  have hfreq : (k : ℤ) - 2 * (k : ℤ) = -(k : ℤ) := by ring
  rw [hfreq, signed_sum_negative_endpoint hk hζ, Nat.choose_self, Nat.cast_one, mul_one]
  have hsign : (-1 : ℂ) ^ (k + k) = 1 := by
    rw [pow_add, ← mul_pow]
    simp
  have hphase : (-1 : ℂ) ^ k * I ^ k = (-I) ^ k := by rw [← mul_pow]; simp
  rw [hsign, one_mul]
  calc
    _ = (((2 * k : ℕ) : ℂ) * ((-1 : ℂ) ^ k * I ^ k)) +
        ((2 * k : ℕ) : ℂ) * (-I) ^ k := by ring
    _ = _ := by rw [hphase]; ring

theorem signedAverage_const_mul (k : ℕ) (A : ℂ) (B : ℂ → ℂ) :
    signedAverage k (fun t => A * B t) = A * signedAverage k B := by
  unfold signedAverage
  have hfactor : (∑ j ∈ range (2 * k), (-1 : ℂ) ^ j *
      (A * B (I * PhaseAverage.standardRoot k ^ j))) =
      A * ∑ j ∈ range (2 * k), (-1 : ℂ) ^ j *
        B (I * PhaseAverage.standardRoot k ^ j) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    ring
  rw [hfactor, mul_div_assoc]

/-- The exact scalar interface needed by the tensor phase expectation. -/
theorem signedAverage_phase_power {k : ℕ} (hk : 0 < k) (A : ℂ) :
    signedAverage k (fun t => A * (t⁻¹ - t) ^ k) = 2 * (-I) ^ k * A := by
  rw [signedAverage_const_mul]
  unfold signedAverage
  rw [signed_sum_inverse_sub_pow hk (PhaseAverage.standardRoot_primitive hk)]
  have hn : ((2 * k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show 2 * k ≠ 0 by omega)
  field_simp

/-- The signed averaging functional has norm at most one on bounded samples. -/
theorem norm_signedAverage_le {k : ℕ} (hk : 0 < k) (B : ℂ → ℂ) {M : ℝ}
    (hbound : ∀ j ∈ range (2 * k),
      ‖B (I * PhaseAverage.standardRoot k ^ j)‖ ≤ M) :
    ‖signedAverage k B‖ ≤ M := by
  have hn : (0 : ℝ) < ((2 * k : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * k by omega)
  have hsum :
      ‖∑ j ∈ range (2 * k), (-1 : ℂ) ^ j *
          B (I * PhaseAverage.standardRoot k ^ j)‖ ≤ ((2 * k : ℕ) : ℝ) * M := by
    calc
      _ ≤ ∑ j ∈ range (2 * k),
          ‖(-1 : ℂ) ^ j * B (I * PhaseAverage.standardRoot k ^ j)‖ := norm_sum_le _ _
      _ = ∑ j ∈ range (2 * k), ‖B (I * PhaseAverage.standardRoot k ^ j)‖ := by simp
      _ ≤ ∑ j ∈ range (2 * k), M := sum_le_sum hbound
      _ = _ := by simp
  unfold signedAverage
  rw [norm_div, Complex.norm_natCast]
  exact (div_le_iff₀ hn).mpr (by simpa [mul_comm] using hsum)

end

end ApproxDegree.PhasePower
end

-- PhaseExtraction.lean
section
/-!
# From a banded logical matrix to the whole Fourier level

This module connects the actual reciprocal-bra tensor phase functional to
the matrix-distance cancellation and the phase-power average. The concrete
matrix bandwidth and highest-distance commutator identity are explicit inputs.
The extreme phase coefficients are not hypotheses: the checked tensor
calculation and phase filter derive their combined contribution.
-/

open scoped BigOperators
open Finset Complex

namespace ApproxDegree.PhaseExtraction

open CommonPhaseMatrix

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem logicalWeight_eq_bitWeight (a : TensorPhase.Bits ι) :
    logicalWeight a = (TensorPhase.bitWeight a : ℤ) := by
  unfold logicalWeight TensorPhase.bitWeight
  exact sum_boole _ _

theorem grid_ne_zero {k : ℕ} (hk : 0 < k) (j : ℕ) :
    I * PhaseAverage.standardRoot k ^ j ≠ 0 := by
  apply mul_ne_zero I_ne_zero
  apply pow_ne_zero
  exact (PhaseAverage.standardRoot_primitive hk).ne_zero (by omega)

theorem signedAverage_congr_on_nonzero {k : ℕ} (hk : 0 < k)
    {B C : ℂ → ℂ} (h : ∀ t, t ≠ 0 → B t = C t) :
    signedAverage k B = signedAverage k C := by
  unfold signedAverage
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [h _ (grid_ne_zero hk j)]

theorem phaseExpectation_eq_phaseSum (z : ι → ℂ) {t : ℂ} (ht : t ≠ 0)
    (R : Matrix (TensorPhase.Bits ι) (TensorPhase.Bits ι) ℂ) :
    TensorPhase.phaseExpectation z t R =
      phaseSum logicalWeight (TensorPhase.phaseCoefficient z R) t := by
  rw [TensorPhase.phaseExpectation_eq_weight_sum z ht R]
  unfold phaseSum
  simp_rw [logicalWeight_eq_bitWeight]

omit [DecidableEq ι] in
theorem phaseCoefficient_topDistancePart (z : ι → ℂ) (k : ℕ)
    (R : Matrix (TensorPhase.Bits ι) (TensorPhase.Bits ι) ℂ) :
    TensorPhase.phaseCoefficient z (topDistancePart id k R) =
      topDistancePart id k (TensorPhase.phaseCoefficient z R) := by
  ext a b
  by_cases h : logicalDistance a b = k <;>
    simp [TensorPhase.phaseCoefficient, topDistancePart, h]

/-- Cancellation of lower-distance contributions for the concrete tensor
phase expectation, rather than an assumed Laurent representation. -/
theorem signedAverage_expectation_eq_top {k : ℕ} (hk : 0 < k) (z : ι → ℂ)
    (R : Matrix (TensorPhase.Bits ι) (TensorPhase.Bits ι) ℂ)
    (hband : ∀ a b, k < logicalDistance a b → R a b = 0) :
    signedAverage k (fun t => TensorPhase.phaseExpectation z t R) =
      signedAverage k (fun t => TensorPhase.phaseExpectation z t (topDistancePart id k R)) := by
  have heq (T : Matrix (TensorPhase.Bits ι) (TensorPhase.Bits ι) ℂ) :
      signedAverage k (fun t => TensorPhase.phaseExpectation z t T) =
        signedAverage k (phaseSum logicalWeight (TensorPhase.phaseCoefficient z T)) :=
    signedAverage_congr_on_nonzero hk (fun t ht => phaseExpectation_eq_phaseSum z ht T)
  rw [heq, heq, phaseCoefficient_topDistancePart]
  apply signedAverage_eq_topDistancePart hk id
  intro a b hab
  simp [TensorPhase.phaseCoefficient, hband a b hab]

/-- Given the actual top-distance matrix identity, the signed average
extracts exactly the whole Fourier level with its factorial and scale. -/
theorem signedAverage_expectation_eq_fourier {k : ℕ} (hk : 0 < k)
    (z : ι → ℂ) (hz : ∀ i, z i * z i = 1) (κ : ℂ)
    (R : Matrix (TensorPhase.Bits ι) (TensorPhase.Bits ι) ℂ) (c : Finset ι → ℂ)
    (hband : ∀ a b, k < logicalDistance a b → R a b = 0)
    (htop : topDistancePart id k R =
      ((k.factorial : ℂ) * κ ^ k) •
        ∑ S ∈ univ.filter (fun S : Finset ι => S.card = k),
          TensorPhase.mixedSet S (TensorPhase.fourierMatrix c)) :
    signedAverage k (fun t => TensorPhase.phaseExpectation z t R) =
      2 * (-I) ^ k * ((k.factorial : ℂ) * κ ^ k * TensorPhase.fourierLevel k c z) := by
  rw [signedAverage_expectation_eq_top hk z R hband]
  have heq :
      signedAverage k (fun t => TensorPhase.phaseExpectation z t (topDistancePart id k R)) =
        signedAverage k (fun t =>
          ((k.factorial : ℂ) * κ ^ k * TensorPhase.fourierLevel k c z) * (t⁻¹ - t) ^ k) := by
    apply signedAverage_congr_on_nonzero hk
    intro t ht
    rw [htop, map_smul, TensorPhase.expectation_mixed_fourier_level z hz ht]
    simp only [smul_eq_mul]
    ring
  rw [heq, PhasePower.signedAverage_phase_power hk]

/-- The uniform scalar level bound follows from an actual banded matrix,
its specified top-distance part, and bounds on its phase-state samples. -/
theorem fourier_level_bound_of_banded_matrix {k D : ℕ} (hk : 0 < k)
    {κ M : ℝ} (hκ : 0 < κ) (z : ι → ℂ) (hz : ∀ i, z i * z i = 1)
    (R : Matrix (TensorPhase.Bits ι) (TensorPhase.Bits ι) ℂ) (c : Finset ι → ℂ)
    (hband : ∀ a b, k < logicalDistance a b → R a b = 0)
    (htop : topDistancePart id k R =
      ((k.factorial : ℂ) * (κ : ℂ) ^ k) •
        ∑ S ∈ univ.filter (fun S : Finset ι => S.card = k),
          TensorPhase.mixedSet S (TensorPhase.fourierMatrix c))
    (hbound : ∀ j ∈ range (2 * k),
      ‖TensorPhase.phaseExpectation z (I * PhaseAverage.standardRoot k ^ j) R‖ ≤
        (D : ℝ) ^ k * M) :
    ‖TensorPhase.fourierLevel k c z‖ ≤ M / (2 * (k.factorial : ℝ)) * ((D : ℝ) / κ) ^ k := by
  have havg := signedAverage_expectation_eq_fourier hk z hz (κ : ℂ) R c hband htop
  have hnorm := PhasePower.norm_signedAverage_le hk
    (fun t => TensorPhase.phaseExpectation z t R) hbound
  rw [havg] at hnorm
  simp only [norm_mul, norm_ofNat, norm_pow, norm_neg, norm_I, one_pow, mul_one] at hnorm
  have hfact : 0 < (k.factorial : ℝ) := by positivity
  have hden : 0 < 2 * (k.factorial : ℝ) * κ ^ k := by positivity
  have hscale : 2 * ((k.factorial : ℝ) * κ ^ k * ‖TensorPhase.fourierLevel k c z‖) ≤
      (D : ℝ) ^ k * M := by
    simpa [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ] using hnorm
  calc
    ‖TensorPhase.fourierLevel k c z‖ ≤
        (D : ℝ) ^ k * M / (2 * (k.factorial : ℝ) * κ ^ k) := by
      apply (le_div_iff₀ hden).mpr
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hscale
    _ = M / (2 * (k.factorial : ℝ)) * ((D : ℝ) / κ) ^ k := by
      rw [div_pow]
      field_simp

end

end ApproxDegree.PhaseExtraction
end

-- OperatorExtraction.lean
section
/-!
# The connected operator-to-Fourier extraction

The highest-distance identity and bandwidth are derived from the actual
local matrices and a diagonal multiplier, then transported through a
fiber-supported compression. The remaining hypotheses concern the chosen
compression/intertwinings, the represented Fourier coefficients, and the
analytic sample bound. No phase coefficients, bandwidth, or highest-distance
identity are assumed by the final theorem.
-/

open scoped BigOperators
open Finset Complex

namespace ApproxDegree.OperatorExtraction

open CommonPhaseMatrix

noncomputable section

variable {X ι : Type*} [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι]

/-- The actual raw iterated commutator of a point multiplier. -/
def rawCommutator (H : ι → Matrix X X ℂ) (p : X → ℂ) (k : ℕ) : Matrix X X ℂ :=
  (fun T => matrixCommutator (∑ i, H i) T)^[k] (Matrix.diagonal p)

/-- The algebraic extraction theorem with all grading and endpoint
connections discharged. Locality and distinct crossing commutation are
structural hypotheses here; concrete tensor lifts satisfy them separately. -/
theorem fourier_level_bound_from_local_operators {k D : ℕ} (hk : 0 < k)
    {κ M : ℝ} (hκ : 0 < κ) (label : X → TensorPhase.Bits ι)
    (H : ι → Matrix X X ℂ) (hH : ∀ i, OperatorGrading.LocalAt label i (H i))
    (hcomm : ∀ i j, i ≠ j →
      OperatorGrading.gradePart label {i} (H i) * OperatorGrading.gradePart label {j} (H j) =
      OperatorGrading.gradePart label {j} (H j) * OperatorGrading.gradePart label {i} (H i))
    (W : Matrix (TensorPhase.Bits ι) X ℂ) (V : Matrix X (TensorPhase.Bits ι) ℂ)
    (hW : ∀ a x, W a x ≠ 0 → label x = a)
    (hV : ∀ x b, V x b ≠ 0 → label x = b)
    (hleft : ∀ i, W * OperatorGrading.gradePart label {i} (H i) =
      ((κ : ℂ) • TensorPhase.localX i) * W)
    (hright : ∀ i, OperatorGrading.gradePart label {i} (H i) * V =
      V * ((κ : ℂ) • TensorPhase.localX i))
    (p : X → ℂ) (c : Finset ι → ℂ)
    (hQ : W * Matrix.diagonal p * V = TensorPhase.fourierMatrix c)
    (z : ι → ℂ) (hz : ∀ i, z i * z i = 1)
    (hbound : ∀ j ∈ range (2 * k),
      ‖TensorPhase.phaseExpectation z (I * PhaseAverage.standardRoot k ^ j)
        (W * rawCommutator H p k * V)‖ ≤ (D : ℝ) ^ k * M) :
    ‖TensorPhase.fourierLevel k c z‖ ≤
      M / (2 * (k.factorial : ℝ)) * ((D : ℝ) / κ) ^ k := by
  have hP := OperatorGrading.hasGrade_diagonal label p
  have hrawBand : ∀ x y, k < logicalDistance (label x) (label y) →
      rawCommutator H p k x y = 0 := by
    intro x y hxy
    exact OperatorGrading.iterated_total_sum_bandwidth label H hH hP k x y hxy
  have hrawTop : topDistancePart label k (rawCommutator H p k) =
      (k.factorial : ℂ) •
        ∑ S ∈ univ.filter (fun S : Finset ι => S.card = k),
          mixedMatrixCommutator (fun i => OperatorGrading.gradePart label {i} (H i))
            S.toList (Matrix.diagonal p) := by
    change OperatorGrading.distancePart label k
      ((fun T => matrixCommutator (∑ i, H i) T)^[k] (Matrix.diagonal p)) = _
    rw [OperatorGrading.highest_distance_factorial_identity label H hH hcomm hP k,
      FiberCompression.factorial_sum_conventions]
  have htop := FiberCompression.compress_top_fourier_identity label W V hW hV
    (fun i => OperatorGrading.gradePart label {i} (H i)) (κ : ℂ)
    hleft hright k (Matrix.diagonal p) (rawCommutator H p k) c hQ hrawTop
  have hband := FiberCompression.compression_preserves_bandwidth label W V hW hV
    k (rawCommutator H p k) hrawBand
  exact PhaseExtraction.fourier_level_bound_of_banded_matrix hk hκ z hz
    (W * rawCommutator H p k * V) c hband htop hbound

section CoordinateLifts

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

set_option maxHeartbeats 800000 in
/-- Concrete tensor-coordinate version: locality, crossing commutation,
bandwidth, factorial regrouping, and phase endpoints are all derived.
The hypotheses left for the analytic construction are fiber-supported
intertwinings, the compressed multiplier, and the scalar sample bound. -/
theorem fourier_level_bound_from_coordinate_lifts {k D : ℕ} (hk : 0 < k)
    {κ M : ℝ} (hκ : 0 < κ) (g : Y → Bool) (K : ι → Matrix Y Y ℂ)
    (W : Matrix (TensorPhase.Bits ι) (ι → Y) ℂ)
    (V : Matrix (ι → Y) (TensorPhase.Bits ι) ℂ)
    (hW : ∀ a x, W a x ≠ 0 → (fun i => g (x i)) = a)
    (hV : ∀ x b, V x b ≠ 0 → (fun i => g (x i)) = b)
    (hleft : ∀ i, W * OperatorGrading.localLift (LocalCommutation.innerCrossing g (K i)) i =
      ((κ : ℂ) • TensorPhase.localX i) * W)
    (hright : ∀ i, OperatorGrading.localLift (LocalCommutation.innerCrossing g (K i)) i * V =
      V * ((κ : ℂ) • TensorPhase.localX i))
    (p : (ι → Y) → ℂ) (c : Finset ι → ℂ)
    (hQ : W * Matrix.diagonal p * V = TensorPhase.fourierMatrix c)
    (z : ι → ℂ) (hz : ∀ i, z i * z i = 1)
    (hbound : ∀ j ∈ range (2 * k),
      ‖TensorPhase.phaseExpectation z (I * PhaseAverage.standardRoot k ^ j)
        (W * rawCommutator (fun i => OperatorGrading.localLift (K i) i) p k * V)‖ ≤
        (D : ℝ) ^ k * M) :
    ‖TensorPhase.fourierLevel k c z‖ ≤
      M / (2 * (k.factorial : ℝ)) * ((D : ℝ) / κ) ^ k := by
  apply fourier_level_bound_from_local_operators (X := ι → Y) (ι := ι)
    hk hκ (fun x i => g (x i))
    (fun i => OperatorGrading.localLift (K i) i)
    (fun i => OperatorGrading.localAt_localLift g (K i) i)
    (fun i j hij => LocalCommutation.gradePart_localLift_commute g (K i) (K j) hij)
    W V hW hV _ _ p c hQ z hz hbound
  · intro i
    simpa only [LocalCommutation.gradePart_localLift] using hleft i
  · intro i
    simpa only [LocalCommutation.gradePart_localLift] using hright i

end CoordinateLifts

end

end ApproxDegree.OperatorExtraction
end

-- ConstructedExtraction.lean
section
/-!
# Fourier extraction with the inner witness and channel fully constructed

Inner polynomial nonapproximation constructs the dual weight, finite projection
generator, norm-scale exchange pair, positive exact-fiber product channel, and
its Walsh coefficients. The remaining quantitative premise is the explicit
phase sample bound for the actual iterated raw coordinate-lift commutator.
-/

open scoped BigOperators
open Finset Complex

namespace ApproxDegree.ConstructedExtraction

noncomputable section

variable {X σ : Type*} [Fintype X] [DecidableEq X]

/-- The one-block data constructed by degree nonapproximation. Its exchange
scale is the actual Hilbert operator norm of the explicitly defined strip. -/
structure InnerData (coords : X → σ → ℝ) (g : X → Bool) (d : ℕ) (ε : ℝ) where
  psi : X → ℝ
  u : Bool → X → ℂ
  mass_one : (∑ x, |psi x|) = 1
  scale_lower : ε * (d : ℝ) / 2 < ‖DegreeScaleWitness.witnessStrip psi coords g d‖
  scale_pos : 0 < ‖DegreeScaleWitness.witnessStrip psi coords g d‖
  normalized : ∀ b, ∑ x, ‖u b x‖ ^ 2 = 1
  support : ∀ b x, u b x ≠ 0 → g x = b
  exchange : ∀ b x,
    ∑ y, LocalCommutation.innerCrossing g (DegreeScaleWitness.witnessMatrix psi coords d) x y *
      u b y = (‖DegreeScaleWitness.witnessStrip psi coords g d‖ : ℂ) * u (!b) x

/-- The data structure is inhabited as a theorem, from actual failure of
degree-(d-1) polynomial approximation on the given finite point domain. -/
theorem exists_innerData (coords : X → σ → ℝ) (g : X → Bool)
    (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 ≤ ε)
    (hno : ¬ ∃ p : MvPolynomial σ ℝ, p.totalDegree ≤ d - 1 ∧
      ∀ x, |DegreeScaleWitness.signTarget g x - MvPolynomial.eval (coords x) p| ≤ ε) :
    Nonempty (InnerData coords g d ε) := by
  obtain ⟨psi, u, hm, hs, hp, hn, hf, he⟩ :=
    DegreeScaleWitness.exists_degree_scale_witness coords g d hd ε hε hno
  exact ⟨⟨psi, u, hm, hs, hp, hn, hf, he⟩⟩

namespace InnerData

variable {coords : X → σ → ℝ} {g : X → Bool} {d : ℕ} {ε : ℝ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every constructed witness gives the exact Fourier-level bound for its
constructed channel. Fiber support, tensor exchange, and Fourier representation
are proved inside this theorem; none is an extraction premise. -/
theorem fourier_level_bound (w : InnerData coords g d ε)
    (p : (ι → X) → ℂ) {k D : ℕ} (hk : 0 < k) {M : ℝ}
    (z : ι → ℂ) (hz : ∀ i, z i * z i = 1)
    (hbound : ∀ j ∈ range (2 * k),
      ‖TensorPhase.phaseExpectation z (I * PhaseAverage.standardRoot k ^ j)
        (FiberChannel.productW w.u *
          OperatorExtraction.rawCommutator
            (fun i => OperatorGrading.localLift
              (DegreeScaleWitness.witnessMatrix w.psi coords d) i) p k *
          FiberChannel.productV w.u)‖ ≤ (D : ℝ) ^ k * M) :
    ‖TensorPhase.fourierLevel k
      (WalshReconstruction.coefficient (FiberChannel.channelQ w.u p)) z‖ ≤
      M / (2 * (k.factorial : ℝ)) *
        ((D : ℝ) / ‖DegreeScaleWitness.witnessStrip w.psi coords g d‖) ^ k := by
  have hintertwining := FiberIntertwining.crossing_intertwinings g
    (fun _ : ι => DegreeScaleWitness.witnessMatrix w.psi coords d)
    (fun _ => DegreeScaleWitness.witnessMatrix_isHermitian w.psi coords d)
    w.u ‖DegreeScaleWitness.witnessStrip w.psi coords g d‖ (fun _ => w.exchange)
  exact OperatorExtraction.fourier_level_bound_from_coordinate_lifts hk w.scale_pos g
    (fun _ : ι => DegreeScaleWitness.witnessMatrix w.psi coords d)
    (FiberChannel.productW w.u) (FiberChannel.productV w.u)
    (FiberChannel.productW_support g w.u w.support)
    (FiberChannel.productV_support g w.u w.support)
    hintertwining.1 hintertwining.2 p
    (WalshReconstruction.coefficient (FiberChannel.channelQ w.u p))
    (WalshReconstruction.channel_compression g w.u w.support p) z hz hbound

/-- The same constructed data also give actual normalized nonnegative
channel weights on every product cube. -/
theorem channel_probability (w : InnerData coords g d ε) (b : FiberChannel.Bits ι) :
    (∀ x : ι → X, 0 ≤ FiberChannel.weights w.u b x) ∧
      ∑ x : ι → X, FiberChannel.weights w.u b x = 1 :=
  ⟨FiberChannel.weights_nonnegative w.u b,
    FiberChannel.weights_sum_one w.u w.normalized b⟩

end InnerData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- End-to-end existential form: the same dual weight and point vectors work
for every raw point function and every requested Fourier level. The scale,
support, exchange intertwinings, and Fourier coefficients are constructed from
inner nonapproximation. Only the explicit phase sample estimate remains. -/
theorem exists_constructed_fourier_bound (coords : X → σ → ℝ) (g : X → Bool)
    (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 ≤ ε)
    (hno : ¬ ∃ p : MvPolynomial σ ℝ, p.totalDegree ≤ d - 1 ∧
      ∀ x, |DegreeScaleWitness.signTarget g x - MvPolynomial.eval (coords x) p| ≤ ε) :
    ∃ (psi : X → ℝ) (u : Bool → X → ℂ),
      (∑ x, |psi x|) = 1 ∧
      ε * (d : ℝ) / 2 < ‖DegreeScaleWitness.witnessStrip psi coords g d‖ ∧
      0 < ‖DegreeScaleWitness.witnessStrip psi coords g d‖ ∧
      (∀ b, ∑ x, ‖u b x‖ ^ 2 = 1) ∧
      (∀ b x, u b x ≠ 0 → g x = b) ∧
      (∀ (p : (ι → X) → ℂ) (k D : ℕ) (M : ℝ) (z : ι → ℂ),
        0 < k → (∀ i, z i * z i = 1) →
        (∀ j ∈ range (2 * k),
          ‖TensorPhase.phaseExpectation z (I * PhaseAverage.standardRoot k ^ j)
            (FiberChannel.productW u *
              OperatorExtraction.rawCommutator
                (fun i => OperatorGrading.localLift
                  (DegreeScaleWitness.witnessMatrix psi coords d) i) p k *
              FiberChannel.productV u)‖ ≤ (D : ℝ) ^ k * M) →
        ‖TensorPhase.fourierLevel k
          (WalshReconstruction.coefficient (FiberChannel.channelQ u p)) z‖ ≤
          M / (2 * (k.factorial : ℝ)) *
            ((D : ℝ) / ‖DegreeScaleWitness.witnessStrip psi coords g d‖) ^ k) := by
  obtain ⟨w⟩ := exists_innerData coords g d hd ε hε hno
  refine ⟨w.psi, w.u, w.mass_one, w.scale_lower, w.scale_pos,
    w.normalized, w.support, ?_⟩
  intro p k D M z hk hz hbound
  exact w.fourier_level_bound p hk z hz hbound

end

end ApproxDegree.ConstructedExtraction
end


