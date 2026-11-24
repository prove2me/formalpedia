-- Prove2me | Definitions.Def_CSL_Circuit_Framework_MatrixFactorization
-- name    : CSL_Circuit_Framework_MatrixFactorization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:57:44.676258+00:00
-- url     : https://prove2.me/theorems/dc68c043-ce9f-42a0-8549-20b7e9b49c4f
-- title:
--   Coded sorting library: Circuit / Framework / MatrixFactorization
-- statement:
--   Module `CodedSorting.Circuit.Framework.MatrixFactorization` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Uniform specialization of finite rational matrix data
--
--   This module constructs a common denominator localization for arbitrary finite
--   rational coefficient data and a single odd prime which works for every prime
--   power.  Matrix identities are transported through an actual constructed ring
--   homomorphism.  The manuscript's lower-triangular/partial-permutation factorization is
--   proved by extremal-pivot elimination and strong induction on actual matrix rank.
--   The final theorems specialize every factor and inverse jointly and implement
--   the partial permutation by exactly rank_Q(A) elementary coordinate shears.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Framework.MatrixFactorization

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Memory_Address
import Definitions.Def_CSL_Circuit_Labels_Framework_TensorLabels
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Uniform specialization of finite rational matrix data

This module constructs a common denominator localization for arbitrary finite
rational coefficient data and a single odd prime which works for every prime
power.  Matrix identities are transported through an actual constructed ring
homomorphism.  The manuscript's lower-triangular/partial-permutation factorization is
proved by extremal-pivot elimination and strong induction on actual matrix rank.
The final theorems specialize every factor and inverse jointly and implement
the partial permutation by exactly rank_Q(A) elementary coordinate shears.
-/

namespace CSL.MatrixFactorization

abbrev CoeffRing (D : ℕ) := Localization.Away (D : ℤ)

noncomputable def intoRat (D : ℕ) (hD : D ≠ 0) : CoeffRing D →+* ℚ :=
  Localization.awayLift (Int.castRingHom ℚ) (D : ℤ)
    (isUnit_iff_ne_zero.mpr (by
      change (D : ℚ) ≠ 0
      exact_mod_cast hD))

@[simp] theorem intoRat_int (D : ℕ) (hD : D ≠ 0) (z : ℤ) :
    intoRat D hD (z : CoeffRing D) = (z : ℚ) := by
  simp

theorem intoRat_injective (D : ℕ) (hD : D ≠ 0) :
    Function.Injective (intoRat D hD) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (M := Submonoid.powers (D : ℤ)) (intoRat D hD)).2
  intro x y
  constructor
  · exact congrArg (intoRat D hD)
  · intro h
    have hrat : (x : ℚ) = (y : ℚ) := by simpa using h
    have hxy : x = y := by exact_mod_cast hrat
    rw [hxy]

/-- Every rational whose denominator divides `D` belongs to this explicit
localization; the existence of its lift is proved, not supplied by the caller. -/
theorem exists_rational_lift (D : ℕ) (hD : D ≠ 0) (r : ℚ)
    (hr : r.den ∣ D) :
    ∃ a : CoeffRing D, intoRat D hD a = r := by
  have hdiv : (r.den : ℤ) ∣ (D : ℤ) := by exact_mod_cast hr
  have hu : IsUnit ((r.den : ℤ) : CoeffRing D) := by
    simpa using (IsLocalization.Away.isUnit_of_dvd
      (S := CoeffRing D) (D : ℤ) hdiv)
  refine ⟨(r.num : CoeffRing D) * (↑hu.unit⁻¹ : CoeffRing D), ?_⟩
  rw [map_mul, intoRat_int, map_units_inv, hu.unit_spec, intoRat_int]
  exact Rat.num_div_den r

section FiniteCoefficients

variable {ι : Type*} [Fintype ι]

/-- The product deliberately includes every denominator in the finite data. -/
def commonDenominator (a : ι → ℚ) : ℕ := ∏ i, (a i).den

theorem commonDenominator_ne_zero (a : ι → ℚ) :
    commonDenominator a ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (a i).den_nz

theorem denominator_dvd_common (a : ι → ℚ) (i : ι) :
    (a i).den ∣ commonDenominator a := by
  classical
  exact Finset.dvd_prod_of_mem (fun i => (a i).den) (Finset.mem_univ i)

/-- All entries have lifts into the same explicit denominator ring. -/
theorem exists_common_lifts (a : ι → ℚ) :
    ∃ b : ι → CoeffRing (commonDenominator a),
      ∀ i, intoRat _ (commonDenominator_ne_zero a) (b i) = a i := by
  choose b hb using fun i => exists_rational_lift (commonDenominator a)
    (commonDenominator_ne_zero a) (a i) (denominator_dvd_common a i)
  exact ⟨b, hb⟩

/-- A genuine map into each `ZMod (q^f)` exists for one chosen odd prime.
The denominator-unit condition is obtained from `Address.exists_good_prime`. -/
theorem exists_uniform_specialization (a : ι → ℚ) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧
      ∃ maps : ∀ f : ℕ, CoeffRing (commonDenominator a) →+* ZMod (q ^ f),
        ∀ f (z : ℤ), maps f (z : CoeffRing (commonDenominator a)) = z := by
  classical
  obtain ⟨q, hq, hodd, hunits⟩ :=
    Address.exists_good_prime {commonDenominator a} (by
      intro n hn
      simp only [Finset.mem_singleton] at hn
      subst n
      exact commonDenominator_ne_zero a)
  have hunit (f : ℕ) : IsUnit ((commonDenominator a : ℤ) : ZMod (q ^ f)) := by
    simpa using hunits (commonDenominator a) (Finset.mem_singleton_self _) f
  refine ⟨q, hq, hodd,
    fun f => Localization.awayLift (Int.castRingHom (ZMod (q ^ f)))
      (commonDenominator a : ℤ) (hunit f), ?_⟩
  intro f z
  simp

end FiniteCoefficients

section MatrixFamilies

variable {K I : Type*} [Fintype K] [Fintype I] [DecidableEq I]

/-- A specialization contains the explicit common-denominator ring, its
injective rational interpretation, all lifted matrices, and actual maps to
every power of one odd prime.  The finite input may include both a matrix and
its rational inverse; their identities will then be preserved automatically. -/
structure SpecializedFamily (A : K → Matrix I I ℚ) where
  denominator : ℕ
  denominator_ne_zero : denominator ≠ 0
  prime : ℕ
  prime_is_prime : prime.Prime
  prime_is_odd : Odd prime
  coefficients : K → Matrix I I (CoeffRing denominator)
  lift_correct : ∀ k,
    (intoRat denominator denominator_ne_zero).mapMatrix (coefficients k) = A k
  inverse_coefficients : K → Matrix I I (CoeffRing denominator)
  inverse_lift_correct : ∀ k i j,
    intoRat denominator denominator_ne_zero (inverse_coefficients k i j) = (A k i j)⁻¹
  reduce : ∀ f : ℕ, CoeffRing denominator →+* ZMod (prime ^ f)

/-- Construction for an arbitrary finite family of rational matrices.
There are no assumptions about denominators being units after reduction. -/
noncomputable def specializeFamily (A : K → Matrix I I ℚ) : SpecializedFamily A := by
  apply Classical.choice
  let entries : Bool × (K × I × I) → ℚ := fun x =>
    if x.1 then (A x.2.1 x.2.2.1 x.2.2.2)⁻¹ else A x.2.1 x.2.2.1 x.2.2.2
  obtain ⟨b, hb⟩ := exists_common_lifts entries
  obtain ⟨q, hq, hodd, maps, _⟩ := exists_uniform_specialization entries
  refine ⟨{
    denominator := commonDenominator entries
    denominator_ne_zero := commonDenominator_ne_zero entries
    prime := q
    prime_is_prime := hq
    prime_is_odd := hodd
    coefficients := fun k i j => b (false, k, i, j)
    lift_correct := ?_
    inverse_coefficients := fun k i j => b (true, k, i, j)
    inverse_lift_correct := ?_
    reduce := maps }⟩
  · intro k
    ext i j
    exact hb (false, k, i, j)
  · intro k i j
    exact hb (true, k, i, j)

namespace SpecializedFamily

variable {A : K → Matrix I I ℚ} (F : SpecializedFamily A)

def matrix (f : ℕ) (k : K) : Matrix I I (ZMod (F.prime ^ f)) :=
  (F.reduce f).mapMatrix (F.coefficients k)

theorem coefficient_spec (k : K) (i j : I) :
    intoRat F.denominator F.denominator_ne_zero (F.coefficients k i j) = A k i j :=
  congrArg (fun M : Matrix I I ℚ => M i j) (F.lift_correct k)

theorem rational_embedding_injective :
    Function.Injective
      ((intoRat F.denominator F.denominator_ne_zero).mapMatrix :
        Matrix I I (CoeffRing F.denominator) → Matrix I I ℚ) :=
  Matrix.map_injective (intoRat_injective F.denominator F.denominator_ne_zero)

/-- Every supplied rational product identity survives, for every exponent. -/
theorem preserves_product (i j k : K) (h : A i * A j = A k) (f : ℕ) :
    F.matrix f i * F.matrix f j = F.matrix f k := by
  have hlocal : F.coefficients i * F.coefficients j = F.coefficients k := by
    apply F.rational_embedding_injective
    simpa only [map_mul, F.lift_correct] using h
  simpa only [matrix, map_mul] using congrArg ((F.reduce f).mapMatrix) hlocal

theorem preserves_product_one (i j : K) (h : A i * A j = 1) (f : ℕ) :
    F.matrix f i * F.matrix f j = 1 := by
  have hlocal : F.coefficients i * F.coefficients j = 1 := by
    apply F.rational_embedding_injective
    simpa only [map_mul, map_one, F.lift_correct] using h
  simpa only [matrix, map_mul, map_one] using
    congrArg ((F.reduce f).mapMatrix) hlocal

/-- Inverse identities are preserved because the actual inverse matrix was
included in the finite data before the prime was chosen.  Nonzero pivots are
not silently allowed to vanish under a denominator-only selection. -/
theorem preserves_two_sided_inverse (i j : K)
    (hleft : A i * A j = 1) (hright : A j * A i = 1) (f : ℕ) :
    F.matrix f i * F.matrix f j = 1 ∧
      F.matrix f j * F.matrix f i = 1 :=
  ⟨F.preserves_product_one i j hleft f,
    F.preserves_product_one j i hright f⟩

theorem preserves_factorization (target left pivot right : K)
    (h : A target = A left * A pivot * A right) (f : ℕ) :
    F.matrix f target = F.matrix f left * F.matrix f pivot * F.matrix f right := by
  have hlocal : F.coefficients target =
      F.coefficients left * F.coefficients pivot * F.coefficients right := by
    apply F.rational_embedding_injective
    simpa only [map_mul, F.lift_correct] using h
  simpa only [matrix, map_mul] using congrArg ((F.reduce f).mapMatrix) hlocal

theorem preserves_entry_zero (k : K) (i j : I) (h : A k i j = 0) (f : ℕ) :
    F.matrix f k i j = 0 := by
  have hentry : F.coefficients k i j = 0 := by
    apply intoRat_injective F.denominator F.denominator_ne_zero
    have hlift := congrArg (fun M : Matrix I I ℚ => M i j) (F.lift_correct k)
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, map_zero, h] using hlift
  change F.reduce f (F.coefficients k i j) = 0
  rw [hentry, map_zero]

theorem preserves_entry_one (k : K) (i j : I) (h : A k i j = 1) (f : ℕ) :
    F.matrix f k i j = 1 := by
  have hentry : F.coefficients k i j = 1 := by
    apply intoRat_injective F.denominator F.denominator_ne_zero
    have hlift := congrArg (fun M : Matrix I I ℚ => M i j) (F.lift_correct k)
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, map_one, h] using hlift
  change F.reduce f (F.coefficients k i j) = 1
  rw [hentry, map_one]

/-- Every nonzero supplied coefficient becomes a unit.  The construction
includes the denominators of its reciprocal before choosing the prime,
thereby protecting nonzero numerators as well as denominators. -/
theorem preserves_nonzero_entry_unit (k : K) (i j : I)
    (h : A k i j ≠ 0) (f : ℕ) : IsUnit (F.matrix f k i j) := by
  have hlocal : F.coefficients k i j * F.inverse_coefficients k i j = 1 := by
    apply intoRat_injective F.denominator F.denominator_ne_zero
    rw [map_mul, map_one, F.coefficient_spec, F.inverse_lift_correct]
    exact mul_inv_cancel₀ h
  apply isUnit_iff_exists_inv.mpr
  refine ⟨F.reduce f (F.inverse_coefficients k i j), ?_⟩
  change F.reduce f (F.coefficients k i j) *
    F.reduce f (F.inverse_coefficients k i j) = 1
  rw [← map_mul, hlocal, map_one]

theorem preserves_entry_nonzero (k : K) (i j : I)
    (h : A k i j ≠ 0) (f : ℕ) (hf : f ≠ 0) : F.matrix f k i j ≠ 0 := by
  letI : Fact (1 < F.prime ^ f) := ⟨Nat.one_lt_pow hf F.prime_is_prime.one_lt⟩
  exact (F.preserves_nonzero_entry_unit k i j h f).ne_zero

/-- The zero pattern expressing lower triangularity is retained. -/
theorem preserves_lower_triangular [LT I] (k : K)
    (h : ∀ i j, i < j → A k i j = 0) (f : ℕ) :
    ∀ i j, i < j → F.matrix f k i j = 0 := by
  intro i j hij
  exact F.preserves_entry_zero k i j (h i j hij) f

/-- A fixed 0/1 placement, including a partial permutation matrix, is retained
entry by entry.  The combinatorial condition on the placement need not be
reproved after changing the coefficient ring. -/
theorem preserves_zero_one_pattern (k : K) (pattern : I → I → Bool)
    (h : ∀ i j, A k i j = if pattern i j then 1 else 0) (f : ℕ) :
    ∀ i j, F.matrix f k i j = if pattern i j then 1 else 0 := by
  intro i j
  cases hp : pattern i j
  · apply F.preserves_entry_zero
    simpa [hp] using h i j
  · apply F.preserves_entry_one
    simpa [hp] using h i j

end SpecializedFamily

end MatrixFamilies

section PivotElimination

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A matrix with only column `r` potentially nonzero. -/
def columnSpike (r : I) (u : I → ℚ) : Matrix I I ℚ :=
  fun i j => if j = r then u i else 0

/-- A matrix with only row `c` potentially nonzero. -/
def rowSpike (c : I) (v : I → ℚ) : Matrix I I ℚ :=
  fun i j => if i = c then v j else 0

theorem columnSpike_mul (r : I) (u : I → ℚ) (A : Matrix I I ℚ) (i j : I) :
    (columnSpike r u * A) i j = u i * A r j := by
  simp [Matrix.mul_apply, columnSpike, ite_mul]

theorem mul_rowSpike (c : I) (v : I → ℚ) (A : Matrix I I ℚ) (i j : I) :
    (A * rowSpike c v) i j = A i c * v j := by
  simp [Matrix.mul_apply, rowSpike, mul_ite]

theorem columnSpike_square_zero (r : I) (u : I → ℚ) (hu : u r = 0) :
    columnSpike r u * columnSpike r u = 0 := by
  ext i j
  simp [columnSpike_mul, columnSpike, hu]

theorem rowSpike_square_zero (c : I) (v : I → ℚ) (hv : v c = 0) :
    rowSpike c v * rowSpike c v = 0 := by
  ext i j
  simp [mul_rowSpike, rowSpike, hv]

theorem one_add_square_zero_isUnit (N : Matrix I I ℚ) (hN : N * N = 0) :
    IsUnit (1 + N) := by
  apply isUnit_iff_exists.mpr
  refine ⟨1 - N, ?_, ?_⟩
  · simp [mul_sub, add_mul, hN]
  · simp [sub_mul, mul_add, hN]

def pivotColumnCorrection (A : Matrix I I ℚ) (r c : I) (i : I) : ℚ :=
  if i = r then 0 else -(A i c / A r c)

def pivotRowCorrection (A : Matrix I I ℚ) (r c : I) (j : I) : ℚ :=
  if j = c then 0 else -(A r j / A r c)

def pivotLeft (A : Matrix I I ℚ) (r c : I) : Matrix I I ℚ :=
  1 + columnSpike r (pivotColumnCorrection A r c)

def pivotRight (A : Matrix I I ℚ) (r c : I) : Matrix I I ℚ :=
  1 + rowSpike c (pivotRowCorrection A r c)

def pivotEliminate (A : Matrix I I ℚ) (r c : I) : Matrix I I ℚ :=
  pivotLeft A r c * A * pivotRight A r c

theorem pivotLeft_isUnit (A : Matrix I I ℚ) (r c : I) :
    IsUnit (pivotLeft A r c) := by
  apply one_add_square_zero_isUnit
  apply columnSpike_square_zero
  simp [pivotColumnCorrection]

theorem pivotRight_isUnit (A : Matrix I I ℚ) (r c : I) :
    IsUnit (pivotRight A r c) := by
  apply one_add_square_zero_isUnit
  apply rowSpike_square_zero
  simp [pivotRowCorrection]

theorem pivotLeft_apply (A : Matrix I I ℚ) (r c i j : I) :
    (pivotLeft A r c * A) i j = A i j + pivotColumnCorrection A r c i * A r j := by
  simp only [pivotLeft, add_mul, one_mul, Matrix.add_apply, columnSpike_mul]

theorem pivotLeft_row (A : Matrix I I ℚ) (r c j : I) :
    (pivotLeft A r c * A) r j = A r j := by
  simp [pivotLeft_apply, pivotColumnCorrection]

theorem pivotLeft_column (A : Matrix I I ℚ) (r c : I) (ha : A r c ≠ 0)
    (i : I) (hi : i ≠ r) : (pivotLeft A r c * A) i c = 0 := by
  rw [pivotLeft_apply]
  simp [pivotColumnCorrection, hi, div_mul_cancel₀ _ ha]

theorem pivotEliminate_apply (A : Matrix I I ℚ) (r c i j : I) :
    pivotEliminate A r c i j = (pivotLeft A r c * A) i j +
      (pivotLeft A r c * A) i c * pivotRowCorrection A r c j := by
  simp only [pivotEliminate, pivotRight, mul_add, mul_one, Matrix.add_apply, mul_rowSpike]

theorem pivotEliminate_pivot (A : Matrix I I ℚ) (r c : I) :
    pivotEliminate A r c r c = A r c := by
  simp [pivotEliminate_apply, pivotLeft_row, pivotRowCorrection]

theorem pivotEliminate_row (A : Matrix I I ℚ) (r c : I) (ha : A r c ≠ 0)
    (j : I) (hj : j ≠ c) : pivotEliminate A r c r j = 0 := by
  rw [pivotEliminate_apply, pivotLeft_row, pivotLeft_row]
  simp [pivotRowCorrection, hj, div_mul_cancel₀ _ ha, mul_comm (A r c)]

theorem pivotEliminate_column (A : Matrix I I ℚ) (r c : I) (ha : A r c ≠ 0)
    (i : I) (hi : i ≠ r) : pivotEliminate A r c i c = 0 := by
  simp [pivotEliminate_apply, pivotLeft_column A r c ha i hi]

/-- Off the isolated pivot row and column, elimination gives the actual
Schur-complement formula used for the recursive smaller matrix. -/
theorem pivotEliminate_complement (A : Matrix I I ℚ) (r c : I) (ha : A r c ≠ 0)
    (i j : I) (hi : i ≠ r) :
    pivotEliminate A r c i j = A i j - A i c * A r j / A r c := by
  rw [pivotEliminate_apply, pivotLeft_column A r c ha i hi]
  simp [pivotLeft_apply, pivotColumnCorrection, hi, div_mul_eq_mul_div, sub_eq_add_neg]

theorem pivotEliminate_rank (A : Matrix I I ℚ) (r c : I) :
    (pivotEliminate A r c).rank = A.rank := by
  unfold pivotEliminate
  rw [Matrix.rank_mul_eq_left_of_isUnit_det (pivotRight A r c)
    (pivotLeft A r c * A)
    ((Matrix.isUnit_iff_isUnit_det _).mp (pivotRight_isUnit A r c))]
  exact Matrix.rank_mul_eq_right_of_isUnit_det (pivotLeft A r c) A
    ((Matrix.isUnit_iff_isUnit_det _).mp (pivotLeft_isUnit A r c))

/-- Remove the isolated pivot column, leaving the smaller-rank residual. -/
def eraseColumn (B : Matrix I I ℚ) (c : I) : Matrix I I ℚ :=
  B * Matrix.diagonal (fun j => if j = c then 0 else 1)

@[simp] theorem eraseColumn_apply (B : Matrix I I ℚ) (c i j : I) :
    eraseColumn B c i j = if j = c then 0 else B i j := by
  simp only [eraseColumn, Matrix.mul_diagonal]
  split_ifs <;> simp

theorem eraseColumn_row_zero (B : Matrix I I ℚ) (r c : I)
    (hrow : ∀ j, j ≠ c → B r j = 0) (j : I) :
    eraseColumn B c r j = 0 := by
  by_cases hj : j = c
  · simp [hj]
  · simp [hj, hrow j hj]

/-- An isolated nonzero pivot contributes a dimension absent from the residual.
This proves genuine descent without assuming a matrix normal form. -/
theorem eraseColumn_rank_lt (B : Matrix I I ℚ) (r c : I)
    (hpivot : B r c ≠ 0) (hrow : ∀ j, j ≠ c → B r j = 0) :
    (eraseColumn B c).rank < B.rank := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_iff_le_not_ge.mpr
  constructor
  · intro y hy
    obtain ⟨x, hx⟩ := hy
    refine ⟨(Matrix.diagonal (fun j => if j = c then 0 else 1)).mulVec x, ?_⟩
    change B.mulVec ((Matrix.diagonal (fun j => if j = c then 0 else 1)).mulVec x) = y
    rw [Matrix.mulVec_mulVec]
    exact hx
  · intro hreverse
    have hmem : B.mulVec (Pi.single c 1) ∈ LinearMap.range B.mulVecLin :=
      ⟨Pi.single c 1, rfl⟩
    obtain ⟨x, hx⟩ := hreverse hmem
    have hz : ((eraseColumn B c).mulVec x) r = 0 := by
      simp only [Matrix.mulVec, dotProduct, eraseColumn_row_zero B r c hrow, zero_mul, Finset.sum_const_zero]
    have heq := congrFun hx r
    change ((eraseColumn B c).mulVec x) r = (B.mulVec (Pi.single c 1)) r at heq
    rw [hz, Matrix.mulVec_single_one] at heq
    exact hpivot heq.symm

/-- The concrete pivot-elimination step has a strictly smaller residual rank. -/
theorem pivotResidual_rank_lt (A : Matrix I I ℚ) (r c : I)
    (hpivot : A r c ≠ 0) :
    (eraseColumn (pivotEliminate A r c) c).rank < A.rank := by
  rw [← pivotEliminate_rank A r c]
  apply eraseColumn_rank_lt (pivotEliminate A r c) r c
  · simpa only [pivotEliminate_pivot] using hpivot
  · exact fun j hj => pivotEliminate_row A r c hpivot j hj

/-- A transformation leaves one coordinate untouched, both as an input and output. -/
def FixesCoordinate (M : Matrix I I ℚ) (k : I) : Prop :=
  (∀ j, M k j = (1 : Matrix I I ℚ) k j) ∧
  (∀ i, M i k = (1 : Matrix I I ℚ) i k)

theorem fixesCoordinate_one (k : I) : FixesCoordinate (1 : Matrix I I ℚ) k :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem fixesCoordinate_mul_row (M N : Matrix I I ℚ) (k : I)
    (hM : FixesCoordinate M k) (j : I) : (M * N) k j = N k j := by
  calc
    (M * N) k j = ((1 : Matrix I I ℚ) * N) k j := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro a _
      rw [hM.1 a]
    _ = N k j := by rw [one_mul]

theorem fixesCoordinate_mul_col (M N : Matrix I I ℚ) (k : I)
    (hN : FixesCoordinate N k) (i : I) : (M * N) i k = M i k := by
  calc
    (M * N) i k = (M * (1 : Matrix I I ℚ)) i k := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro a _
      rw [hN.2 a]
    _ = M i k := by rw [mul_one]

theorem fixesCoordinate_mul (M N : Matrix I I ℚ) (k : I)
    (hM : FixesCoordinate M k) (hN : FixesCoordinate N k) :
    FixesCoordinate (M * N) k := by
  constructor
  · intro j
    rw [fixesCoordinate_mul_row M N k hM j, hN.1 j]
  · intro i
    rw [fixesCoordinate_mul_col M N k hN i, hM.2 i]

theorem pivotLeft_fixes_zero_row (A : Matrix I I ℚ) (r c k : I)
    (ha : A r c ≠ 0) (hk : ∀ j, A k j = 0) :
    FixesCoordinate (pivotLeft A r c) k := by
  have hkr : k ≠ r := by
    intro heq
    subst k
    exact ha (hk c)
  constructor
  · intro j
    simp [pivotLeft, columnSpike, pivotColumnCorrection, hkr, hk c]
  · intro i
    simp [pivotLeft, columnSpike, hkr]

theorem pivotRight_fixes_zero_col (A : Matrix I I ℚ) (r c k : I)
    (ha : A r c ≠ 0) (hk : ∀ i, A i k = 0) :
    FixesCoordinate (pivotRight A r c) k := by
  have hkc : k ≠ c := by
    intro heq
    subst k
    exact ha (hk r)
  constructor
  · intro j
    simp [pivotRight, rowSpike, hkc]
  · intro i
    simp [pivotRight, rowSpike, pivotRowCorrection, hkc, hk r]

theorem pivotResidual_zero_row (A : Matrix I I ℚ) (r c k : I)
    (ha : A r c ≠ 0) (hk : ∀ j, A k j = 0) (j : I) :
    eraseColumn (pivotEliminate A r c) c k j = 0 := by
  have hrow : ∀ a, (pivotLeft A r c * A) k a = 0 := by
    intro a
    rw [fixesCoordinate_mul_row _ _ k (pivotLeft_fixes_zero_row A r c k ha hk) a]
    exact hk a
  simp only [eraseColumn_apply]
  split_ifs
  · rfl
  · simp [pivotEliminate, Matrix.mul_apply, hrow]

theorem pivotResidual_zero_col (A : Matrix I I ℚ) (r c k : I)
    (ha : A r c ≠ 0) (hk : ∀ i, A i k = 0) (i : I) :
    eraseColumn (pivotEliminate A r c) c i k = 0 := by
  have hcol : ∀ a, (A * pivotRight A r c) a k = 0 := by
    intro a
    rw [fixesCoordinate_mul_col _ _ k (pivotRight_fixes_zero_col A r c k ha hk) a]
    exact hk a
  simp only [eraseColumn_apply]
  split_ifs
  · rfl
  · change (pivotLeft A r c * A * pivotRight A r c) i k = 0
    rw [Matrix.mul_assoc]
    simp only [Matrix.mul_apply, hcol, mul_zero, Finset.sum_const_zero]

/-- A partial monomial matrix has at most one nonzero entry in every row and column. -/
def PartialMonomial (P : Matrix I I ℚ) : Prop :=
  (∀ i j k, P i j ≠ 0 → P i k ≠ 0 → j = k) ∧
  (∀ i j k, P i j ≠ 0 → P k j ≠ 0 → i = k)

def pivotEntry (r c : I) (a : ℚ) : Matrix I I ℚ :=
  fun i j => if i = r ∧ j = c then a else 0

theorem eraseColumn_add_pivotEntry (B : Matrix I I ℚ) (r c : I)
    (hcol : ∀ i, i ≠ r → B i c = 0) :
    eraseColumn B c + pivotEntry r c (B r c) = B := by
  ext i j
  by_cases hj : j = c
  · subst j
    by_cases hi : i = r
    · subst i; simp [pivotEntry]
    · simp [pivotEntry, hi, hcol i hi]
  · simp [pivotEntry, hj]

theorem fixesCoordinate_pivotEntry (L R : Matrix I I ℚ) (r c : I) (a : ℚ)
    (hL : FixesCoordinate L r) (hR : FixesCoordinate R c) :
    L * pivotEntry r c a * R = pivotEntry r c a := by
  have hleft : L * pivotEntry r c a = pivotEntry r c a := by
    ext i j
    by_cases hj : j = c
    · subst j
      simp only [Matrix.mul_apply, pivotEntry, and_true]
      simp_rw [mul_ite, mul_zero]
      simp [hL.2 i, Matrix.one_apply, eq_comm]
    · simp [Matrix.mul_apply, pivotEntry, hj]
  rw [hleft]
  ext i j
  by_cases hi : i = r
  · subst i
    simp only [Matrix.mul_apply, pivotEntry, true_and]
    simp_rw [ite_mul, zero_mul]
    simp [hR.1 j, Matrix.one_apply, eq_comm]
  · simp [Matrix.mul_apply, pivotEntry, hi]

theorem partialMonomial_add_pivot (P : Matrix I I ℚ) (r c : I) (a : ℚ)
    (hP : PartialMonomial P) (hrow : ∀ j, P r j = 0) (hcol : ∀ i, P i c = 0) :
    PartialMonomial (P + pivotEntry r c a) := by
  constructor
  · intro i j k hij hik
    by_cases hi : i = r
    · subst i
      have hj : j = c := by
        by_contra h
        exact hij (by simp [pivotEntry, hrow, h])
      have hk : k = c := by
        by_contra h
        exact hik (by simp [pivotEntry, hrow, h])
      exact hj.trans hk.symm
    · apply hP.1 i j k
      · simpa [pivotEntry, hi] using hij
      · simpa [pivotEntry, hi] using hik
  · intro i j k hij hkj
    by_cases hj : j = c
    · subst j
      have hi : i = r := by
        by_contra h
        exact hij (by simp [pivotEntry, hcol, h])
      have hk : k = r := by
        by_contra h
        exact hkj (by simp [pivotEntry, hcol, h])
      exact hi.trans hk.symm
    · apply hP.2 i j k
      · simpa [pivotEntry, hj] using hij
      · simpa [pivotEntry, hj] using hkj

section Ordered

variable [LinearOrder I]

def LowerTriangular (A : Matrix I I ℚ) : Prop := ∀ i j, i < j → A i j = 0

theorem pivotLeft_lower (A : Matrix I I ℚ) (r c : I)
    (hbefore : ∀ i, i < r → ∀ j, A i j = 0) : LowerTriangular (pivotLeft A r c) := by
  intro i j hij
  have hne : i ≠ j := ne_of_lt hij
  simp only [pivotLeft, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, columnSpike]
  split_ifs with hj
  · subst j
    simp [pivotColumnCorrection, hbefore i hij c]
  · rfl

theorem pivotRight_lower (A : Matrix I I ℚ) (r c : I)
    (hafter : ∀ j, c < j → A r j = 0) : LowerTriangular (pivotRight A r c) := by
  intro i j hij
  have hne : i ≠ j := ne_of_lt hij
  simp only [pivotRight, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, rowSpike]
  split_ifs with hi
  · subst i
    simp [pivotRowCorrection, hafter j hij]
  · rfl

/-- Every nonzero matrix has the extremal pivot required to make both
elimination matrices lower triangular: the first nonzero row and, within it,
the last nonzero column. -/
theorem exists_extremal_pivot (A : Matrix I I ℚ) (hA : A ≠ 0) :
    ∃ r c, A r c ≠ 0 ∧
      (∀ i, i < r → ∀ j, A i j = 0) ∧ (∀ j, c < j → A r j = 0) := by
  classical
  have hentry : ∃ i j, A i j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hA
    ext i j
    exact h i j
  let rows := Finset.univ.filter (fun i => ∃ j, A i j ≠ 0)
  have hrows : rows.Nonempty := by
    obtain ⟨i, j, hij⟩ := hentry
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨j, hij⟩⟩⟩
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image rows id hrows
  have hrentry : ∃ j, A r j ≠ 0 := (Finset.mem_filter.mp hr).2
  let cols := Finset.univ.filter (fun j => A r j ≠ 0)
  have hcols : cols.Nonempty := by
    obtain ⟨j, hj⟩ := hrentry
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image cols id hcols
  refine ⟨r, c, (Finset.mem_filter.mp hc).2, ?_, ?_⟩
  · intro i hi j
    by_contra hij
    have hmem : i ∈ rows := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨j, hij⟩⟩
    exact (not_le_of_gt hi) (hmin i hmem)
  · intro j hj
    by_contra hrj
    have hmem : j ∈ cols := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrj⟩
    exact (not_le_of_gt hj) (hmax j hmem)

/-- The actual first Gaussian step: two constructed lower triangular units
isolate a nonzero pivot while preserving the original matrix rank. -/
theorem exists_lower_pivot_elimination (A : Matrix I I ℚ) (hA : A ≠ 0) :
    ∃ (r c : I) (L R : Matrix I I ℚ),
      A r c ≠ 0 ∧ LowerTriangular L ∧ LowerTriangular R ∧ IsUnit L ∧ IsUnit R ∧
      (L * A * R).rank = A.rank ∧
      (L * A * R) r c = A r c ∧
      (∀ j, j ≠ c → (L * A * R) r j = 0) ∧
      (∀ i, i ≠ r → (L * A * R) i c = 0) := by
  obtain ⟨r, c, ha, hbefore, hafter⟩ := exists_extremal_pivot A hA
  refine ⟨r, c, pivotLeft A r c, pivotRight A r c, ha,
    pivotLeft_lower A r c hbefore, pivotRight_lower A r c hafter,
    pivotLeft_isUnit A r c, pivotRight_isUnit A r c,
    pivotEliminate_rank A r c, pivotEliminate_pivot A r c, ?_, ?_⟩
  · exact fun j hj => pivotEliminate_row A r c ha j hj
  · exact fun i hi => pivotEliminate_column A r c ha i hi

theorem lowerTriangular_one : LowerTriangular (1 : Matrix I I ℚ) := by
  intro i j hij
  exact Matrix.one_apply_ne (ne_of_lt hij)

theorem LowerTriangular.mul {L R : Matrix I I ℚ}
    (hL : LowerTriangular L) (hR : LowerTriangular R) : LowerTriangular (L * R) := by
  intro i j hij
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i < k
  · rw [hL i k hik, zero_mul]
  · rw [hR k j (lt_of_le_of_lt (le_of_not_gt hik) hij), mul_zero]

/-- Complete rank induction for a lower--partial-monomial--lower decomposition.
The zero-coordinate invariant ensures recursive pivots never disturb earlier pivots. -/
theorem exists_lower_partialMonomial_reduction (A : Matrix I I ℚ) :
    ∃ L R : Matrix I I ℚ,
      LowerTriangular L ∧ LowerTriangular R ∧ IsUnit L ∧ IsUnit R ∧
      PartialMonomial (L * A * R) ∧
      (∀ k, (∀ j, A k j = 0) → FixesCoordinate L k) ∧
      (∀ k, (∀ i, A i k = 0) → FixesCoordinate R k) := by
  generalize hn : A.rank = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases hA : A = 0
    · subst A
      refine ⟨1, 1, lowerTriangular_one, lowerTriangular_one, isUnit_one,
        isUnit_one, ?_, fun k _ => fixesCoordinate_one k, fun k _ => fixesCoordinate_one k⟩
      simp only [mul_zero, zero_mul]
      exact ⟨fun _ _ _ h => (h rfl).elim, fun _ _ _ h => (h rfl).elim⟩
    · obtain ⟨r, c, ha, hbefore, hafter⟩ := exists_extremal_pivot A hA
      let L := pivotLeft A r c
      let R := pivotRight A r c
      let B := pivotEliminate A r c
      let C := eraseColumn B c
      have hCr : ∀ j, C r j = 0 :=
        eraseColumn_row_zero B r c (fun j hj => pivotEliminate_row A r c ha j hj)
      have hCc : ∀ i, C i c = 0 := by intro i; simp [C]
      have hC_rank : C.rank < n := by
        rw [← hn]
        exact pivotResidual_rank_lt A r c ha
      obtain ⟨L', R', hL', hR', huL', huR', hP', hfixL', hfixR'⟩ :=
        ih C.rank hC_rank C rfl
      have hfixr := hfixL' r hCr
      have hfixc := hfixR' c hCc
      have hProw : ∀ j, (L' * C * R') r j = 0 := by
        intro j
        have hrow : ∀ k, (L' * C) r k = 0 := by
          intro k
          rw [fixesCoordinate_mul_row L' C r hfixr k, hCr k]
        simp only [Matrix.mul_apply, hrow, zero_mul, Finset.sum_const_zero]
      have hPcol : ∀ i, (L' * C * R') i c = 0 := by
        intro i
        rw [fixesCoordinate_mul_col (L' * C) R' c hfixc i]
        simp only [Matrix.mul_apply, hCc, mul_zero, Finset.sum_const_zero]
      have hsplit : C + pivotEntry r c (A r c) = B := by
        simpa only [C, B, pivotEliminate_pivot] using
          eraseColumn_add_pivotEntry B r c (fun i hi => pivotEliminate_column A r c ha i hi)
      have hproduct : (L' * L) * A * (R * R') =
          L' * C * R' + pivotEntry r c (A r c) := by
        calc
          (L' * L) * A * (R * R') = L' * B * R' := by
            simp only [B, pivotEliminate, L, R, Matrix.mul_assoc]
          _ = L' * (C + pivotEntry r c (A r c)) * R' := by rw [hsplit]
          _ = L' * C * R' + pivotEntry r c (A r c) := by
            rw [mul_add, add_mul, fixesCoordinate_pivotEntry L' R' r c (A r c) hfixr hfixc]
      refine ⟨L' * L, R * R', hL'.mul (pivotLeft_lower A r c hbefore),
        (pivotRight_lower A r c hafter).mul hR', huL'.mul (pivotLeft_isUnit A r c),
        (pivotRight_isUnit A r c).mul huR', ?_, ?_, ?_⟩
      · rw [hproduct]
        exact partialMonomial_add_pivot _ r c (A r c) hP' hProw hPcol
      · intro k hk
        exact fixesCoordinate_mul L' L k
          (hfixL' k (pivotResidual_zero_row A r c k ha hk))
          (pivotLeft_fixes_zero_row A r c k ha hk)
      · intro k hk
        exact fixesCoordinate_mul R R' k
          (pivotRight_fixes_zero_col A r c k ha hk)
          (hfixR' k (pivotResidual_zero_col A r c k ha hk))

theorem LowerTriangular.inv {L : Matrix I I ℚ}
    (hL : LowerTriangular L) (hu : IsUnit L) : LowerTriangular L⁻¹ := by
  cases hu.nonempty_invertible
  have hblock : L.BlockTriangular (OrderDual.toDual : I → OrderDual I) :=
    fun {_ _} hij => hL _ _ hij
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hblock
  exact fun _ _ hij => hi hij

/-- The unique nonzero value in a nonzero row; zero rows use the harmless value 1. -/
noncomputable def rowPivotValue (P : Matrix I I ℚ) (i : I) : ℚ :=
  if h : ∃ j, P i j ≠ 0 then P i (Classical.choose h) else 1

theorem rowPivotValue_ne_zero (P : Matrix I I ℚ) (i : I) : rowPivotValue P i ≠ 0 := by
  unfold rowPivotValue
  split_ifs with h
  · exact Classical.choose_spec h
  · exact one_ne_zero

theorem rowPivotValue_eq (P : Matrix I I ℚ) (hP : PartialMonomial P)
    (i j : I) (hij : P i j ≠ 0) : rowPivotValue P i = P i j := by
  have h : ∃ k, P i k ≠ 0 := ⟨j, hij⟩
  rw [rowPivotValue, dif_pos h]
  rw [hP.1 i (Classical.choose h) j (Classical.choose_spec h) hij]

noncomputable def normalizeRows (P : Matrix I I ℚ) : Matrix I I ℚ :=
  Matrix.diagonal (fun i => (rowPivotValue P i)⁻¹)

theorem normalizeRows_isUnit (P : Matrix I I ℚ) : IsUnit (normalizeRows P) := by
  apply Matrix.isUnit_diagonal.mpr
  refine isUnit_iff_exists.mpr ⟨rowPivotValue P, ?_, ?_⟩
  · ext i
    exact inv_mul_cancel₀ (rowPivotValue_ne_zero P i)
  · ext i
    exact mul_inv_cancel₀ (rowPivotValue_ne_zero P i)

theorem normalizeRows_lower (P : Matrix I I ℚ) : LowerTriangular (normalizeRows P) := by
  intro i j hij
  simp [normalizeRows, Matrix.diagonal_apply_ne _ (ne_of_lt hij)]

theorem normalized_entry (P : Matrix I I ℚ) (hP : PartialMonomial P) (i j : I) :
    (normalizeRows P * P) i j = if P i j = 0 then 0 else 1 := by
  rw [normalizeRows, Matrix.diagonal_mul]
  by_cases hij : P i j = 0
  · simp [hij]
  · simp [hij, rowPivotValue_eq P hP i j hij]

theorem normalized_partialMonomial (P : Matrix I I ℚ) (hP : PartialMonomial P) :
    PartialMonomial (normalizeRows P * P) := by
  constructor
  · intro i j k hij hik
    apply hP.1 i j k
    · intro hz
      exact hij (by simp [normalized_entry P hP, hz])
    · intro hz
      exact hik (by simp [normalized_entry P hP, hz])
  · intro i j k hij hkj
    apply hP.2 i j k
    · intro hz
      exact hij (by simp [normalized_entry P hP, hz])
    · intro hz
      exact hkj (by simp [normalized_entry P hP, hz])

/-- Exact LPL existence over the rationals: two invertible lower-triangular
factors and a 0/1 partial permutation matrix of the same rank as A. -/
theorem exists_lower_partialPermutation_factorization (A : Matrix I I ℚ) :
    ∃ E₁ P E₂ : Matrix I I ℚ,
      LowerTriangular E₁ ∧ LowerTriangular E₂ ∧ IsUnit E₁ ∧ IsUnit E₂ ∧
      PartialMonomial P ∧ (∀ i j, P i j = 0 ∨ P i j = 1) ∧
      A = E₁ * P * E₂ ∧ P.rank = A.rank := by
  obtain ⟨L, R, hL, hR, huL, huR, hP, _, _⟩ := exists_lower_partialMonomial_reduction A
  let T := L * A * R
  let N := normalizeRows T
  let L₀ := N * L
  have huN : IsUnit N := normalizeRows_isUnit T
  have huL₀ : IsUnit L₀ := huN.mul huL
  have hL₀ : LowerTriangular L₀ := (normalizeRows_lower T).mul hL
  let P := N * T
  have hPeq : P = L₀ * A * R := by simp only [P, L₀, T, Matrix.mul_assoc]
  have hdetL : IsUnit L₀.det := (Matrix.isUnit_iff_isUnit_det L₀).mp huL₀
  have hdetR : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp huR
  refine ⟨L₀⁻¹, P, R⁻¹, hL₀.inv huL₀, hR.inv huR, ?_, ?_,
    normalized_partialMonomial T hP, ?_, ?_, ?_⟩
  · exact isUnit_iff_exists.mpr ⟨L₀, Matrix.nonsing_inv_mul L₀ hdetL,
      Matrix.mul_nonsing_inv L₀ hdetL⟩
  · exact isUnit_iff_exists.mpr ⟨R, Matrix.nonsing_inv_mul R hdetR,
      Matrix.mul_nonsing_inv R hdetR⟩
  · intro i j
    change (normalizeRows T * T) i j = 0 ∨ (normalizeRows T * T) i j = 1
    rw [normalized_entry T hP]
    split_ifs <;> simp
  · rw [hPeq]
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul L₀ hdetL, one_mul,
      Matrix.mul_nonsing_inv_cancel_right R A hdetR]
  · rw [hPeq]
    rw [Matrix.rank_mul_eq_left_of_isUnit_det R (L₀ * A) hdetR]
    exact Matrix.rank_mul_eq_right_of_isUnit_det L₀ A hdetL

end Ordered

section PartialPermutationRank

/-- Positions occupied by the ones of a partial permutation matrix. -/
abbrev OnePosition (P : Matrix I I ℚ) := {p : I × I // P p.1 p.2 = 1}

def oneRow {P : Matrix I I ℚ} (k : OnePosition P) : I := k.1.1

def oneCol {P : Matrix I I ℚ} (k : OnePosition P) : I := k.1.2

theorem oneRow_injective (P : Matrix I I ℚ) (hP : PartialMonomial P) :
    Function.Injective (oneRow (P := P)) := by
  intro k l h
  apply Subtype.ext
  apply Prod.ext h
  apply hP.1 k.1.1 k.1.2 l.1.2
  · rw [k.2]; exact one_ne_zero
  · change k.1.1 = l.1.1 at h
    rw [h, l.2]; exact one_ne_zero

theorem oneCol_injective (P : Matrix I I ℚ) (hP : PartialMonomial P) :
    Function.Injective (oneCol (P := P)) := by
  intro k l h
  apply Subtype.ext
  apply Prod.ext _ h
  apply hP.2 k.1.1 k.1.2 l.1.1
  · rw [k.2]; exact one_ne_zero
  · change k.1.2 = l.1.2 at h
    rw [h, l.2]; exact one_ne_zero

def coordinateEmbedding {K : Type*} (f : K → I) : Matrix I K ℚ :=
  fun i k => if i = f k then 1 else 0

theorem coordinateEmbedding_leftInverse {K : Type*} [Fintype K] [DecidableEq K]
    (f : K → I) (hf : Function.Injective f) :
    (coordinateEmbedding f).transpose * coordinateEmbedding f = 1 := by
  ext k l
  simp [Matrix.mul_apply, coordinateEmbedding, Matrix.transpose_apply, ite_mul,
    Matrix.one_apply, hf.eq_iff, eq_comm]

theorem partialPermutation_factor (P : Matrix I I ℚ)
    (h01 : ∀ i j, P i j = 0 ∨ P i j = 1) :
    coordinateEmbedding (oneRow (P := P)) *
      (coordinateEmbedding (oneCol (P := P))).transpose = P := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : P i j = 0
  · rw [hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hi : i = oneRow k
    · have hj : j ≠ oneCol k := by
        intro hj
        have hentry := k.2
        change P (oneRow k) (oneCol k) = 1 at hentry
        rw [← hi, ← hj, hij] at hentry
        exact zero_ne_one hentry
      simp [coordinateEmbedding, Matrix.transpose_apply, hj]
    · simp [coordinateEmbedding, Matrix.transpose_apply, hi]
  · have hone := (h01 i j).resolve_left hij
    let k : OnePosition P := ⟨(i, j), hone⟩
    rw [Finset.sum_eq_single k]
    · simp [coordinateEmbedding, Matrix.transpose_apply, oneRow, oneCol, k, hone]
    · intro l _ hl
      by_cases hi : i = oneRow l
      · have hj : j ≠ oneCol l := by
          intro hj
          apply hl
          apply Subtype.ext
          exact Prod.ext hi.symm hj.symm
        simp [coordinateEmbedding, Matrix.transpose_apply, hj]
      · simp [coordinateEmbedding, Matrix.transpose_apply, hi]
    · simp

/-- The rank of a 0/1 partial permutation is exactly its number of ones. -/
theorem partialPermutation_rank (P : Matrix I I ℚ) (hP : PartialMonomial P)
    (h01 : ∀ i j, P i j = 0 ∨ P i j = 1) :
    P.rank = Fintype.card (OnePosition P) := by
  let U := coordinateEmbedding (oneRow (P := P))
  let V := (coordinateEmbedding (oneCol (P := P))).transpose
  have hU : U.transpose * U = 1 :=
    coordinateEmbedding_leftInverse _ (oneRow_injective P hP)
  have hV : V * V.transpose = 1 := by
    simp only [V, Matrix.transpose_transpose]
    exact coordinateEmbedding_leftInverse _ (oneCol_injective P hP)
  calc
    P.rank = (U * V).rank := congrArg Matrix.rank (partialPermutation_factor P h01).symm
    _ = Fintype.card (OnePosition P) :=
      CSL.TensorLabels.rank_of_split_factors U V U.transpose V.transpose hU hV

/-- The 0/1 support pattern transported to any coefficient ring. -/
def patternMatrix (P : Matrix I I ℚ) (S : Type*) [Zero S] [One S] : Matrix I I S :=
  fun i j => if P i j = 1 then 1 else 0

def unitEntry (S : Type*) [Zero S] [One S] (r c : I) : Matrix I I S :=
  fun i j => if i = r ∧ j = c then 1 else 0

/-- One unit coordinate shear for every one of P, in a fixed finite list. -/
noncomputable def unitShears (P : Matrix I I ℚ) (S : Type*) [Zero S] [One S] :
    List (Matrix I I S) :=
  (Finset.univ : Finset (OnePosition P)).toList.map
    (fun k => unitEntry S (oneRow k) (oneCol k))

theorem unitShears_length (P : Matrix I I ℚ) (hP : PartialMonomial P)
    (h01 : ∀ i j, P i j = 0 ∨ P i j = 1) (S : Type*) [Zero S] [One S] :
    (unitShears P S).length = P.rank := by
  rw [partialPermutation_rank P hP h01]
  simp [unitShears]

theorem unitShears_sum (P : Matrix I I ℚ) (S : Type*) [AddCommMonoid S] [One S] :
    (unitShears P S).sum = patternMatrix P S := by
  unfold unitShears
  rw [Finset.sum_map_toList]
  ext i j
  simp only [Matrix.sum_apply, patternMatrix]
  by_cases hij : P i j = 1
  · let k : OnePosition P := ⟨(i, j), hij⟩
    rw [if_pos hij, Finset.sum_eq_single k]
    · simp [unitEntry, oneRow, oneCol, k]
    · intro l _ hl
      have hne : ¬(i = oneRow l ∧ j = oneCol l) := by
        intro h
        apply hl
        apply Subtype.ext
        exact Prod.ext h.1.symm h.2.symm
      simp [unitEntry, hne]
    · simp
  · rw [if_neg hij]
    apply Finset.sum_eq_zero
    intro k _
    have hne : ¬(i = oneRow k ∧ j = oneCol k) := by
      intro h
      apply hij
      have hk := k.2
      change P (oneRow k) (oneCol k) = 1 at hk
      rw [← h.1, ← h.2] at hk
      exact hk
    simp [unitEntry, hne]

theorem unitEntry_mulVec (S : Type*) [Semiring S] (r c : I) (d : I → S) (i : I) :
    (unitEntry S r c).mulVec d i = if i = r then d c else 0 := by
  by_cases hi : i = r
  · subst i
    simp [unitEntry, Matrix.mulVec, dotProduct, ite_mul]
  · simp [unitEntry, Matrix.mulVec, dotProduct, hi]

theorem list_sum_mulVec (S : Type*) [Semiring S] (Ms : List (Matrix I I S)) :
    (Ms.map Matrix.mulVec).sum = Ms.sum.mulVec := by
  induction Ms with
  | nil =>
    ext x i
    simp [Matrix.zero_mulVec]
  | cons M Ms ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ext x i
    exact (congrFun (Matrix.add_mulVec M Ms.sum x) i).symm

/-- Executing the concrete list of unit shears realizes the entire support matrix. -/
theorem unitShears_execute (P : Matrix I I ℚ) (S : Type*) [Ring S] {Value : Type*}
    (F : (I → S) × (I → S) → Value) :
    CSL.Address.applyShears ((unitShears P S).map Matrix.mulVec) F =
      CSL.Address.matrixPhi (patternMatrix P S) F := by
  rw [CSL.Address.applyShears_sum, list_sum_mulVec, unitShears_sum]
  rfl

end PartialPermutationRank

section SpecializedShears

variable {K : Type*} [Fintype K] {A : K → Matrix I I ℚ}

/-- A specialized 0/1 matrix is precisely the same combinatorial support pattern. -/
theorem SpecializedFamily.partialPermutation_pattern (F : SpecializedFamily A) (k : K)
    (h01 : ∀ i j, A k i j = 0 ∨ A k i j = 1) (f : ℕ) :
    F.matrix f k = patternMatrix (A k) (ZMod (F.prime ^ f)) := by
  ext i j
  rcases h01 i j with hzero | hone
  · rw [F.preserves_entry_zero k i j hzero f]
    simp [patternMatrix, hzero]
  · rw [F.preserves_entry_one k i j hone f]
    simp [patternMatrix, hone]

/-- For every prime power, exactly rank_Q(P) unit coordinate shears implement
its actual specialization, with no unproved assumption about the number of ones. -/
theorem SpecializedFamily.unitShears_correct (F : SpecializedFamily A) (k : K)
    (hP : PartialMonomial (A k)) (h01 : ∀ i j, A k i j = 0 ∨ A k i j = 1)
    (f : ℕ) {Value : Type*} (stream : (I → ZMod (F.prime ^ f)) ×
      (I → ZMod (F.prime ^ f)) → Value) :
    (unitShears (A k) (ZMod (F.prime ^ f))).length = (A k).rank ∧
    CSL.Address.applyShears
      ((unitShears (A k) (ZMod (F.prime ^ f))).map Matrix.mulVec) stream =
      CSL.Address.matrixPhi (F.matrix f k) stream := by
  constructor
  · exact unitShears_length (A k) hP h01 _
  · rw [F.partialPermutation_pattern k h01 f]
    exact unitShears_execute (A k) _ stream

end SpecializedShears

end PivotElimination

end CSL.MatrixFactorization


