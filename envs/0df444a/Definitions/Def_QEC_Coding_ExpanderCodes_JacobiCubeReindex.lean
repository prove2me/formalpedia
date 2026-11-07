-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
-- name    : QEC_Coding_ExpanderCodes_JacobiCubeReindex
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T22:11:47.5866+00:00
-- url     : https://prove2.me/theorems/ef1abce1-c213-4076-a0d5-4110633d74c4
-- title:
--   Jacobi Cube Reindex
-- statement:
--   Definitions and structural lemmas for Jacobi Cube Reindex, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedSquareSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiWeightedTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSixProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiEulerSquareProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiThetaProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_jacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalBilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalIntegerThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_constantCoeff_rationalTriangularThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_integerTriangularRoots_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inl
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiParityReindex_inr
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobi_oppositeParity_exponent
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobi_oppositeParity_weight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobi_sameParity_exponent
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobi_sameParity_weight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_mem_integerTriangularRoots_iff
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedSquareSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiWeightedTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSixProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiEulerSquareProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiThetaProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_jacobiTriangularProduct
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalBilateralTriangularSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalIntegerThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.constantCoeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.integerTriangularRoots_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inl
attribute [local simp] QEC.Coding.TannerLiftedProduct.jacobiParityReindex_inr
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
abbrev JacobiReindexedPair (n : ℕ) :=
  {p : ℤ × ℤ // p.1 ^ 2 + p.1 + p.2 ^ 2 = n}
abbrev JacobiCubePair (n : ℕ) :=
  {p : ℤ × ℤ //
    p.1 ^ 2 + p.1 + p.2 ^ 2 + p.2 = 2 * n}
noncomputable def jacobiReindexedPairs (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-((n : ℤ)) - 1) (n : ℤ)) ×ˢ
      Finset.Icc (-(n : ℤ)) (n : ℤ)).filter fun p =>
    p.1 ^ 2 + p.1 + p.2 ^ 2 = n
theorem mem_jacobiReindexedPairs_iff (n : ℕ) (p : ℤ × ℤ) :
    p ∈ jacobiReindexedPairs n ↔
      p.1 ^ 2 + p.1 + p.2 ^ 2 = n := by
  rw [jacobiReindexedPairs, Finset.mem_filter]
  refine and_iff_right_of_imp fun hp => ?_
  simp only [Finset.mem_product, Finset.mem_Icc]
  have hn : (0 : ℤ) ≤ n := by positivity
  have hs_nonneg : 0 ≤ p.1 ^ 2 + p.1 := by
    by_cases hs : 0 ≤ p.1
    · nlinarith [sq_nonneg p.1]
    · have hs' : p.1 ≤ -1 := by omega
      nlinarith [sq_nonneg (p.1 + 1)]
  have ht_sq : p.2 ^ 2 ≤ n := by nlinarith
  have hs_tri : p.1 ^ 2 + p.1 ≤ n := by
    nlinarith [sq_nonneg p.2]
  constructor
  · constructor
    · by_cases hs : -1 ≤ p.1
      · omega
      · nlinarith [sq_nonneg (p.1 + 1)]
    · by_cases hs : p.1 ≤ 0
      · omega
      · nlinarith [sq_nonneg p.1]
  · constructor <;> nlinarith [sq_nonneg p.2]
noncomputable instance (n : ℕ) : Fintype (JacobiReindexedPair n) :=
  Fintype.ofEquiv
    {p : ℤ × ℤ // p ∈ jacobiReindexedPairs n}
    (Equiv.subtypeEquivRight fun p => mem_jacobiReindexedPairs_iff n p)
noncomputable def jacobiCubePairEquiv (n : ℕ) :
    (JacobiReindexedPair n ⊕ JacobiReindexedPair n) ≃ JacobiCubePair n :=
  let P : (ℤ × ℤ) ⊕ (ℤ × ℤ) → Prop
    | .inl p => p.1 ^ 2 + p.1 + p.2 ^ 2 = n
    | .inr p => p.1 ^ 2 + p.1 + p.2 ^ 2 = n
  let Q : ℤ × ℤ → Prop := fun p =>
    p.1 ^ 2 + p.1 + p.2 ^ 2 + p.2 = 2 * n
  Equiv.subtypeSum.symm.trans <|
    jacobiParityReindex.subtypeEquiv (p := P) (q := Q) fun p => by
      cases p with
      | inl p =>
          change p.1 ^ 2 + p.1 + p.2 ^ 2 = n ↔ _
          rw [jacobiParityReindex_inl]
          change p.1 ^ 2 + p.1 + p.2 ^ 2 = n ↔
            (p.1 + p.2) ^ 2 + (p.1 + p.2) +
              (p.1 - p.2) ^ 2 + (p.1 - p.2) = 2 * n
          rw [jacobi_sameParity_exponent]
          omega
      | inr p =>
          change p.1 ^ 2 + p.1 + p.2 ^ 2 = n ↔ _
          rw [jacobiParityReindex_inr]
          change p.1 ^ 2 + p.1 + p.2 ^ 2 = n ↔
            (p.1 + p.2) ^ 2 + (p.1 + p.2) +
              (p.2 - p.1 - 1) ^ 2 + (p.2 - p.1 - 1) = 2 * n
          rw [jacobi_oppositeParity_exponent]
          omega
noncomputable instance (n : ℕ) : Fintype (JacobiCubePair n) :=
  Fintype.ofEquiv
    (JacobiReindexedPair n ⊕ JacobiReindexedPair n)
    (jacobiCubePairEquiv n)
@[simp] theorem jacobiCubePairEquiv_inl_val (n : ℕ)
    (p : JacobiReindexedPair n) :
    (jacobiCubePairEquiv n (Sum.inl p)).1 =
      (p.1.1 + p.1.2, p.1.1 - p.1.2) := by
  rfl
@[simp] theorem jacobiCubePairEquiv_inr_val (n : ℕ)
    (p : JacobiReindexedPair n) :
    (jacobiCubePairEquiv n (Sum.inr p)).1 =
      (p.1.1 + p.1.2, p.1.2 - p.1.1 - 1) := by
  rfl
def jacobiParitySign (z : ℤ) : ℚ :=
  if Even z then 1 else -1
theorem jacobiParitySign_same_chart (s t : ℤ) :
    jacobiParitySign ((s + t) + (s - t)) = 1 := by
  rw [jacobiParitySign, if_pos]
  exact ⟨s, by ring⟩
theorem jacobiParitySign_opposite_chart (s t : ℤ) :
    jacobiParitySign ((s + t) + (t - s - 1)) = -1 := by
  rw [jacobiParitySign, if_neg]
  intro h
  obtain ⟨r, hr⟩ := h
  omega
def jacobiCubePairWeight (p : ℤ × ℤ) : ℚ :=
  jacobiParitySign (p.1 + p.2) *
    (2 * (p.1 : ℚ) + 1) * (2 * (p.2 : ℚ) + 1)
def jacobiReindexedPairWeight (p : ℤ × ℤ) : ℚ :=
  (2 * (p.1 : ℚ) + 1) ^ 2 - (2 * (p.2 : ℚ)) ^ 2
@[simp] theorem jacobiCubePairWeight_equiv_inl (n : ℕ)
    (p : JacobiReindexedPair n) :
    jacobiCubePairWeight (jacobiCubePairEquiv n (Sum.inl p)).1 =
      jacobiReindexedPairWeight p.1 := by
  rcases p with ⟨⟨s, t⟩, hp⟩
  simp only [jacobiCubePairEquiv_inl_val, jacobiCubePairWeight,
    jacobiReindexedPairWeight, jacobiParitySign_same_chart,
    one_mul]
  exact_mod_cast jacobi_sameParity_weight s t
@[simp] theorem jacobiCubePairWeight_equiv_inr (n : ℕ)
    (p : JacobiReindexedPair n) :
    jacobiCubePairWeight (jacobiCubePairEquiv n (Sum.inr p)).1 =
      jacobiReindexedPairWeight p.1 := by
  rcases p with ⟨⟨s, t⟩, hp⟩
  simp only [jacobiCubePairEquiv_inr_val, jacobiCubePairWeight,
    jacobiReindexedPairWeight, jacobiParitySign_opposite_chart,
    neg_one_mul]
  exact_mod_cast jacobi_oppositeParity_weight s t
def jacobiHalfTriangularDegree (z : ℤ) : ℕ :=
  ((z ^ 2 + z) / 2).toNat
theorem two_mul_jacobiHalfTriangularDegree (z : ℤ) :
    2 * (jacobiHalfTriangularDegree z : ℤ) = z ^ 2 + z := by
  have hnonneg : 0 ≤ z ^ 2 + z := by
    by_cases hz : 0 ≤ z
    · nlinarith [sq_nonneg z]
    · have hz' : z ≤ -1 := by omega
      nlinarith [sq_nonneg (z + 1)]
  have heven : Even (z ^ 2 + z) := by
    simpa [pow_two, mul_add] using Int.even_mul_succ_self z
  have hhalf : 2 * ((z ^ 2 + z) / 2) = z ^ 2 + z :=
    Int.two_mul_ediv_two_of_even heven
  have hhalf_nonneg : 0 ≤ (z ^ 2 + z) / 2 := by nlinarith
  rw [jacobiHalfTriangularDegree, Int.toNat_of_nonneg hhalf_nonneg]
  exact hhalf
theorem mem_integerTriangularRoots_two_mul_degree (z : ℤ) :
    z ∈ integerTriangularRoots (2 * jacobiHalfTriangularDegree z) := by
  rw [mem_integerTriangularRoots_iff]
  rw [← two_mul_jacobiHalfTriangularDegree z]
  norm_num
theorem jacobiHalfTriangularDegree_eq_of_mem
    {n : ℕ} {z : ℤ} (hz : z ∈ integerTriangularRoots (2 * n)) :
    jacobiHalfTriangularDegree z = n := by
  have hz' := (mem_integerTriangularRoots_iff (2 * n) z).mp hz
  have hd := two_mul_jacobiHalfTriangularDegree z
  norm_num at hz' hd
  omega
theorem two_mul_jacobiHalfTriangularDegree_eq_of_mem
    {n : ℕ} {z : ℤ} (hz : z ∈ integerTriangularRoots n) :
    2 * jacobiHalfTriangularDegree z = n := by
  rw [← Nat.cast_inj (R := ℤ)]
  push_cast
  rw [two_mul_jacobiHalfTriangularDegree]
  exact (mem_integerTriangularRoots_iff n z).mp hz
def jacobiSquareDegree (z : ℤ) : ℕ := z.natAbs ^ 2
theorem jacobiSquareDegree_cast (z : ℤ) :
    (jacobiSquareDegree z : ℤ) = z ^ 2 := by
  simp [jacobiSquareDegree]
theorem mem_integerSquareRoots_jacobiSquareDegree (z : ℤ) :
    z ∈ integerSquareRoots (jacobiSquareDegree z) := by
  rw [mem_integerSquareRoots_iff, ← jacobiSquareDegree_cast]
theorem jacobiSquareDegree_eq_of_mem
    {n : ℕ} {z : ℤ} (hz : z ∈ integerSquareRoots n) :
    jacobiSquareDegree z = n := by
  rw [← Nat.cast_inj (R := ℤ), jacobiSquareDegree_cast]
  exact (mem_integerSquareRoots_iff n z).mp hz
abbrev JacobiCubeCoeffWitness (n : ℕ) :=
  Σ ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n},
    {k : ℤ // k ∈ integerTriangularRoots (2 * ij.1.1)} ×
      {l : ℤ // l ∈ integerTriangularRoots (2 * ij.1.2)}
noncomputable def jacobiCubeCoeffWitnessEquiv (n : ℕ) :
    JacobiCubeCoeffWitness n ≃ JacobiCubePair n where
  toFun w := ⟨(w.2.1.1, w.2.2.1), by
    have hk := (mem_integerTriangularRoots_iff
      (2 * w.1.1.1) w.2.1.1).mp w.2.1.2
    have hl := (mem_integerTriangularRoots_iff
      (2 * w.1.1.2) w.2.2.1).mp w.2.2.2
    have hij := Finset.mem_antidiagonal.mp w.1.2
    norm_num at hk hl
    have hijz : (w.1.1.1 : ℤ) + (w.1.1.2 : ℤ) = n := by
      exact_mod_cast hij
    calc
      w.2.1.1 ^ 2 + w.2.1.1 + w.2.2.1 ^ 2 + w.2.2.1 =
          2 * (w.1.1.1 : ℤ) + 2 * (w.1.1.2 : ℤ) := by nlinarith
      _ = 2 * n := by nlinarith⟩
  invFun p :=
    ⟨⟨(jacobiHalfTriangularDegree p.1.1,
          jacobiHalfTriangularDegree p.1.2), by
        rw [Finset.mem_antidiagonal]
        have hk := two_mul_jacobiHalfTriangularDegree p.1.1
        have hl := two_mul_jacobiHalfTriangularDegree p.1.2
        omega⟩,
      ⟨⟨p.1.1, mem_integerTriangularRoots_two_mul_degree p.1.1⟩,
        ⟨p.1.2, mem_integerTriangularRoots_two_mul_degree p.1.2⟩⟩⟩
  left_inv w := by
    rcases w with ⟨⟨⟨i, j⟩, hij⟩, ⟨⟨k, hk⟩, ⟨l, hl⟩⟩⟩
    have hi := jacobiHalfTriangularDegree_eq_of_mem hk
    have hj := jacobiHalfTriangularDegree_eq_of_mem hl
    change jacobiHalfTriangularDegree k = i at hi
    change jacobiHalfTriangularDegree l = j at hj
    subst i
    subst j
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl
abbrev JacobiReindexedCoeffWitness (n : ℕ) :=
  Σ ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n},
    {t : ℤ // t ∈ integerSquareRoots ij.1.1} ×
      {s : ℤ // s ∈ integerTriangularRoots ij.1.2}
noncomputable def jacobiReindexedCoeffWitnessEquiv (n : ℕ) :
    JacobiReindexedCoeffWitness n ≃ JacobiReindexedPair n where
  toFun w := ⟨(w.2.2.1, w.2.1.1), by
    have ht := (mem_integerSquareRoots_iff w.1.1.1 w.2.1.1).mp w.2.1.2
    have hs := (mem_integerTriangularRoots_iff w.1.1.2 w.2.2.1).mp w.2.2.2
    have hij := Finset.mem_antidiagonal.mp w.1.2
    have hijz : (w.1.1.1 : ℤ) + (w.1.1.2 : ℤ) = n := by
      exact_mod_cast hij
    nlinarith⟩
  invFun p :=
    ⟨⟨(jacobiSquareDegree p.1.2,
          2 * jacobiHalfTriangularDegree p.1.1), by
        rw [Finset.mem_antidiagonal]
        have ht := jacobiSquareDegree_cast p.1.2
        have hs := two_mul_jacobiHalfTriangularDegree p.1.1
        rw [← Nat.cast_inj (R := ℤ)]
        push_cast
        nlinarith [p.2]⟩,
      ⟨⟨p.1.2, mem_integerSquareRoots_jacobiSquareDegree p.1.2⟩,
        ⟨p.1.1, mem_integerTriangularRoots_two_mul_degree p.1.1⟩⟩⟩
  left_inv w := by
    rcases w with ⟨⟨⟨i, j⟩, hij⟩, ⟨⟨t, ht⟩, ⟨s, hs⟩⟩⟩
    have hi := jacobiSquareDegree_eq_of_mem ht
    have hj := two_mul_jacobiHalfTriangularDegree_eq_of_mem hs
    change jacobiSquareDegree t = i at hi
    change 2 * jacobiHalfTriangularDegree s = j at hj
    subst i
    subst j
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl
noncomputable def jacobiSignedCubeSeriesRaw : ℚ⟦X⟧ :=
  PowerSeries.mk fun n =>
    ∑ z : {z : ℤ // z ∈ integerTriangularRoots (2 * n)},
      jacobiParitySign z.1 * (2 * (z.1 : ℚ) + 1)
noncomputable def jacobiSignedCubeSeries : ℚ⟦X⟧ :=
  PowerSeries.C (1 / 2 : ℚ) * jacobiSignedCubeSeriesRaw
def jacobiCubeCoeffWitnessWeight {n : ℕ}
    (w : JacobiCubeCoeffWitness n) : ℚ :=
  (jacobiParitySign w.2.1.1 * (2 * (w.2.1.1 : ℚ) + 1)) *
    (jacobiParitySign w.2.2.1 * (2 * (w.2.2.1 : ℚ) + 1))
end QEC.Coding.TannerLiftedProduct


