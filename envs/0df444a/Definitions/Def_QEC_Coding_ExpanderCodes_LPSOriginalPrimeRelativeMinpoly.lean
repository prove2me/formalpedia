-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeRelativeMinpoly
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalPrimeRelativeMinpoly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:15:29.526856+00:00
-- url     : https://prove2.me/theorems/78984f25-8c82-4991-9e1c-cd7ba5fe577f
-- title:
--   LPSOriginal Prime Relative Minpoly
-- statement:
--   Definitions and structural lemmas for LPSOriginal Prime Relative Minpoly, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeRelativeMinpoly.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_level_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalJN_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_integralQ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNIntegerFractionEval_X
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_degree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_productLevelFractionRoot
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
lemma lpsOriginalPrimeProductJN_minpoly_natDegree
    (N p : ℕ) [NeZero N] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (minpoly (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalJNInFractionField (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos))).natDegree = p+1 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let K := lpsOriginalGeneratedFunctionFieldQ N hN
  let x := lpsOriginalJNInFractionField (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  have hx : IsIntegral K x :=
    (lpsOriginalJNInFractionField_integralQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).tower_top
  have hl := lpsOriginalGeneratedFunctionFieldQ_level_le N (N*p)
    (dvd_mul_right N p) h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  have he : (lpsOriginalGeneratedFunctionFieldQ N hN).relfinrank
      (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)) = (minpoly K x).natDegree := by
    rw [IntermediateField.relfinrank_eq_finrank_of_le hl]
    change Module.finrank K (IntermediateField.extendScalars
      (show K ≤ IntermediateField.adjoin (FractionRing (Polynomial ℚ)) {x} from hl)) = _
    rw [IntermediateField.extendScalars_adjoin]
    exact IntermediateField.adjoin.finrank hx
  exact he.symm.trans (lpsOriginalPrimeGeneratedFunctionFieldQ_relfinrank N p hNp h4N hN)
def lpsOriginalPrimeRelativeCoefficientMap (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Polynomial ℤ →+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact Polynomial.eval₂RingHom (Int.castRingHom _)
    (lpsOriginalIntegerNormalJN N hN).val
def lpsOriginalPrimeRelativeModularPolynomial
    (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Polynomial (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (lpsOriginalIntegerPolynomial p hp).map
    (lpsOriginalPrimeRelativeCoefficientMap N hN)
lemma lpsOriginalPrimeRelativeModularPolynomial_monic
    (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalPrimeRelativeModularPolynomial N p hN hp).Monic := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (lpsOriginalIntegerPolynomial_monic p hp).map _
lemma lpsOriginalPrimeRelativeCoefficientMap_ambient
    (N : ℕ) [NeZero N] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hN).val.toRingHom.comp
      (lpsOriginalPrimeRelativeCoefficientMap N hN) =
      lpsOriginalJNIntegerFractionEval N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply Polynomial.ringHom_ext
  · intro z
    have hz : Polynomial.C z = (z : Polynomial ℤ) := by simp
    rw [hz, map_intCast, map_intCast]
  · simp only [RingHom.comp_apply, lpsOriginalPrimeRelativeCoefficientMap,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rw [lpsOriginalJNIntegerFractionEval_X]
    exact lpsOriginalIntegerNormalJN_coe N hN
lemma lpsOriginalPrimeRelativeModularPolynomial_root
    (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Polynomial.aeval (lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN hp))
      (lpsOriginalPrimeRelativeModularPolynomial N p hN hp) = 0 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [Polynomial.aeval_def, lpsOriginalPrimeRelativeModularPolynomial,
    Polynomial.eval₂_map]
  change (lpsOriginalIntegerPolynomial p hp).eval₂
    ((lpsOriginalGeneratedFunctionFieldQ N hN).val.toRingHom.comp
      (lpsOriginalPrimeRelativeCoefficientMap N hN))
      (lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN hp)) = 0
  rw [lpsOriginalPrimeRelativeCoefficientMap_ambient,
    lpsOriginalPrimeIntegerPolynomial_productLevelFractionRoot]
lemma lpsOriginalPrimeRelativeModularPolynomial_natDegree
    (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalPrimeRelativeModularPolynomial N p hN
      (Fact.out : p.Prime).pos).natDegree = p+1 := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change ((lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
    (lpsOriginalPrimeRelativeCoefficientMap N hN)).natDegree = _
  rw [(lpsOriginalIntegerPolynomial_monic p (Fact.out : p.Prime).pos).natDegree_map,
    lpsOriginalPrimeIntegerPolynomial_degree]
lemma lpsOriginalPrimeRelativeModularPolynomial_eq_minpoly
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalPrimeRelativeModularPolynomial N p hN (Fact.out : p.Prime).pos =
      minpoly (lpsOriginalGeneratedFunctionFieldQ N hN)
        (lpsOriginalJNInFractionField (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let K := lpsOriginalGeneratedFunctionFieldQ N hN
  let x := lpsOriginalJNInFractionField (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  have hx : IsIntegral K x :=
    (lpsOriginalJNInFractionField_integralQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).tower_top
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hx)
    (lpsOriginalPrimeRelativeModularPolynomial_monic N p hN (Fact.out : p.Prime).pos)
    (minpoly.dvd K x (lpsOriginalPrimeRelativeModularPolynomial_root N p hN
      (Fact.out : p.Prime).pos))
  rw [lpsOriginalPrimeRelativeModularPolynomial_natDegree,
    lpsOriginalPrimeProductJN_minpoly_natDegree N p hNp h4N hN]
def lpsOriginalPrimeRelativeAdjoinRootEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    AdjoinRoot (lpsOriginalPrimeRelativeModularPolynomial N p hN
      (Fact.out : p.Prime).pos) ≃+*
        lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let K := lpsOriginalGeneratedFunctionFieldQ N hN
  let x := lpsOriginalJNInFractionField (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  have hx : IsIntegral K x :=
    (lpsOriginalJNInFractionField_integralQ (N*p)
      (Nat.mul_pos hN (Fact.out : p.Prime).pos)).tower_top
  let h := lpsOriginalGeneratedFunctionFieldQ_level_le N (N*p) (dvd_mul_right N p)
    h4N hN (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  change AdjoinRoot (lpsOriginalPrimeRelativeModularPolynomial N p hN
    (Fact.out : p.Prime).pos) ≃+* IntermediateField.extendScalars
      (show K ≤ IntermediateField.adjoin (FractionRing (Polynomial ℚ)) {x} from h)
  exact ((AdjoinRoot.algEquivOfEq K _ _
    (lpsOriginalPrimeRelativeModularPolynomial_eq_minpoly N p hNp h4N hN)).trans
    ((IntermediateField.adjoinRootEquivAdjoin K hx).trans
      (IntermediateField.equivOfEq (IntermediateField.extendScalars_adjoin
        (show K ≤ IntermediateField.adjoin (FractionRing (Polynomial ℚ)) {x} from h)).symm))).toRingEquiv
end
end QEC.Coding.TannerLiftedProduct


