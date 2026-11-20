-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:28:35.038187+00:00
-- url     : https://prove2.me/theorems/053d7edd-88a5-4b20-9ace-8683509e75ca
-- title:
--   LPSOriginal Relative Gauss Normalization Branches
-- statement:
--   Definitions and structural lemmas for LPSOriginal Relative Gauss Normalization Branches, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalizationBranches.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
abbrev LPSOriginalRelativeGaussNormalization
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) : Type :=
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI : Algebra (LPSOriginalGaussBase p)
      (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
    ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
  ↥(integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)))
@[instance_reducible, instance 1100]
def lpsOriginalRelativeGaussNormalization_commRing
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    CommRing (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := by
  dsimp only [LPSOriginalRelativeGaussNormalization]
  infer_instance
def lpsOriginalRelativeGaussNormalizationRingEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalRelativeGaussHeckeOrder N hN p ≃+*
      LPSOriginalRelativeGaussNormalization N p hNp h4N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).toAlgebra
  let : Algebra (LPSOriginalGaussBase p)
      (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
    ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
  exact (lpsOriginalRelativeGaussNormalizationEquiv N p hNp h4N hN hpN).toRingEquiv
def lpsOriginalRelativeGaussNormalizationCoefficients
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalGaussAffineOrder N hN p →+*
      LPSOriginalRelativeGaussNormalization N p hNp h4N hN :=
  (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN).toRingHom.comp
    (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p))
def lpsOriginalRelativeGaussNormalizationRoot
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    LPSOriginalRelativeGaussNormalization N p hNp h4N hN :=
  lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN
    (AdjoinRoot.root (lpsOriginalRelativeGaussHeckePolynomial N hN p))
lemma lpsOriginalRelativeGaussNormalizationMaximalMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) :
    q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN) =
      (q.map (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p))).map
        (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN :
          LPSOriginalRelativeGaussHeckeOrder N hN p →+*
            LPSOriginalRelativeGaussNormalization N p hNp h4N hN) :=
  (Ideal.map_map _ _).symm
def lpsOriginalRelativeGaussNormalizationFiberEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)) ≃+*
        (LPSOriginalGaussAffineOrder N hN p ⧸ q) ×
          LPSOriginalRelativeGaussInseparableBranch N hN p q := by
  exact (Ideal.quotientEquiv
    (q.map (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)))
    (q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN))
    (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)
    (lpsOriginalRelativeGaussNormalizationMaximalMap N p hNp h4N hN hpN q)).symm.trans
      (lpsOriginalRelativeGaussHeckeFiberEquiv N hN p hpN q)
@[instance_reducible]
def lpsOriginalRelativeGaussNormalizationCoefficients_algebra
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) : Algebra (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) :=
  (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN).toAlgebra
def lpsOriginalRelativeGaussNormalizationAffineEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    LPSOriginalRelativeGaussHeckeOrder N hN p ≃ₐ[LPSOriginalGaussAffineOrder N hN p]
      LPSOriginalRelativeGaussNormalization N p hNp h4N hN := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  refine { (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN) with commutes' := ?_ }
  intro c
  rfl
abbrev LPSOriginalRelativeGaussNormalizationLinearBranchIdeal
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :=
  (LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q).map (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)
lemma lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_liesOver
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    (LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q).LiesOver q := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussHeckeLinearBranchIdeal_liesOver N hN p hpN q
  exact Ideal.LiesOver.of_eq_map_equiv q (lpsOriginalRelativeGaussNormalizationAffineEquiv N p hNp h4N hN hpN) rfl
abbrev LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :=
  (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).map (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN)
lemma lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_maximal
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q).IsMaximal := by
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_maximal N hN p hpN q
  exact Ideal.IsMaximal.map_bijective _ (lpsOriginalRelativeGaussNormalizationRingEquiv N p hNp h4N hN hpN).bijective inferInstance
lemma lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_liesOver
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    (LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q).LiesOver q := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
  exact Ideal.LiesOver.of_eq_map_equiv q (lpsOriginalRelativeGaussNormalizationAffineEquiv N p hNp h4N hN hpN) rfl
def lpsOriginalRelativeGaussNormalizationLinearBranchResidueEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    letI := lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_liesOver N p hNp h4N hN hpN q
    (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸ LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) ≃ₐ[LPSOriginalGaussAffineOrder N hN p ⧸ q]
      (LPSOriginalGaussAffineOrder N hN p ⧸ q) := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussHeckeLinearBranchIdeal_liesOver N hN p hpN q
  let := lpsOriginalRelativeGaussNormalizationLinearBranchIdeal_liesOver N p hNp h4N hN hpN q
  exact (Ideal.Quotient.algEquivOfEqMap q (lpsOriginalRelativeGaussNormalizationAffineEquiv N p hNp h4N hN hpN)
      (P := LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q) (Q := LPSOriginalRelativeGaussNormalizationLinearBranchIdeal N p hNp h4N hN hpN q) rfl).symm.trans
    (lpsOriginalRelativeGaussHeckeLinearBranchResidueEquiv N hN p hpN q)
def lpsOriginalRelativeGaussNormalizationInseparableBranchResidueEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    letI := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_liesOver N p hNp h4N hN hpN q
    (LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸ LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) ≃ₐ[LPSOriginalGaussAffineOrder N hN p ⧸ q]
      LPSOriginalRelativeGaussInseparableBranch N hN p q := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  let := lpsOriginalRelativeGaussHeckeInseparableBranchIdeal_liesOver N hN p hpN q
  let := lpsOriginalRelativeGaussNormalizationInseparableBranchIdeal_liesOver N p hNp h4N hN hpN q
  exact (Ideal.Quotient.algEquivOfEqMap q (lpsOriginalRelativeGaussNormalizationAffineEquiv N p hNp h4N hN hpN)
      (P := LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) (Q := LPSOriginalRelativeGaussNormalizationInseparableBranchIdeal N p hNp h4N hN hpN q) rfl).symm.trans
    (lpsOriginalRelativeGaussHeckeInseparableBranchResidueEquiv N hN p hpN q)
end
end QEC.Coding.TannerLiftedProduct


