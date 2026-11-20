-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointInteger
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointInteger
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T11:52:07.258264+00:00
-- url     : https://prove2.me/theorems/987460db-82f9-49c7-b544-8c56535e35c8
-- title:
--   LPSOriginal Relative Gauss Joint Integer
-- statement:
--   Definitions and structural lemmas for LPSOriginal Relative Gauss Joint Integer, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointInteger.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_degree

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
def lpsOriginalRelativeGaussNormalizationJointIntegerTensorMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
    letI : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
    letI : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
    letI : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
    (LPSOriginalGaussAffineOrder N hN p ⊗[ℤ] LPSOriginalGaussAffineOrder N hN p) →ₐ[ℤ] LPSOriginalRelativeGaussNormalization N p hNp h4N hN := by
  let : Algebra ℤ (LPSOriginalGaussAffineOrder N hN p) := Ring.toIntAlgebra _
  let : Algebra ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Ring.toIntAlgebra _
  let : Module ℤ (LPSOriginalGaussAffineOrder N hN p) := Algebra.toModule
  let : Module ℤ (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := Algebra.toModule
  exact Algebra.TensorProduct.lift
    (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN).toIntAlgHom
    (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN).toIntAlgHom
    (fun _ _ => Commute.all _ _)
lemma lpsOriginalRelativeGaussHeckePolynomial_natDegree
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    (lpsOriginalRelativeGaussHeckePolynomial N hN p).natDegree = p + 1 := by
  let := lpsOriginalGaussAffineOrder_domain N hN p
  rw [lpsOriginalRelativeGaussHeckePolynomial,
    (lpsOriginalIntegerPolynomial_monic p (Fact.out : p.Prime).pos).natDegree_map,
    lpsOriginalPrimeIntegerPolynomial_degree]
def lpsOriginalRelativeGaussNormalizationFirstBasis
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
    Module.Basis (Fin (p+1)) (LPSOriginalGaussAffineOrder N hN p) (LPSOriginalRelativeGaussNormalization N p hNp h4N hN) := by
  let := lpsOriginalRelativeGaussNormalizationCoefficients_algebra N p hNp h4N hN hpN
  exact ((AdjoinRoot.powerBasis' (lpsOriginalRelativeGaussHeckePolynomial_monic N hN p)).basis.map
    (lpsOriginalRelativeGaussNormalizationAffineEquiv N p hNp h4N hN hpN).toLinearEquiv).reindex
    (finCongr (lpsOriginalRelativeGaussHeckePolynomial_natDegree N hN p))
end
end QEC.Coding.TannerLiftedProduct


