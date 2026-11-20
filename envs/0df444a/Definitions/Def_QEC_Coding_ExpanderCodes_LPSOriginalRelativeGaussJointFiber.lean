-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T11:50:13.944744+00:00
-- url     : https://prove2.me/theorems/e2207702-5f8a-46e6-b68b-eb7209441f86
-- title:
--   LPSOriginal Relative Gauss Joint Fiber
-- statement:
--   Definitions and structural lemmas for LPSOriginal Relative Gauss Joint Fiber, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidue_charP
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective

set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
def lpsOriginalPrimeFieldAlgHomOfRingHom
    (p : ℕ) {R S : Type*} [CommRing R] [CommRing S]
    [Algebra (ZMod p) R] [Algebra (ZMod p) S] (f : R →+* S) : R →ₐ[ZMod p] S :=
  { f with
    commutes' := by
      intro r
      exact RingHom.congr_fun
        (Subsingleton.elim (f.comp (algebraMap (ZMod p) R)) (algebraMap (ZMod p) S)) r }
def lpsOriginalRelativeGaussNormalizationFiberJointTensorMap
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
    let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
      q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
    letI : Field K := Ideal.Quotient.field q
    letI : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
    letI : CharP F p := charP_of_injective_ringHom
      (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    letI : Module (ZMod p) K := Algebra.toModule
    letI : Module (ZMod p) F := Algebra.toModule
    (K ⊗[ZMod p] K) →ₐ[ZMod p] F := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let F := LPSOriginalRelativeGaussNormalization N p hNp h4N hN ⧸
    q.map (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN)
  let : Field K := Ideal.Quotient.field q
  let : CharP K p := lpsOriginalGaussMaximalResidue_charP N hN p q
  let : CharP F p := charP_of_injective_ringHom
    (lpsOriginalRelativeGaussNormalizationFirstFiberMap_injective N p hNp h4N hN hpN q) p
  let : Algebra (ZMod p) K := ZMod.algebra K p
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Module (ZMod p) K := Algebra.toModule
  let : Module (ZMod p) F := Algebra.toModule
  exact Algebra.TensorProduct.lift (R := ZMod p) (S := ZMod p) (A := K) (B := K) (C := F)
    (lpsOriginalPrimeFieldAlgHomOfRingHom p (R := K) (S := F)
      (lpsOriginalRelativeGaussNormalizationFirstFiberMap N p hNp h4N hN hpN q))
    (lpsOriginalPrimeFieldAlgHomOfRingHom p (R := K) (S := F)
      (lpsOriginalRelativeGaussNormalizationSecondFiberMap N p hNp h4N hN hpN q))
    (fun _ _ => Commute.all _ _)
def lpsOriginalFrobeniusFirstTensorGraphMap
    (p : ℕ) (K : Type*) [Field K] [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] : (K ⊗[ZMod p] K) →ₐ[ZMod p] K :=
  Algebra.TensorProduct.lift (AlgHom.id (ZMod p) K)
    (lpsOriginalPrimeFieldAlgHomOfRingHom p (frobenius K p)) (fun _ _ => Commute.all _ _)
def lpsOriginalFrobeniusSecondTensorGraphMap
    (p : ℕ) (K : Type*) [Field K] [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] : (K ⊗[ZMod p] K) →ₐ[ZMod p] K :=
  Algebra.TensorProduct.lift
    (lpsOriginalPrimeFieldAlgHomOfRingHom p (frobenius K p))
    (AlgHom.id (ZMod p) K) (fun _ _ => Commute.all _ _)
end
end QEC.Coding.TannerLiftedProduct


