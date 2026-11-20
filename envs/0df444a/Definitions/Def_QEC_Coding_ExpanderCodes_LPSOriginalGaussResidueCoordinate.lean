-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T09:20:21.521594+00:00
-- url     : https://prove2.me/theorems/92937506-17d3-48bd-8ce5-71281759e406
-- title:
--   LPSOriginal Gauss Residue Coordinate
-- statement:
--   Definitions and structural lemmas for LPSOriginal Gauss Residue Coordinate, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDualMonicRelation_transcendental
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerPolynomial_gaussDualRoot
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
def lpsOriginalAdjoinRootMaximalResidueBaseMap
    (R : Type*) [CommRing R] [IsLocalRing R]
    (P : Polynomial R) (hP : P.Monic)
    (q : Ideal (AdjoinRoot P)) [q.IsMaximal] :
    IsLocalRing.ResidueField R →+* (AdjoinRoot P ⧸ q) := by
  let : Module.Finite R (AdjoinRoot P) := hP.finite_adjoinRoot
  have hcontract : q.comap (algebraMap R (AdjoinRoot P)) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) q)
  let i := (Ideal.Quotient.mk q).comp (algebraMap R (AdjoinRoot P))
  exact Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) i (by
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change a ∈ q.comap (algebraMap R (AdjoinRoot P))
    rwa [hcontract])
lemma lpsOriginalAdjoinRootMaximalResidueBaseMap_diagram
    (R : Type*) [CommRing R] [IsLocalRing R]
    (P : Polynomial R) (hP : P.Monic)
    (q : Ideal (AdjoinRoot P)) [q.IsMaximal] :
    (lpsOriginalAdjoinRootMaximalResidueBaseMap R P hP q).comp
      (IsLocalRing.residue R) =
      (Ideal.Quotient.mk q).comp (algebraMap R (AdjoinRoot P)) := by
  apply RingHom.ext
  intro a
  rfl
def lpsOriginalGaussMaximalResidueFractionMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    FractionRing (Polynomial (ZMod p)) →+* (LPSOriginalGaussAffineOrder N hN p ⧸ q) :=
  (lpsOriginalAdjoinRootMaximalResidueBaseMap (LPSOriginalGaussBase p)
    (lpsOriginalGaussPolynomial N hN p)
    ((lpsOriginalIntegerPolynomial_monic N hN).map _) q).comp
    (lpsOriginalGaussResidueEquiv p).symm.toRingHom
lemma lpsOriginalGaussMaximalResidueFractionMap_injective
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Injective (lpsOriginalGaussMaximalResidueFractionMap N hN p q) :=
  (lpsOriginalGaussMaximalResidueFractionMap N hN p q).injective
def lpsOriginalGaussMaximalResidueJ
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) :
    LPSOriginalGaussAffineOrder N hN p ⧸ q :=
  Ideal.Quotient.mk q
    (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X))
def lpsOriginalGaussMaximalResidueJN
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) :
    LPSOriginalGaussAffineOrder N hN p ⧸ q :=
  Ideal.Quotient.mk q (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))
lemma lpsOriginalIntegerPolynomial_gaussMaximalResidueDualRoot
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalGaussMaximalResidueJN N hN p q))
      (lpsOriginalGaussMaximalResidueJ N hN p q) = 0 := by
  let f := Ideal.Quotient.mk q
  have h := congrArg f (lpsOriginalIntegerPolynomial_gaussDualRoot N hN p hpN)
  have hc : f.comp (Polynomial.eval₂RingHom (Int.castRingHom _)
        (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))) =
      Polynomial.eval₂RingHom (Int.castRingHom _)
        (lpsOriginalGaussMaximalResidueJN N hN p q) := by
    apply Polynomial.ringHom_ext
    · intro z
      simp
    · simp [lpsOriginalGaussMaximalResidueJN,f]
  rw [Polynomial.hom_eval₂,map_zero,hc] at h
  exact h
lemma lpsOriginalGaussMaximalResidueFractionMap_base
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (P : Polynomial ℤ) :
    lpsOriginalGaussMaximalResidueFractionMap N hN p q
      (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))
        (lpsOriginalGaussCoefficientReduction p P)) =
      Ideal.Quotient.mk q
        (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
          (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) P)) := by
  rw [← lpsOriginalGaussResidueEquiv_base p P]
  simp only [lpsOriginalGaussMaximalResidueFractionMap,RingHom.comp_apply]
  erw [(lpsOriginalGaussResidueEquiv p).symm_apply_apply]
  rw [IsScalarTower.algebraMap_apply (Polynomial ℤ) (LPSOriginalGaussBase p)
    (IsLocalRing.ResidueField (LPSOriginalGaussBase p))]
  change (lpsOriginalAdjoinRootMaximalResidueBaseMap (LPSOriginalGaussBase p)
    (lpsOriginalGaussPolynomial N hN p)
    ((lpsOriginalIntegerPolynomial_monic N hN).map _) q).comp
    (IsLocalRing.residue (LPSOriginalGaussBase p))
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) P) = _
  erw [lpsOriginalAdjoinRootMaximalResidueBaseMap_diagram]
  rfl
def lpsOriginalGaussMaximalResidueConstantMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    ZMod p →+* (LPSOriginalGaussAffineOrder N hN p ⧸ q) :=
  (lpsOriginalGaussMaximalResidueFractionMap N hN p q).comp
    (algebraMap (ZMod p) (FractionRing (Polynomial (ZMod p))))
lemma lpsOriginalGaussMaximalResidueFractionMap_polynomial
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalGaussMaximalResidueFractionMap N hN p q).comp
      (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p)))) =
      Polynomial.eval₂RingHom (lpsOriginalGaussMaximalResidueConstantMap N hN p q)
        (lpsOriginalGaussMaximalResidueJ N hN p q) := by
  apply Polynomial.ringHom_ext
  · intro z
    simp only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
      lpsOriginalGaussMaximalResidueConstantMap]
    rw [IsScalarTower.algebraMap_apply (ZMod p) (Polynomial (ZMod p))
      (FractionRing (Polynomial (ZMod p)))]
    rfl
  · simp only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
    simpa only [lpsOriginalGaussCoefficientReduction,Polynomial.coe_mapRingHom,
      Polynomial.map_X,lpsOriginalGaussMaximalResidueJ] using
      lpsOriginalGaussMaximalResidueFractionMap_base N hN p q Polynomial.X
lemma lpsOriginalGaussMaximalResidueJ_transcendental
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := (lpsOriginalGaussMaximalResidueConstantMap N hN p q).toAlgebra
    Transcendental (ZMod p) (lpsOriginalGaussMaximalResidueJ N hN p q) := by
  let := (lpsOriginalGaussMaximalResidueConstantMap N hN p q).toAlgebra
  apply transcendental_iff_injective.mpr
  change Function.Injective (Polynomial.eval₂RingHom
    (lpsOriginalGaussMaximalResidueConstantMap N hN p q)
    (lpsOriginalGaussMaximalResidueJ N hN p q))
  rw [← lpsOriginalGaussMaximalResidueFractionMap_polynomial]
  exact (lpsOriginalGaussMaximalResidueFractionMap_injective N hN p q).comp
    (IsFractionRing.injective (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))))
lemma lpsOriginalGaussMaximalResidueJN_transcendental
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI := (lpsOriginalGaussMaximalResidueConstantMap N hN p q).toAlgebra
    Transcendental (ZMod p) (lpsOriginalGaussMaximalResidueJN N hN p q) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let : Field K := Ideal.Quotient.field q
  let := (lpsOriginalGaussMaximalResidueConstantMap N hN p q).toAlgebra
  let P := (lpsOriginalIntegerPolynomial N hN).map
    (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))
  have hc : (Polynomial.eval₂RingHom (algebraMap (ZMod p) K)
      (lpsOriginalGaussMaximalResidueJN N hN p q)).comp
      (Polynomial.mapRingHom (Int.castRingHom (ZMod p))) =
      Polynomial.eval₂RingHom (Int.castRingHom K)
        (lpsOriginalGaussMaximalResidueJN N hN p q) := by
    apply Polynomial.ringHom_ext
    · intro z
      simp
    · simp
  have hr : P.eval₂ (Polynomial.eval₂RingHom (algebraMap (ZMod p) K)
      (lpsOriginalGaussMaximalResidueJN N hN p q))
      (lpsOriginalGaussMaximalResidueJ N hN p q) = 0 := by
    dsimp only [P]
    rw [Polynomial.eval₂_map,hc]
    exact lpsOriginalIntegerPolynomial_gaussMaximalResidueDualRoot N hN p hpN q
  exact lpsOriginalDualMonicRelation_transcendental (ZMod p) K P
    ((lpsOriginalIntegerPolynomial_monic N hN).map _)
    (lpsOriginalGaussMaximalResidueJ N hN p q)
    (lpsOriginalGaussMaximalResidueJN N hN p q) hr
    (lpsOriginalGaussMaximalResidueJ_transcendental N hN p q)
def lpsOriginalGaussMaximalResidueJN_FractionMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    FractionRing (Polynomial (ZMod p)) →+* (LPSOriginalGaussAffineOrder N hN p ⧸ q) := by
  letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  letI := (lpsOriginalGaussMaximalResidueConstantMap N hN p q).toAlgebra
  have hi : Function.Injective (Polynomial.eval₂RingHom
      (lpsOriginalGaussMaximalResidueConstantMap N hN p q)
      (lpsOriginalGaussMaximalResidueJN N hN p q)) :=
    transcendental_iff_injective.mp
      (lpsOriginalGaussMaximalResidueJN_transcendental N hN p hpN q)
  exact IsFractionRing.lift hi
end
end QEC.Coding.TannerLiftedProduct


