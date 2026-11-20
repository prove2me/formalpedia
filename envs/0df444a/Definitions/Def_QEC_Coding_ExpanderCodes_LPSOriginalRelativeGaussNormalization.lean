-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T10:19:10.339736+00:00
-- url     : https://prove2.me/theorems/5b3f8b84-47f9-49fa-900d-3697dcf74e1f
-- title:
--   LPSOriginal Relative Gauss Normalization
-- statement:
--   Definitions and structural lemmas for LPSOriginal Relative Gauss Normalization, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalization.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeRelativeMinpoly
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussAffineToGenerated_root
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueJN_not_prime_power
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalJN_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeKronecker_afterCoefficientMap
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeRelativeModularPolynomial_irreducible
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
def lpsOriginalRelativeGaussHeckeCoefficientMap
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    Polynomial ℤ →+* LPSOriginalGaussAffineOrder N hN p :=
  Polynomial.eval₂RingHom (Int.castRingHom _)
    (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p))
def lpsOriginalRelativeGaussHeckePolynomial
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    Polynomial (LPSOriginalGaussAffineOrder N hN p) :=
  (lpsOriginalIntegerPolynomial p (Fact.out : p.Prime).pos).map
    (lpsOriginalRelativeGaussHeckeCoefficientMap N hN p)
lemma lpsOriginalRelativeGaussHeckePolynomial_monic
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    (lpsOriginalRelativeGaussHeckePolynomial N hN p).Monic :=
  (lpsOriginalIntegerPolynomial_monic p (Fact.out : p.Prime).pos).map _
lemma lpsOriginalRelativeGaussHeckePolynomial_residue
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (lpsOriginalRelativeGaussHeckePolynomial N hN p).map (Ideal.Quotient.mk q) =
      (Polynomial.X - Polynomial.C ((lpsOriginalGaussMaximalResidueJN N hN p q)^p)) *
      (Polynomial.X^p - Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) := by
  let K := LPSOriginalGaussAffineOrder N hN p ⧸ q
  let c := lpsOriginalGaussMaximalResidueConstantMap N hN p q
  let f : Polynomial (ZMod p) →+* K :=
    Polynomial.eval₂RingHom c (lpsOriginalGaussMaximalResidueJN N hN p q)
  have hc : (Ideal.Quotient.mk q).comp
      (lpsOriginalRelativeGaussHeckeCoefficientMap N hN p) =
      f.comp (Polynomial.mapRingHom (Int.castRingHom (ZMod p))) := by
    apply Polynomial.ringHom_ext
    · intro z
      simp [lpsOriginalRelativeGaussHeckeCoefficientMap,f]
    · simp [lpsOriginalRelativeGaussHeckeCoefficientMap,f,
        lpsOriginalGaussMaximalResidueJN]
  rw [lpsOriginalRelativeGaussHeckePolynomial,Polynomial.map_map,hc,
    lpsOriginalPrimeKronecker_afterCoefficientMap]
  simp [f]
lemma lpsOriginalRelativeGaussHeckeInseparableFactor_irreducible
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    Irreducible ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q))^p -
      Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  exact _root_.X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime)
    (lpsOriginalGaussMaximalResidueJN_not_prime_power N hN p hpN q)
lemma lpsOriginalRelativeGaussHeckePolynomial_residue_squarefree
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Squarefree ((lpsOriginalRelativeGaussHeckePolynomial N hN p).map
      (Ideal.Quotient.mk q)) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  have hi := lpsOriginalRelativeGaussHeckeInseparableFactor_irreducible N hN p hpN q
  have hc : IsCoprime
      ((Polynomial.X : Polynomial (LPSOriginalGaussAffineOrder N hN p ⧸ q)) -
        Polynomial.C ((lpsOriginalGaussMaximalResidueJN N hN p q)^p))
      (Polynomial.X^p - Polynomial.C (lpsOriginalGaussMaximalResidueJN N hN p q)) := by
    apply IsCoprime.symm
    apply hi.coprime_iff_not_dvd.mpr
    intro hdiv
    have hdeg := Polynomial.natDegree_le_of_dvd hdiv
      (Polynomial.X_sub_C_ne_zero ((lpsOriginalGaussMaximalResidueJN N hN p q)^p))
    rw [Polynomial.natDegree_X_pow_sub_C,Polynomial.natDegree_X_sub_C] at hdeg
    exact (Nat.not_le_of_gt (Fact.out : p.Prime).one_lt) hdeg
  rw [lpsOriginalRelativeGaussHeckePolynomial_residue]
  exact squarefree_mul_iff.mpr ⟨hc.isRelPrime,
    (Polynomial.prime_X_sub_C _).irreducible.squarefree,hi.squarefree⟩
lemma lpsOriginalRelativeGaussHeckePolynomial_residue_quotient_reduced
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    IsReduced (AdjoinRoot ((lpsOriginalRelativeGaussHeckePolynomial N hN p).map
      (Ideal.Quotient.mk q))) := by
  let : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  exact isRadical_iff_span_singleton.mp
    (lpsOriginalRelativeGaussHeckePolynomial_residue_squarefree N hN p hpN q).isRadical
lemma lpsOriginalMonicAdjoinRootMap_injective
    {R K : Type*} [CommRing R] [CommRing K] (f : R →+* K)
    (hf : Function.Injective f) (P : Polynomial R) (hP : P.Monic) :
    Function.Injective (AdjoinRoot.map f P (P.map f) dvd_rfl) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using AdjoinRoot.induction_on with
  | ih Q =>
    rw [AdjoinRoot.map,AdjoinRoot.lift_mk] at hx
    have he : AdjoinRoot.mk (P.map f) (Q.map f) = 0 := by
      rw [← AdjoinRoot.aeval_eq,Polynomial.aeval_def,Polynomial.eval₂_map]
      exact hx
    apply AdjoinRoot.mk_eq_zero.mpr
    rw [← Polynomial.map_dvd_map f hf hP]
    exact AdjoinRoot.mk_eq_zero.mp he
lemma lpsOriginalRelativeGaussHeckeCoefficientMap_generated
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGaussAffineToGenerated N hN p).comp
      (lpsOriginalRelativeGaussHeckeCoefficientMap N hN p) =
      lpsOriginalPrimeRelativeCoefficientMap N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply Polynomial.ringHom_ext
  · intro z
    simp [lpsOriginalRelativeGaussHeckeCoefficientMap,
      lpsOriginalPrimeRelativeCoefficientMap]
  · simp only [RingHom.comp_apply,lpsOriginalRelativeGaussHeckeCoefficientMap,
      lpsOriginalPrimeRelativeCoefficientMap,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
    apply Subtype.ext
    rw [lpsOriginalGaussAffineToGenerated_root,lpsOriginalIntegerNormalJN_coe]
lemma lpsOriginalRelativeGaussHeckePolynomial_fraction
    (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalRelativeGaussHeckePolynomial N hN p).map
      (lpsOriginalGaussAffineToGenerated N hN p) =
      lpsOriginalPrimeRelativeModularPolynomial N p hN (Fact.out : p.Prime).pos := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalRelativeGaussHeckePolynomial,Polynomial.map_map,
    lpsOriginalRelativeGaussHeckeCoefficientMap_generated]
  rfl
abbrev LPSOriginalRelativeGaussHeckeOrder
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :=
  AdjoinRoot (lpsOriginalRelativeGaussHeckePolynomial N hN p)
lemma lpsOriginalRelativeGaussHeckeOrder_domain
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    IsDomain (LPSOriginalRelativeGaussHeckeOrder N hN p) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let R := LPSOriginalGaussAffineOrder N hN p
  let K := lpsOriginalGeneratedFunctionFieldQ N hN
  let := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  let := lpsOriginalGaussAffineOrder_domain N hN p
  let := lpsOriginalGaussAffineGenerated_isFractionRing N hN p
  let P := lpsOriginalRelativeGaussHeckePolynomial N hN p
  have hi : Irreducible (P.map (lpsOriginalGaussAffineToGenerated N hN p)) := by
    rw [lpsOriginalRelativeGaussHeckePolynomial_fraction]
    exact lpsOriginalPrimeRelativeModularPolynomial_irreducible N p hNp h4N hN
  let : IsDomain (AdjoinRoot (P.map (lpsOriginalGaussAffineToGenerated N hN p))) :=
    AdjoinRoot.isDomain_of_prime hi.prime
  exact (lpsOriginalMonicAdjoinRootMap_injective
    (lpsOriginalGaussAffineToGenerated N hN p) (IsFractionRing.injective R K) P
    (lpsOriginalRelativeGaussHeckePolynomial_monic N hN p)).isDomain _
lemma lpsOriginalRelativeGaussHeckeOrder_maximalFiber_reduced
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    IsReduced (LPSOriginalRelativeGaussHeckeOrder N hN p ⧸
      q.map (algebraMap (LPSOriginalGaussAffineOrder N hN p)
        (LPSOriginalRelativeGaussHeckeOrder N hN p))) := by
  let e : (LPSOriginalRelativeGaussHeckeOrder N hN p ⧸
      q.map (algebraMap (LPSOriginalGaussAffineOrder N hN p)
        (LPSOriginalRelativeGaussHeckeOrder N hN p))) ≃+*
      AdjoinRoot ((lpsOriginalRelativeGaussHeckePolynomial N hN p).map
        (Ideal.Quotient.mk q)) :=
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot q
      (lpsOriginalRelativeGaussHeckePolynomial N hN p)
  let : IsReduced (AdjoinRoot ((lpsOriginalRelativeGaussHeckePolynomial N hN p).map
      (Ideal.Quotient.mk q))) :=
    lpsOriginalRelativeGaussHeckePolynomial_residue_quotient_reduced N hN p hpN q
  exact isReduced_of_injective e e.injective
lemma lpsOriginalRelativeGaussHeckeOrder_dedekind
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    IsDedekindDomain (LPSOriginalRelativeGaussHeckeOrder N hN p) := by
  let R := LPSOriginalGaussAffineOrder N hN p
  let B := LPSOriginalRelativeGaussHeckeOrder N hN p
  let := lpsOriginalGaussAffineOrder_dedekind N hN p hpN
  let := lpsOriginalRelativeGaussHeckeOrder_domain N p hNp h4N hN
  let : Module.Finite R B := (lpsOriginalRelativeGaussHeckePolynomial_monic N hN p).finite_adjoinRoot
  apply QEC.Coding.AlgebraicGeometry.finite_dedekind_domain_of_reduced_maximal_fibres R B
  intro q hq
  exact lpsOriginalRelativeGaussHeckeOrder_maximalFiber_reduced N hN p hpN q
lemma lpsOriginalRelativeGaussHeckeOrder_integrallyClosed
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    IsIntegrallyClosed (LPSOriginalRelativeGaussHeckeOrder N hN p) := by
  let := lpsOriginalRelativeGaussHeckeOrder_dedekind N p hNp h4N hN hpN
  infer_instance
lemma lpsOriginalFieldLocalization_isFractionRing
    (R K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (M : Submonoid R) [IsLocalization M K]
    (hi : Function.Injective (algebraMap R K)) : IsFractionRing R K := by
  apply IsLocalization.of_le (M := M) (nonZeroDivisors R)
  · intro x hx
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro he
    have hu : IsUnit (algebraMap R K x) := IsLocalization.map_units K (⟨x,hx⟩ : M)
    rw [he,map_zero] at hu
    exact not_isUnit_zero hu
  · intro x hx
    apply isUnit_iff_ne_zero.mpr
    exact (map_ne_zero_iff _ hi).mpr (mem_nonZeroDivisors_iff_ne_zero.mp hx)
lemma lpsOriginalMonicAdjoinRoot_fractionRing
    (R K : Type*) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (P : Polynomial R) (hP : P.Monic)
    (hi : Irreducible (P.map (algebraMap R K))) :
    letI : Algebra (AdjoinRoot P) (AdjoinRoot (P.map (algebraMap R K))) :=
      (AdjoinRoot.map (algebraMap R K) P (P.map (algebraMap R K)) dvd_rfl).toAlgebra
    IsFractionRing (AdjoinRoot P) (AdjoinRoot (P.map (algebraMap R K))) := by
  let A := AdjoinRoot (P.map (algebraMap R K))
  let B := AdjoinRoot P
  let : Fact (Irreducible (P.map (algebraMap R K))) := ⟨hi⟩
  let : Field A := inferInstance
  let : Algebra B A :=
    (AdjoinRoot.map (algebraMap R K) P (P.map (algebraMap R K)) dvd_rfl).toAlgebra
  have hinj : Function.Injective (algebraMap B A) :=
    lpsOriginalMonicAdjoinRootMap_injective (algebraMap R K)
      (IsFractionRing.injective R K) P hP
  let : IsDomain B := hinj.isDomain (algebraMap B A)
  let : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) A :=
    QEC.Coding.AlgebraicGeometry.adjoinRoot_baseChange_isLocalization R K
      (nonZeroDivisors R) P
  exact lpsOriginalFieldLocalization_isFractionRing B A
    (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) hinj
def lpsOriginalRelativeGaussHeckeFieldEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    AdjoinRoot ((lpsOriginalRelativeGaussHeckePolynomial N hN p).map
      (lpsOriginalGaussAffineToGenerated N hN p)) ≃+*
        lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let K := lpsOriginalGeneratedFunctionFieldQ N hN
  exact (AdjoinRoot.mapRingEquiv (RingEquiv.refl K) _ _
    (Associated.of_eq (by simpa using
      (lpsOriginalRelativeGaussHeckePolynomial_fraction N p hN)))).trans
    (lpsOriginalPrimeRelativeAdjoinRootEquiv N p hNp h4N hN)
def lpsOriginalRelativeGaussHeckeToGenerated
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    LPSOriginalRelativeGaussHeckeOrder N hN p →+*
      lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (lpsOriginalRelativeGaussHeckeFieldEquiv N p hNp h4N hN).toRingHom.comp
    (AdjoinRoot.map (lpsOriginalGaussAffineToGenerated N hN p)
      (lpsOriginalRelativeGaussHeckePolynomial N hN p)
      ((lpsOriginalRelativeGaussHeckePolynomial N hN p).map
        (lpsOriginalGaussAffineToGenerated N hN p)) dvd_rfl)
lemma lpsOriginalRelativeGaussHeckeGenerated_isFractionRing
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).toAlgebra
    IsFractionRing (LPSOriginalRelativeGaussHeckeOrder N hN p)
      (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let R := LPSOriginalGaussAffineOrder N hN p
  let K := lpsOriginalGeneratedFunctionFieldQ N hN
  let P := lpsOriginalRelativeGaussHeckePolynomial N hN p
  let B := AdjoinRoot P
  let A := AdjoinRoot (P.map (lpsOriginalGaussAffineToGenerated N hN p))
  let := (lpsOriginalGaussAffineToGenerated N hN p).toAlgebra
  let := lpsOriginalGaussAffineOrder_domain N hN p
  let := lpsOriginalGaussAffineGenerated_isFractionRing N hN p
  let : Algebra B A :=
    (AdjoinRoot.map (lpsOriginalGaussAffineToGenerated N hN p) P
      (P.map (lpsOriginalGaussAffineToGenerated N hN p)) dvd_rfl).toAlgebra
  have hi : Irreducible (P.map (lpsOriginalGaussAffineToGenerated N hN p)) := by
    rw [lpsOriginalRelativeGaussHeckePolynomial_fraction]
    exact lpsOriginalPrimeRelativeModularPolynomial_irreducible N p hNp h4N hN
  let : IsFractionRing B A := lpsOriginalMonicAdjoinRoot_fractionRing R K P
    (lpsOriginalRelativeGaussHeckePolynomial_monic N hN p) hi
  exact (IsLocalization.isLocalization_iff_of_ringEquiv (nonZeroDivisors B)
    (lpsOriginalRelativeGaussHeckeFieldEquiv N p hNp h4N hN)).mp inferInstance
lemma lpsOriginalRelativeGaussHeckeOrder_isIntegralClosure
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
      ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
    IsIntegralClosure (LPSOriginalRelativeGaussHeckeOrder N hN p)
      (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let A := LPSOriginalGaussBase p
  let R := LPSOriginalGaussAffineOrder N hN p
  let B := LPSOriginalRelativeGaussHeckeOrder N hN p
  let L := lpsOriginalGeneratedFunctionFieldQ (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  let := (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).toAlgebra
  let : Algebra A L := ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
    (algebraMap A B)).toAlgebra
  let := lpsOriginalRelativeGaussHeckeOrder_domain N p hNp h4N hN
  let := lpsOriginalRelativeGaussHeckeGenerated_isFractionRing N p hNp h4N hN
  let := lpsOriginalRelativeGaussHeckeOrder_integrallyClosed N p hNp h4N hN hpN
  let : Module.Finite A R := ((lpsOriginalIntegerPolynomial_monic N hN).map _).finite_adjoinRoot
  let : Module.Finite R B := (lpsOriginalRelativeGaussHeckePolynomial_monic N hN p).finite_adjoinRoot
  let : Module.Finite A B := Module.Finite.trans R B
  let : IsScalarTower A B L := .of_algebraMap_eq' rfl
  infer_instance
def lpsOriginalRelativeGaussNormalizationEquiv
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p)
        (lpsOriginalGeneratedFunctionFieldQ (N*p)
          (Nat.mul_pos hN (Fact.out : p.Prime).pos)) :=
      ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalRelativeGaussHeckeOrder N hN p))).toAlgebra
    LPSOriginalRelativeGaussHeckeOrder N hN p ≃ₐ[LPSOriginalGaussBase p]
      integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ (N*p)
        (Nat.mul_pos hN (Fact.out : p.Prime).pos)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let A := LPSOriginalGaussBase p
  let B := LPSOriginalRelativeGaussHeckeOrder N hN p
  let L := lpsOriginalGeneratedFunctionFieldQ (N*p)
    (Nat.mul_pos hN (Fact.out : p.Prime).pos)
  let := (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).toAlgebra
  let : Algebra A L := ((lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN).comp
    (algebraMap A B)).toAlgebra
  let : IsScalarTower A B L := .of_algebraMap_eq' rfl
  let := lpsOriginalRelativeGaussHeckeOrder_isIntegralClosure N p hNp h4N hN hpN
  exact IsIntegralClosure.equiv A B L (integralClosure A L)
end
end QEC.Coding.TannerLiftedProduct


