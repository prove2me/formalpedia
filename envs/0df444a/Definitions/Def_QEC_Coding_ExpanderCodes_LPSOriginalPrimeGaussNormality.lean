-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T04:45:38.302189+00:00
-- url     : https://prove2.me/theorems/6adb4d4f-4625-4b17-a084-5bfeab929e49
-- title:
--   LPSOriginal Prime Gauss Normality
-- statement:
--   Definitions and structural lemmas for LPSOriginal Prime Gauss Normality, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeGaussNormality.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeIntegerPolynomial_Kronecker
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
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
lemma ratFunc_intDegree_pow_of_ne_zero
    (K : Type*) [Field K] (u : RatFunc K) (hu : u ≠ 0) (n : ℕ) :
    RatFunc.intDegree (u^n) = (n : ℤ) * RatFunc.intDegree u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,RatFunc.intDegree_mul (pow_ne_zero n hu) hu,ih]
    push_cast
    ring
lemma ratFunc_coordinate_not_prime_power
    (K : Type*) [Field K] (p : ℕ) (hp : p.Prime) (u : RatFunc K) :
    u^p ≠ RatFunc.X := by
  intro heq
  have hX : (RatFunc.X : RatFunc K) ≠ 0 := by
    intro h
    have hd := congrArg RatFunc.intDegree h
    simp at hd
  have hu : u ≠ 0 := by
    intro h
    apply hX
    rw [← heq,h,zero_pow hp.ne_zero]
  have hd := congrArg RatFunc.intDegree heq
  rw [ratFunc_intDegree_pow_of_ne_zero K u hu p,RatFunc.intDegree_X] at hd
  have hdiv : (p : ℤ) ∣ (1 : ℤ) := ⟨RatFunc.intDegree u,hd.symm⟩
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp hdiv)
lemma ratFunc_prime_coordinate_polynomial_irreducible
    (K : Type*) [Field K] (p : ℕ) (hp : p.Prime) :
    Irreducible ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X) :=
  _root_.X_pow_sub_C_irreducible_of_prime hp
    (ratFunc_coordinate_not_prime_power K p hp)
lemma ratFunc_kronecker_factors_coprime
    (K : Type*) [Field K] (p : ℕ) (hp : p.Prime) :
    IsCoprime ((Polynomial.X : Polynomial (RatFunc K)) -
      Polynomial.C ((RatFunc.X : RatFunc K)^p))
      ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X) := by
  apply IsCoprime.symm
  apply (ratFunc_prime_coordinate_polynomial_irreducible K p hp).coprime_iff_not_dvd.mpr
  intro hdiv
  have hdeg := Polynomial.natDegree_le_of_dvd hdiv
    (Polynomial.X_sub_C_ne_zero ((RatFunc.X : RatFunc K)^p))
  rw [Polynomial.natDegree_X_pow_sub_C,Polynomial.natDegree_X_sub_C] at hdeg
  exact (Nat.not_le_of_gt hp.one_lt) hdeg
lemma ratFunc_kronecker_product_squarefree
    (K : Type*) [Field K] (p : ℕ) (hp : p.Prime) :
    Squarefree (((Polynomial.X : Polynomial (RatFunc K)) -
      Polynomial.C ((RatFunc.X : RatFunc K)^p)) *
      ((Polynomial.X : Polynomial (RatFunc K))^p - Polynomial.C RatFunc.X)) := by
  apply squarefree_mul_iff.mpr
  exact ⟨(ratFunc_kronecker_factors_coprime K p hp).isRelPrime,
    (Polynomial.prime_X_sub_C ((RatFunc.X : RatFunc K)^p)).irreducible.squarefree,
    (ratFunc_prime_coordinate_polynomial_irreducible K p hp).squarefree⟩
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
lemma lpsOriginalPrimeModularPolynomialModFraction_ratFunc
    (p : ℕ) [Fact p.Prime] :
    (lpsOriginalModularPolynomialModFraction p (Fact.out : p.Prime).pos p).map
      ((RatFunc.toFractionRingRingEquiv (K := ZMod p)).symm.toRingHom) =
      ((Polynomial.X : Polynomial (RatFunc (ZMod p))) -
        Polynomial.C ((RatFunc.X : RatFunc (ZMod p))^p)) *
      ((Polynomial.X : Polynomial (RatFunc (ZMod p)))^p - Polynomial.C RatFunc.X) := by
  have hx : (RatFunc.toFractionRingRingEquiv (K := ZMod p)).symm.toRingHom
      (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) Polynomial.X) =
      (RatFunc.X : RatFunc (ZMod p)) := by
    change RatFunc.ofFractionRing
      (algebraMap (Polynomial (ZMod p)) (FractionRing (Polynomial (ZMod p))) Polynomial.X) = _
    rw [RatFunc.ofFractionRing_algebraMap,RatFunc.algebraMap_X]
  rw [lpsOriginalModularPolynomialModFraction,← Polynomial.map_map,
    lpsOriginalPrimeIntegerPolynomial_Kronecker]
  simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,
    Polynomial.map_pow,map_pow,hx]
lemma lpsOriginalPrimeModularPolynomialModFraction_squarefree
    (p : ℕ) [Fact p.Prime] :
    Squarefree (lpsOriginalModularPolynomialModFraction p (Fact.out : p.Prime).pos p) := by
  let e : Polynomial (FractionRing (Polynomial (ZMod p))) ≃+*
      Polynomial (RatFunc (ZMod p)) := Polynomial.mapEquiv (RatFunc.toFractionRingRingEquiv (K := ZMod p)).symm
  have hs : Squarefree (e
      (lpsOriginalModularPolynomialModFraction p (Fact.out : p.Prime).pos p)) := by
    change Squarefree ((lpsOriginalModularPolynomialModFraction p (Fact.out : p.Prime).pos p).map
      (RatFunc.toFractionRingRingEquiv (K := ZMod p)).symm.toRingHom)
    rw [lpsOriginalPrimeModularPolynomialModFraction_ratFunc]
    exact QEC.Coding.AlgebraicGeometry.ratFunc_kronecker_product_squarefree (ZMod p) p Fact.out
  intro x hx
  apply (MulEquiv.isUnit_map e).mp
  apply hs (e x)
  simpa only [map_mul] using map_dvd e hx
lemma lpsOriginalPrimeGaussPolynomial_residue_squarefree
    (p : ℕ) [Fact p.Prime] :
    Squarefree ((lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p).map
      (IsLocalRing.residue (LPSOriginalGaussBase p))) := by
  let e := Polynomial.mapEquiv (lpsOriginalGaussResidueEquiv p)
  have hs : Squarefree (e ((lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p).map
      (IsLocalRing.residue (LPSOriginalGaussBase p)))) := by
    change Squarefree (((lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p).map
      (IsLocalRing.residue (LPSOriginalGaussBase p))).map (lpsOriginalGaussResidueEquiv p).toRingHom)
    rw [lpsOriginalGaussPolynomial_residueDiagram]
    exact lpsOriginalPrimeModularPolynomialModFraction_squarefree p
  intro x hx
  apply (MulEquiv.isUnit_map e).mp
  apply hs (e x)
  simpa only [map_mul] using map_dvd e hx
lemma lpsOriginalPrimeGaussResidueAdjoinRoot_reduced
    (p : ℕ) [Fact p.Prime] :
    IsReduced (AdjoinRoot ((lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p).map
      (IsLocalRing.residue (LPSOriginalGaussBase p)))) := by
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  exact isRadical_iff_span_singleton.mp
    (lpsOriginalPrimeGaussPolynomial_residue_squarefree p).isRadical
lemma lpsOriginalPrimeGaussAffineOrder_specialFiber_reduced
    (p : ℕ) [Fact p.Prime] :
    IsReduced (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p ⧸
      (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p)
          (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))) := by
  let := lpsOriginalPrimeGaussResidueAdjoinRoot_reduced p
  let e : (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p ⧸
      (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p)).map
        (algebraMap (LPSOriginalGaussBase p)
          (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))) ≃+*
      AdjoinRoot ((lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p).map
        (IsLocalRing.residue (LPSOriginalGaussBase p))) :=
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot
      (IsLocalRing.maximalIdeal (LPSOriginalGaussBase p))
      (lpsOriginalGaussPolynomial p (Fact.out : p.Prime).pos p)
  exact isReduced_of_injective e e.injective
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.AlgebraicGeometry
noncomputable section
lemma finite_dedekind_domain_of_reduced_maximal_fibres
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsDedekindDomain A] [IsDomain B]
    (hf : ∀ (p : Ideal A) [p.IsMaximal], IsReduced (B ⧸ p.map (algebraMap A B))) :
    IsDedekindDomain B := by
  let : IsDedekindDomainDvr B :=
    { __ := IsNoetherianRing.of_finite A B
      is_dvr_at_nonzero_prime := by
        intro q hq hqp
        let q' := IsLocalRing.maximalIdeal (Localization.AtPrime q)
        suffices q'.IsPrincipal from
          ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q)
            (IsLocalization.AtPrime.not_isField B hq (Localization.AtPrime q))).out 4 0).mp this
        let p := q.under A
        let := Localization.AtPrime.algebraOfLiesOver p q
        have : p.IsMaximal := (hqp.under A).isMaximal (q.under_ne_bot A hq)
        let : Field (A ⧸ p) := Ideal.Quotient.field p
        have := IsArtinianRing.of_finite (A ⧸ p) (B ⧸ p.map (algebraMap A B))
        suffices q' = (p.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime q)) by
          rw [this, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
            IsScalarTower.algebraMap_eq A (Localization.AtPrime p) (Localization.AtPrime q),
            ← Ideal.map_map]
          infer_instance
        rw [← ((Ideal.isRadical_iff_quotient_reduced _).mpr (hf p)).radical,
          IsLocalization.map_radical q.primeCompl,
          IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime q) q,
          Localization.AtPrime.map_eq_maximalIdeal]
        rw [Ideal.minimalPrimes_eq_comap]
        exact ⟨q.map (Ideal.Quotient.mk (p.map (algebraMap A B))),
          IsArtinianRing.mem_minimalPrimes bot_le, Ideal.comap_map_mk Ideal.map_comap_le⟩ }
  infer_instance
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
lemma lpsOriginalPrimeGaussAffineOrder_dedekind
    (p : ℕ) [Fact p.Prime] :
    IsDedekindDomain (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p) := by
  let := lpsOriginalGaussBase_dvr p
  let := lpsOriginalGaussAffineOrder_domain p (Fact.out : p.Prime).pos p
  let : Module.Finite (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p) :=
    ((lpsOriginalIntegerPolynomial_monic p (Fact.out : p.Prime).pos).map _).finite_adjoinRoot
  apply QEC.Coding.AlgebraicGeometry.finite_dedekind_domain_of_reduced_maximal_fibres
    (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p)
  intro m hm
  rw [IsLocalRing.eq_maximalIdeal hm]
  exact lpsOriginalPrimeGaussAffineOrder_specialFiber_reduced p
lemma lpsOriginalPrimeGaussAffineOrder_integrallyClosed
    (p : ℕ) [Fact p.Prime] :
    IsIntegrallyClosed (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p) := by
  let := lpsOriginalPrimeGaussAffineOrder_dedekind p
  infer_instance
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
lemma lpsOriginalPrimeGaussAffineOrder_isIntegralClosure
    (p : ℕ) [Fact p.Prime] [NeZero p] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
      ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
    IsIntegralClosure (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p)
      (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
  let : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
    ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
  let := lpsOriginalGaussAffineOrder_domain p (Fact.out : p.Prime).pos p
  let := lpsOriginalGaussAffineGenerated_isFractionRing p (Fact.out : p.Prime).pos p
  let := lpsOriginalPrimeGaussAffineOrder_integrallyClosed p
  let : Module.Finite (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p) :=
    ((lpsOriginalIntegerPolynomial_monic p (Fact.out : p.Prime).pos).map _).finite_adjoinRoot
  let : IsScalarTower (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p)
      (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) := .of_algebraMap_eq' rfl
  infer_instance
def lpsOriginalPrimeGaussNormalizationEquiv
    (p : ℕ) [Fact p.Prime] [NeZero p] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
    letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
      ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
        (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
    LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p ≃ₐ[LPSOriginalGaussBase p]
      integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).toAlgebra
  letI : Algebra (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) :=
    ((lpsOriginalGaussAffineToGenerated p (Fact.out : p.Prime).pos p).comp
      (algebraMap (LPSOriginalGaussBase p) (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p))).toAlgebra
  letI : IsScalarTower (LPSOriginalGaussBase p)
      (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p)
      (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos) := .of_algebraMap_eq' rfl
  letI := lpsOriginalPrimeGaussAffineOrder_isIntegralClosure p
  exact IsIntegralClosure.equiv (LPSOriginalGaussBase p)
    (LPSOriginalGaussAffineOrder p (Fact.out : p.Prime).pos p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos)
    (integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ p (Fact.out : p.Prime).pos))
end
end QEC.Coding.TannerLiftedProduct
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
end
end QEC.Coding.TannerLiftedProduct


