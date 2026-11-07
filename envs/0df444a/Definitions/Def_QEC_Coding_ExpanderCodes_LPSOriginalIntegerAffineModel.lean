-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T02:11:24.572228+00:00
-- url     : https://prove2.me/theorems/7d87b789-4bb3-4dac-ad94-56be1e20d1ff
-- title:
--   LPSOriginal Integer Affine Model
-- statement:
--   Definitions and structural lemmas for LPSOriginal Integer Affine Model, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerAffineModel.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.Integral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbeddingQ_polynomial
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJHolomorphicEvalQ_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_integralQ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNMonicAnnihilatorUniqueQ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJ_jN_integer_monic_relation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalRelation_fractionRoot
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
open scoped UpperHalfPlane MatrixGroups
noncomputable section
def lpsOriginalIntegerPolynomial (N : ℕ) [NeZero N] (hN : 0<N) :
    Polynomial (Polynomial ℤ) :=
  (lpsOriginalJ_jN_integer_monic_relation N hN).choose
lemma lpsOriginalIntegerPolynomial_monic (N : ℕ) [NeZero N] (hN : 0<N) :
    (lpsOriginalIntegerPolynomial N hN).Monic :=
  (lpsOriginalJ_jN_integer_monic_relation N hN).choose_spec.1
lemma lpsOriginalIntegerPolynomial_degree (N : ℕ) [NeZero N] (hN : 0<N) :
    (lpsOriginalIntegerPolynomial N hN).natDegree=
      Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :=
  (lpsOriginalJ_jN_integer_monic_relation N hN).choose_spec.2.1
lemma lpsOriginalIntegerPolynomial_root (N : ℕ) [NeZero N] (hN : 0<N) (τ : ℍ) :
    (lpsOriginalIntegerPolynomial N hN).eval₂
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) (lpsOriginalJDilated N hN τ)=0 :=
  (lpsOriginalJ_jN_integer_monic_relation N hN).choose_spec.2.2 τ
lemma lpsOriginalIntegerCoefficientMap_injective :
    Function.Injective (Polynomial.mapRingHom (algebraMap ℤ ℚ)) := by
  apply Polynomial.map_injective
  intro z w h
  change (z:ℚ)=(w:ℚ) at h
  exact_mod_cast h
def lpsOriginalIntegerPolynomialRational (N : ℕ) [NeZero N] (hN : 0<N) :
    Polynomial (Polynomial ℚ) :=
  (lpsOriginalIntegerPolynomial N hN).map
    (Polynomial.mapRingHom (algebraMap ℤ ℚ))
lemma lpsOriginalIntegerPolynomialRational_monic (N : ℕ) [NeZero N] (hN : 0<N) :
    (lpsOriginalIntegerPolynomialRational N hN).Monic :=
  (lpsOriginalIntegerPolynomial_monic N hN).map _
lemma lpsOriginalIntegerPolynomialRational_degree (N : ℕ) [NeZero N] (hN : 0<N) :
    (lpsOriginalIntegerPolynomialRational N hN).natDegree=
      Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by
  rw [lpsOriginalIntegerPolynomialRational,
    Polynomial.natDegree_map_eq_of_injective lpsOriginalIntegerCoefficientMap_injective,
    lpsOriginalIntegerPolynomial_degree N hN]
lemma lpsOriginalIntegerPolynomialRational_root (N : ℕ) [NeZero N] (hN : 0<N) (τ : ℍ) :
    (lpsOriginalIntegerPolynomialRational N hN).eval₂
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ)=0 := by
  have hc : (((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
      (Polynomial.mapRingHom (algebraMap ℚ ℂ))).comp
      (Polynomial.mapRingHom (algebraMap ℤ ℚ)))=
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) := by
    apply RingHom.ext
    intro P
    change ((P.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℂ)).eval
      (lpsOriginalJInvariant τ)=(P.map (Int.castRingHom ℂ)).eval (lpsOriginalJInvariant τ)
    rw [Polynomial.map_map]
    have he : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ)=Int.castRingHom ℂ := by
      apply RingHom.ext
      intro z
      simp only [RingHom.comp_apply,algebraMap_int_eq,Int.coe_castRingHom,map_intCast]
    rw [he]
  rw [lpsOriginalIntegerPolynomialRational,Polynomial.eval₂_map,hc]
  exact lpsOriginalIntegerPolynomial_root N hN τ
lemma lpsOriginalIntegerPolynomial_minpoly (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalIntegerPolynomialRational N hN).map
        (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))=
      minpoly (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply lpsOriginalJNMonicAnnihilatorUniqueQ N hN
  · exact (lpsOriginalIntegerPolynomialRational_monic N hN).map _
  · exact Polynomial.natDegree_map_le.trans
      (lpsOriginalIntegerPolynomialRational_degree N hN).le
  · exact lpsOriginalRationalRelation_fractionRoot N hN
      (lpsOriginalIntegerPolynomialRational N hN)
      (lpsOriginalIntegerPolynomialRational_root N hN)
lemma lpsOriginalIntegerPolynomialRational_irreducible (N : ℕ) [NeZero N] (hN : 0<N) :
    Irreducible (lpsOriginalIntegerPolynomialRational N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply (lpsOriginalIntegerPolynomialRational_monic N hN).isPrimitive.irreducible_of_irreducible_map_of_injective
      (IsFractionRing.injective (Polynomial ℚ) (FractionRing (Polynomial ℚ)))
  rw [lpsOriginalIntegerPolynomial_minpoly N hN]
  exact minpoly.irreducible (lpsOriginalJNInFractionField_integralQ N hN)
lemma lpsOriginalIntegerPolynomial_irreducible (N : ℕ) [NeZero N] (hN : 0<N) :
    Irreducible (lpsOriginalIntegerPolynomial N hN) := by
  apply (lpsOriginalIntegerPolynomial_monic N hN).isPrimitive.irreducible_of_irreducible_map_of_injective
    lpsOriginalIntegerCoefficientMap_injective
  exact lpsOriginalIntegerPolynomialRational_irreducible N hN
def lpsOriginalJHolomorphicEvalZ : Polynomial ℤ →+* LPSOriginalHolomorphicRing :=
  lpsOriginalJHolomorphicEvalQ.comp (Polynomial.mapRingHom (algebraMap ℤ ℚ))
lemma lpsOriginalIntegerPolynomial_holomorphicRoot
    (N : ℕ) [NeZero N] (hN : 0<N) :
    (lpsOriginalIntegerPolynomial N hN).eval₂ lpsOriginalJHolomorphicEvalZ
      (lpsOriginalJNHolomorphic N hN)=0 := by
  apply Subtype.ext
  funext τ
  let e : LPSOriginalHolomorphicRing →+* ℂ :=
    { toFun f := f.val τ
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hc : e.comp lpsOriginalJHolomorphicEvalZ=
      ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ))) := by
    apply RingHom.ext
    intro P
    change (lpsOriginalJHolomorphicEvalQ (P.map (algebraMap ℤ ℚ))).val τ=
      (P.map (Int.castRingHom ℂ)).eval (lpsOriginalJInvariant τ)
    rw [lpsOriginalJHolomorphicEvalQ_apply,Polynomial.eval_map,Polynomial.eval₂_map]
    congr 1
  have h := Polynomial.hom_eval₂ (lpsOriginalIntegerPolynomial N hN)
    lpsOriginalJHolomorphicEvalZ e (lpsOriginalJNHolomorphic N hN)
  rw [hc] at h
  exact h.trans (lpsOriginalIntegerPolynomial_root N hN τ)
abbrev lpsOriginalIntegerAffineRing (N : ℕ) [NeZero N] (hN : 0<N) : Type :=
  AdjoinRoot (lpsOriginalIntegerPolynomial N hN)
lemma lpsOriginalIntegerAffineRing_domain (N : ℕ) [NeZero N] (hN : 0<N) :
    IsDomain (lpsOriginalIntegerAffineRing N hN) :=
  AdjoinRoot.isDomain_of_prime (lpsOriginalIntegerPolynomial_irreducible N hN).prime
lemma lpsOriginalIntegerAffineRing_finite (N : ℕ) [NeZero N] (hN : 0<N) :
    Module.Finite (Polynomial ℤ) (lpsOriginalIntegerAffineRing N hN) :=
  (lpsOriginalIntegerPolynomial_monic N hN).finite_adjoinRoot
def lpsOriginalIntegerAffineEval (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalIntegerAffineRing N hN →+* LPSOriginalHolomorphicRing :=
  AdjoinRoot.lift lpsOriginalJHolomorphicEvalZ (lpsOriginalJNHolomorphic N hN)
    (lpsOriginalIntegerPolynomial_holomorphicRoot N hN)
lemma lpsOriginalIntegerPolynomial_aevalLocalization
    (N : ℕ) [NeZero N] (hN : 0<N) (p : Polynomial (Polynomial ℤ)) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Polynomial.aeval (lpsOriginalJNInFractionField N hN)
        (p.map ((algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))).comp
          (Polynomial.mapRingHom (algebraMap ℤ ℚ))))=
      algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        (p.eval₂ lpsOriginalJHolomorphicEvalZ (lpsOriginalJNHolomorphic N hN)) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  have hc : (algebraMap (FractionRing (Polynomial ℚ)) LPSOriginalHolomorphicFractionField).comp
      ((algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))).comp
        (Polynomial.mapRingHom (algebraMap ℤ ℚ)))=
      (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
        lpsOriginalJHolomorphicEvalZ := by
    apply RingHom.ext
    intro P
    exact lpsOriginalJFractionEmbeddingQ_polynomial (P.map (algebraMap ℤ ℚ))
  rw [Polynomial.aeval_def,Polynomial.eval₂_map,hc]
  exact (Polynomial.hom_eval₂ p lpsOriginalJHolomorphicEvalZ
    (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
    (lpsOriginalJNHolomorphic N hN)).symm
lemma lpsOriginalIntegerPolynomial_eval_zero_iff_dvd
    (N : ℕ) [NeZero N] (hN : 0<N) (p : Polynomial (Polynomial ℤ)) :
    p.eval₂ lpsOriginalJHolomorphicEvalZ (lpsOriginalJNHolomorphic N hN)=0 ↔
      lpsOriginalIntegerPolynomial N hN ∣ p := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let f : Polynomial ℤ →+* FractionRing (Polynomial ℚ) :=
    (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))).comp
      (Polynomial.mapRingHom (algebraMap ℤ ℚ))
  have hf : Function.Injective f :=
    (IsFractionRing.injective (Polynomial ℚ) (FractionRing (Polynomial ℚ))).comp
      lpsOriginalIntegerCoefficientMap_injective
  have hPhi : (lpsOriginalIntegerPolynomial N hN).map f=
      minpoly (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN) := by
    change ((lpsOriginalIntegerPolynomial N hN).map
      ((algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))).comp
        (Polynomial.mapRingHom (algebraMap ℤ ℚ))))=_
    rw [←Polynomial.map_map]
    exact lpsOriginalIntegerPolynomial_minpoly N hN
  rw [←Polynomial.map_dvd_map f hf (lpsOriginalIntegerPolynomial_monic N hN),hPhi,
    minpoly.dvd_iff,lpsOriginalIntegerPolynomial_aevalLocalization N hN p]
  exact (map_eq_zero_iff (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)
    (IsFractionRing.injective LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField)).symm
lemma lpsOriginalIntegerAffineEval_injective (N : ℕ) [NeZero N] (hN : 0<N) :
    Function.Injective (lpsOriginalIntegerAffineEval N hN) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    rw [lpsOriginalIntegerAffineEval,AdjoinRoot.lift_mk] at hx
    exact AdjoinRoot.mk_eq_zero.mpr
      ((lpsOriginalIntegerPolynomial_eval_zero_iff_dvd N hN p).mp hx)
lemma lpsOriginalPolynomial_eval_mem_subfield
    {R K : Type*} [CommRing R] [Field K] (F : Subfield K)
    (f : R →+* K) (hf : ∀ r, f r ∈ F) (x : K) (hx : x ∈ F)
    (p : Polynomial R) : p.eval₂ f x ∈ F := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval₂_add] using F.add_mem hp hq
  | monomial n r =>
    simpa only [Polynomial.eval₂_monomial] using F.mul_mem (hf r) (F.pow_mem hx n)
def lpsOriginalIntegerAffineLocalizedEval
    (N : ℕ) [NeZero N] (hN : 0<N) :
    lpsOriginalIntegerAffineRing N hN →+* LPSOriginalHolomorphicFractionField :=
  (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
    (lpsOriginalIntegerAffineEval N hN)
lemma lpsOriginalIntegerAffineLocalizedEval_injective
    (N : ℕ) [NeZero N] (hN : 0<N) :
    Function.Injective (lpsOriginalIntegerAffineLocalizedEval N hN) :=
  (IsFractionRing.injective LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
    (lpsOriginalIntegerAffineEval_injective N hN)
def lpsOriginalIntegerAffineFractionEmbedding
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalIntegerAffineRing_domain N hN
    FractionRing (lpsOriginalIntegerAffineRing N hN) →+*
      LPSOriginalHolomorphicFractionField := by
  letI := lpsOriginalIntegerAffineRing_domain N hN
  exact IsFractionRing.lift (lpsOriginalIntegerAffineLocalizedEval_injective N hN)
lemma lpsOriginalIntegerAffineFractionEmbedding_algebraMap
    (N : ℕ) [NeZero N] (hN : 0<N)
    (x : lpsOriginalIntegerAffineRing N hN) :
    letI := lpsOriginalIntegerAffineRing_domain N hN
    lpsOriginalIntegerAffineFractionEmbedding N hN
        (algebraMap (lpsOriginalIntegerAffineRing N hN)
          (FractionRing (lpsOriginalIntegerAffineRing N hN)) x)=
      lpsOriginalIntegerAffineLocalizedEval N hN x := by
  let := lpsOriginalIntegerAffineRing_domain N hN
  exact IsFractionRing.lift_algebraMap _ x
lemma lpsOriginalJHolomorphicEvalQ_localized (p : Polynomial ℚ) :
    algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        (lpsOriginalJHolomorphicEvalQ p)=
      p.eval₂ (algebraMap ℚ LPSOriginalHolomorphicFractionField)
        (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
          lpsOriginalJHolomorphic) := by
  have h : (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
      lpsOriginalJHolomorphicEvalQ=
      Polynomial.eval₂RingHom (algebraMap ℚ LPSOriginalHolomorphicFractionField)
        (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
          lpsOriginalJHolomorphic) := by
    apply Polynomial.ringHom_ext
    · intro q
      change algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
          ((Polynomial.aeval lpsOriginalJHolomorphic) ((Polynomial.C q).map (algebraMap ℚ ℂ)))=
        (Polynomial.C q).eval₂ (algebraMap ℚ LPSOriginalHolomorphicFractionField)
          (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
            lpsOriginalJHolomorphic)
      rw [Polynomial.map_C,Polynomial.aeval_C,Polynomial.eval₂_C]
      exact RingHom.map_rat_algebraMap
        ((algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
          (algebraMap ℂ LPSOriginalHolomorphicRing)) q
    · simp [lpsOriginalJHolomorphicEvalQ,lpsOriginalJHolomorphicEval,
        Polynomial.aeval_def]
  exact RingHom.congr_fun h p
lemma lpsOriginalIntegerAffineFractionEmbedding_range
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerAffineRing_domain N hN
    (lpsOriginalIntegerAffineFractionEmbedding N hN).fieldRange=
      (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerAffineRing_domain N hN
  let F := Subfield.closure (lpsOriginalIntegerAffineLocalizedEval N hN).range.carrier
  have hr : (lpsOriginalIntegerAffineFractionEmbedding N hN).fieldRange=F :=
    IsFractionRing.lift_fieldRange _
  have hz (P : Polynomial ℤ) :
      algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        (lpsOriginalJHolomorphicEvalZ P) ∈ F := by
    apply Subfield.subset_closure
    refine ⟨AdjoinRoot.of (lpsOriginalIntegerPolynomial N hN) P,?_⟩
    simp [lpsOriginalIntegerAffineLocalizedEval,lpsOriginalIntegerAffineEval,
      AdjoinRoot.lift_of]
  have hj : algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
      lpsOriginalJHolomorphic ∈ F := by
    simpa [lpsOriginalJHolomorphicEvalZ,lpsOriginalJHolomorphicEvalQ,
      lpsOriginalJHolomorphicEval,Polynomial.aeval_def] using hz Polynomial.X
  have hq (P : Polynomial ℚ) :
      algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        (lpsOriginalJHolomorphicEvalQ P) ∈ F := by
    rw [lpsOriginalJHolomorphicEvalQ_localized]
    exact lpsOriginalPolynomial_eval_mem_subfield F _
      (fun q => by
        rw [show algebraMap ℚ LPSOriginalHolomorphicFractionField q=(q:LPSOriginalHolomorphicFractionField) by
          simpa only [Rat.cast_id] using
            map_ratCast (algebraMap ℚ LPSOriginalHolomorphicFractionField) q]
        exact SubfieldClass.ratCast_mem F q) _ hj P
  have hb (x : FractionRing (Polynomial ℚ)) : lpsOriginalJFractionEmbeddingQ x ∈ F := by
    obtain ⟨a,b,_,rfl⟩ := IsFractionRing.div_surjective (Polynomial ℚ) x
    rw [map_div₀,lpsOriginalJFractionEmbeddingQ_polynomial,
      lpsOriginalJFractionEmbeddingQ_polynomial]
    exact F.div_mem (hq a) (hq b)
  have hn : lpsOriginalJNInFractionField N hN ∈ F := by
    apply Subfield.subset_closure
    refine ⟨AdjoinRoot.root (lpsOriginalIntegerPolynomial N hN),?_⟩
    simp [lpsOriginalIntegerAffineLocalizedEval,lpsOriginalIntegerAffineEval,
      AdjoinRoot.lift_root,lpsOriginalJNInFractionField]
  rw [hr,lpsOriginalGeneratedFunctionFieldQ,IntermediateField.adjoin_toSubfield]
  apply le_antisymm
  · apply Subfield.closure_le.mpr
    rintro x ⟨a,rfl⟩
    induction a using AdjoinRoot.induction_on with
    | ih p =>
      let K := Subfield.closure
        (Set.range lpsOriginalJFractionEmbeddingQ ∪ {lpsOriginalJNInFractionField N hN})
      have hzK (P : Polynomial ℤ) :
          algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
            (lpsOriginalJHolomorphicEvalZ P) ∈ K := by
        rw [lpsOriginalJHolomorphicEvalZ, RingHom.comp_apply,
          ← lpsOriginalJFractionEmbeddingQ_polynomial]
        exact Subfield.subset_closure (Or.inl ⟨_,rfl⟩)
      change algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        ((lpsOriginalIntegerAffineEval N hN)
          (AdjoinRoot.mk (lpsOriginalIntegerPolynomial N hN) p)) ∈ K
      rw [lpsOriginalIntegerAffineEval,AdjoinRoot.lift_mk]
      rw [Polynomial.hom_eval₂]
      exact lpsOriginalPolynomial_eval_mem_subfield K _ hzK _
        (Subfield.subset_closure (Or.inr (Set.mem_singleton _))) p
  · apply Subfield.closure_le.mpr
    rintro x (⟨a,rfl⟩ | hx)
    · exact hb a
    · exact (Set.mem_singleton_iff.mp hx) ▸ hn
def lpsOriginalIntegerBaseFractionMap :
    Polynomial ℤ →+* FractionRing (Polynomial ℚ) :=
  (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))).comp
    (Polynomial.mapRingHom (algebraMap ℤ ℚ))
def lpsOriginalIntegerBaseToGeneratedField
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Polynomial ℤ →+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)).comp
    lpsOriginalIntegerBaseFractionMap
lemma lpsOriginalIntegerAffineLocalizedEval_memGenerated
    (N : ℕ) [NeZero N] (hN : 0<N) (x : lpsOriginalIntegerAffineRing N hN) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerAffineLocalizedEval N hN x ∈
      lpsOriginalGeneratedFunctionFieldQ N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerAffineRing_domain N hN
  change lpsOriginalIntegerAffineLocalizedEval N hN x ∈
    (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield
  rw [←lpsOriginalIntegerAffineFractionEmbedding_range N hN]
  exact ⟨algebraMap (lpsOriginalIntegerAffineRing N hN)
    (FractionRing (lpsOriginalIntegerAffineRing N hN)) x,
      lpsOriginalIntegerAffineFractionEmbedding_algebraMap N hN x⟩
def lpsOriginalIntegerAffineToGenerated
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerAffineRing N hN →+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (lpsOriginalIntegerAffineLocalizedEval N hN).codRestrict
    (lpsOriginalGeneratedFunctionFieldQ N hN).toSubring
    (lpsOriginalIntegerAffineLocalizedEval_memGenerated N hN)
lemma lpsOriginalIntegerAffineToGenerated_base
    (N : ℕ) [NeZero N] (hN : 0<N) (P : Polynomial ℤ) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalIntegerAffineToGenerated N hN
        (AdjoinRoot.of (lpsOriginalIntegerPolynomial N hN) P)=
      lpsOriginalIntegerBaseToGeneratedField N hN P := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply Subtype.ext
  change (lpsOriginalIntegerAffineLocalizedEval N hN)
      (AdjoinRoot.of (lpsOriginalIntegerPolynomial N hN) P)=
    lpsOriginalJFractionEmbeddingQ (lpsOriginalIntegerBaseFractionMap P)
  rw [lpsOriginalIntegerBaseFractionMap,RingHom.comp_apply,
    lpsOriginalJFractionEmbeddingQ_polynomial]
  simp [lpsOriginalIntegerAffineLocalizedEval,lpsOriginalIntegerAffineEval,
    lpsOriginalJHolomorphicEvalZ,AdjoinRoot.lift_of]
def lpsOriginalIntegerAffineToGeneratedAlgHom
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    lpsOriginalIntegerAffineRing N hN →ₐ[Polynomial ℤ]
      lpsOriginalGeneratedFunctionFieldQ N hN := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact { lpsOriginalIntegerAffineToGenerated N hN with
    commutes' := lpsOriginalIntegerAffineToGenerated_base N hN }
lemma lpsOriginalIntegerAffineToGenerated_integral
    (N : ℕ) [NeZero N] (hN : 0<N) (x : lpsOriginalIntegerAffineRing N hN) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    IsIntegral (Polynomial ℤ) (lpsOriginalIntegerAffineToGeneratedAlgHom N hN x) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  let := lpsOriginalIntegerAffineRing_finite N hN
  exact (IsIntegral.of_finite (Polynomial ℤ) x).map
    (lpsOriginalIntegerAffineToGeneratedAlgHom N hN)
def lpsOriginalIntegerAffineToNormal
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
    lpsOriginalIntegerAffineRing N hN →ₐ[Polynomial ℤ]
      integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  letI := (lpsOriginalIntegerBaseToGeneratedField N hN).toAlgebra
  exact (lpsOriginalIntegerAffineToGeneratedAlgHom N hN).codRestrict
    (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN))
    (lpsOriginalIntegerAffineToGenerated_integral N hN)
end
end QEC.Coding.TannerLiftedProduct


