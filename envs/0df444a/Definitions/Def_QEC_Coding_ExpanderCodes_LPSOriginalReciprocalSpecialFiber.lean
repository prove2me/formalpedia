-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalSpecialFiber
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalReciprocalSpecialFiber
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T04:27:01.102721+00:00
-- url     : https://prove2.me/theorems/7a119a6c-4dea-4c05-8954-c64f7b0ab4a9
-- title:
--   LPSOriginal Reciprocal Special Fiber
-- statement:
--   Definitions and structural lemmas for LPSOriginal Reciprocal Special Fiber, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalSpecialFiber.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSpecialFiberDescent
import Mathlib.Algebra.Polynomial.Reverse
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionInversion_involutive
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
lemma C_dvd_reverse_iff {R : Type*} [CommSemiring R]
    (a : R) (f : Polynomial R) : Polynomial.C a ∣ f.reverse ↔ Polynomial.C a ∣ f := by
  rw [Polynomial.C_dvd_iff_dvd_coeff,Polynomial.C_dvd_iff_dvd_coeff]
  constructor
  · intro h i
    have hi := h (Polynomial.revAt f.natDegree i)
    simpa only [Polynomial.coeff_reverse,Polynomial.revAt_invol] using hi
  · intro h i
    rw [Polynomial.coeff_reverse]
    exact h _
lemma integralElem_comp_iff_of_involutive
    {R K : Type*} [CommRing R] [CommRing K] (f : R →+* K) (t : R →+* R)
    (ht : Function.Involutive t) (y : K) :
    (f.comp t).IsIntegralElem y ↔ f.IsIntegralElem y := by
  have heq : (f.comp t).comp t = f := by
    ext x
    exact congrArg f (ht x)
  constructor
  · exact fun h => h.of_comp
  · intro h
    have h' : ((f.comp t).comp t).IsIntegralElem y := heq.symm ▸ h
    exact h'.of_comp
end
end QEC.Coding.AlgebraicGeometry
namespace QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalGaussPrime_isPrime
lemma lpsOriginalGaussX_isUnit (p : ℕ) [Fact p.Prime] :
    IsUnit (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X) := by
  apply IsLocalization.map_units (M := (lpsOriginalGaussPrime p).primeCompl)
    (LPSOriginalGaussBase p) ⟨Polynomial.X,?_⟩
  change ¬ lpsOriginalGaussCoefficientReduction p Polynomial.X = 0
  simp [lpsOriginalGaussCoefficientReduction]
def lpsOriginalGaussReciprocalPolynomialMap (p : ℕ) [Fact p.Prime] :
    Polynomial ℤ →+* LPSOriginalGaussBase p :=
  Polynomial.eval₂RingHom
    ((algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p)).comp Polynomial.C)
    (↑(lpsOriginalGaussX_isUnit p).unit⁻¹)
lemma lpsOriginalGaussReciprocalPolynomialMap_units
    (p : ℕ) [Fact p.Prime] (s : (lpsOriginalGaussPrime p).primeCompl) :
    IsUnit (lpsOriginalGaussReciprocalPolynomialMap p s) := by
  let G := LPSOriginalGaussBase p
  let u : Gˣ := (lpsOriginalGaussX_isUnit p).unit
  let i : ℤ →+* G := (algebraMap (Polynomial ℤ) G).comp Polynomial.C
  have hr : (s : Polynomial ℤ).reverse ∈ (lpsOriginalGaussPrime p).primeCompl := by
    intro h
    apply s.property
    have hd : Polynomial.C (p : ℤ) ∣ (s : Polynomial ℤ).reverse := by
      exact Ideal.mem_span_singleton.mp ((le_of_eq (lpsOriginalGaussPrime_eq_span p)) h)
    exact (le_of_eq (lpsOriginalGaussPrime_eq_span p).symm)
      (Ideal.mem_span_singleton.mpr
        ((QEC.Coding.AlgebraicGeometry.C_dvd_reverse_iff _ _).mp hd))
  have hmap : (s : Polynomial ℤ).reverse.eval₂ i (↑u : G) =
      algebraMap (Polynomial ℤ) G (s : Polynomial ℤ).reverse := by
    rw [show (↑u : G) = algebraMap (Polynomial ℤ) G Polynomial.X from
      (lpsOriginalGaussX_isUnit p).unit_spec]
    have h := Polynomial.hom_eval₂ (s : Polynomial ℤ).reverse Polynomial.C
      (algebraMap (Polynomial ℤ) G) Polynomial.X
    simpa only [Polynomial.eval₂_C_X] using h.symm
  have hrev := Polynomial.eval₂_reverse_mul_pow i (↑u⁻¹ : G) (s : Polynomial ℤ)
  have heq : lpsOriginalGaussReciprocalPolynomialMap p s =
      algebraMap (Polynomial ℤ) G (s : Polynomial ℤ).reverse * (↑u⁻¹ : G)^
        (s : Polynomial ℤ).natDegree := by
    change Polynomial.eval₂ i (↑u⁻¹ : G) (s : Polynomial ℤ) = _
    simpa only [invOf_units,inv_inv,hmap] using hrev.symm
  rw [heq]
  exact (IsLocalization.map_units G ⟨_,hr⟩).mul ((u⁻¹).isUnit.pow _)
def lpsOriginalGaussInversion (p : ℕ) [Fact p.Prime] :
    LPSOriginalGaussBase p →+* LPSOriginalGaussBase p :=
  IsLocalization.lift (M := (lpsOriginalGaussPrime p).primeCompl)
    (S := LPSOriginalGaussBase p)
    (g := lpsOriginalGaussReciprocalPolynomialMap p)
    (lpsOriginalGaussReciprocalPolynomialMap_units p)
lemma lpsOriginalGaussInversion_polynomial (p : ℕ) [Fact p.Prime]
    (f : Polynomial ℤ) :
    lpsOriginalGaussInversion p
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f) =
        lpsOriginalGaussReciprocalPolynomialMap p f := by
  simp [lpsOriginalGaussInversion]
lemma lpsOriginalGaussInversion_fractionDiagram (p : ℕ) [Fact p.Prime] :
    (lpsOriginalGaussBaseFractionMap p).comp (lpsOriginalGaussInversion p) =
      lpsOriginalJFractionInversion.comp (lpsOriginalGaussBaseFractionMap p) := by
  apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simp [RingHom.comp_apply,lpsOriginalGaussInversion_polynomial,
      lpsOriginalGaussReciprocalPolynomialMap,map_units_inv,
      IsUnit.unit_spec,lpsOriginalGaussBaseFractionMap_base,
      lpsOriginalJFractionInversion_X]
lemma lpsOriginalGaussInversion_involutive (p : ℕ) [Fact p.Prime] :
    Function.Involutive (lpsOriginalGaussInversion p) := by
  intro x
  apply lpsOriginalGaussBaseFractionMap_injective p
  have h := RingHom.congr_fun (lpsOriginalGaussInversion_fractionDiagram p)
  change ∀ z, lpsOriginalGaussBaseFractionMap p (lpsOriginalGaussInversion p z) =
    lpsOriginalJFractionInversion (lpsOriginalGaussBaseFractionMap p z) at h
  rw [h (lpsOriginalGaussInversion p x),h x,
    lpsOriginalJFractionInversion_involutive]
lemma lpsOriginalGaussBaseToGeneratedField_fractionDiagram
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGaussBaseToGeneratedField N hN p =
      (algebraMap (FractionRing (Polynomial ℚ))
        (lpsOriginalGeneratedFunctionFieldQ N hN)).comp (lpsOriginalGaussBaseFractionMap p) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply IsLocalization.ringHom_ext (lpsOriginalGaussPrime p).primeCompl
  apply RingHom.ext
  intro f
  change lpsOriginalGaussBaseToGeneratedField N hN p
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f) = _
  rw [lpsOriginalGaussBaseToGeneratedField_base]
  change algebraMap (FractionRing (Polynomial ℚ))
    (lpsOriginalGeneratedFunctionFieldQ N hN) (lpsOriginalIntegerBaseFractionMap f) = _
  change algebraMap (FractionRing (Polynomial ℚ))
    (lpsOriginalGeneratedFunctionFieldQ N hN) (lpsOriginalIntegerBaseFractionMap f) =
    algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
      (lpsOriginalGaussBaseFractionMap p (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f))
  rw [lpsOriginalGaussBaseFractionMap_base]
  rfl
def lpsOriginalReciprocalGaussBaseToGeneratedField
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    LPSOriginalGaussBase p →+* lpsOriginalGeneratedFunctionFieldQ N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact (lpsOriginalGaussBaseToGeneratedField N hN p).comp (lpsOriginalGaussInversion p)
lemma lpsOriginalReciprocalGaussBaseToGeneratedField_base
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (f : Polynomial ℤ) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalReciprocalGaussBaseToGeneratedField N hN p
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f) =
      lpsOriginalIntegerReciprocalBaseToGeneratedField N hN f := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  rw [lpsOriginalReciprocalGaussBaseToGeneratedField,
    lpsOriginalGaussBaseToGeneratedField_fractionDiagram]
  have h := RingHom.congr_fun (lpsOriginalGaussInversion_fractionDiagram p)
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f)
  change lpsOriginalGaussBaseFractionMap p (lpsOriginalGaussInversion p
    (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f)) =
    lpsOriginalJFractionInversion (lpsOriginalGaussBaseFractionMap p
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f)) at h
  change algebraMap (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN)
    (lpsOriginalGaussBaseFractionMap p (lpsOriginalGaussInversion p
      (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) f))) = _
  rw [h,lpsOriginalGaussBaseFractionMap_base]
  rfl
lemma lpsOriginalReciprocalGaussBase_scalarTower
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalReciprocalGaussBaseToGeneratedField N hN p).toAlgebra
    IsScalarTower (Polynomial ℤ) (LPSOriginalGaussBase p)
      (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalReciprocalGaussBaseToGeneratedField N hN p).toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro f
  exact (lpsOriginalReciprocalGaussBaseToGeneratedField_base N hN p f).symm
lemma lpsOriginalGaussIntegral_reciprocalIntegral_iff
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (y : lpsOriginalGeneratedFunctionFieldQ N hN) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalReciprocalGaussBaseToGeneratedField N hN p).IsIntegralElem y ↔
      (lpsOriginalGaussBaseToGeneratedField N hN p).IsIntegralElem y := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact QEC.Coding.AlgebraicGeometry.integralElem_comp_iff_of_involutive
    (lpsOriginalGaussBaseToGeneratedField N hN p) (lpsOriginalGaussInversion p)
    (lpsOriginalGaussInversion_involutive p) y
attribute [local instance] gaussFiberBaseFieldAlgebra gaussFiberNormalizationCommRing
  gaussFiberNormalizationRing gaussFiberNormalizationSemiring
def lpsOriginalIntegerNormalInfinityToGaussNormalization
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
    integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN) →+*
      integralClosure (LPSOriginalGaussBase p) (lpsOriginalGeneratedFunctionFieldQ N hN) := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
  let := (lpsOriginalGaussBaseToGeneratedField N hN p).toAlgebra
  exact { toFun := fun x => ⟨x.val,by
            apply (lpsOriginalGaussIntegral_reciprocalIntegral_iff N hN p x.val).mp
            let := (lpsOriginalReciprocalGaussBaseToGeneratedField N hN p).toAlgebra
            let := lpsOriginalReciprocalGaussBase_scalarTower N hN p
            exact x.property.tower_top⟩
          map_one' := rfl
          map_mul' _ _ := rfl
          map_zero' := rfl
          map_add' _ _ := rfl }
end
end QEC.Coding.TannerLiftedProduct


