-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
-- name    : QEC_Coding_ExpanderCodes_LPSOriginalRationalHeckePullback
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T02:58:16.554268+00:00
-- url     : https://prove2.me/theorems/27ac2eaa-77a2-462d-b8db-89591059e3dc
-- title:
--   LPSOriginal Rational Hecke Pullback
-- statement:
--   Definitions and structural lemmas for LPSOriginal Rational Hecke Pullback, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalHeckePullback.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_det
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_level_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilated_coe
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbeddingQ_polynomial
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
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
def lpsOriginalPositiveHolomorphicPullback (g : GL (Fin 2) ℝ)
    (hg : 0 < g.det.val) :
    LPSOriginalHolomorphicRing ≃ₐ[ℂ] LPSOriginalHolomorphicRing where
  toFun f := ⟨fun τ => f.val (g • τ), f.property.comp
    (UpperHalfPlane.mdifferentiable_smul hg)⟩
  invFun f := ⟨fun τ => f.val (g⁻¹ • τ), f.property.comp
    (UpperHalfPlane.mdifferentiable_smul (by
      simpa only [map_inv, Units.val_inv_eq_inv_val] using inv_pos.mpr hg))⟩
  left_inv f := by apply Subtype.ext; funext τ; simp only [smul_inv_smul]
  right_inv f := by apply Subtype.ext; funext τ; simp only [inv_smul_smul]
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
def lpsOriginalPositiveFractionPullback (g : GL (Fin 2) ℝ)
    (hg : 0 < g.det.val) :
    LPSOriginalHolomorphicFractionField ≃+* LPSOriginalHolomorphicFractionField :=
  IsFractionRing.ringEquivOfRingEquiv
    (lpsOriginalPositiveHolomorphicPullback g hg).toRingEquiv
lemma lpsOriginalPositiveFractionPullback_localization
    (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val) (f : LPSOriginalHolomorphicRing) :
    lpsOriginalPositiveFractionPullback g hg
        (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField f) =
      algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        (lpsOriginalPositiveHolomorphicPullback g hg f) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ f
def lpsOriginalFrickeMatrix (N : ℕ) (hN : 0 < N) : GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S * lpsE2AffineMatrix N hN 0
lemma lpsOriginalFrickeMatrix_det (N : ℕ) (hN : 0 < N) :
    (lpsOriginalFrickeMatrix N hN).det.val = (N : ℝ) := by
  calc
    (lpsOriginalFrickeMatrix N hN).det.val =
        (lpsE2AffineMatrix N hN 0).det.val := by simp [lpsOriginalFrickeMatrix]
    _ = (N : ℝ) := lpsE2AffineMatrix_det N hN 0
lemma lpsOriginalFrickeMatrix_pos (N : ℕ) (hN : 0 < N) :
    0 < (lpsOriginalFrickeMatrix N hN).det.val := by
  rw [lpsOriginalFrickeMatrix_det]
  exact_mod_cast hN
lemma lpsOriginalPositiveHolomorphicPullback_fricke_j
    (N : ℕ) (hN : 0 < N) :
    lpsOriginalPositiveHolomorphicPullback (lpsOriginalFrickeMatrix N hN)
      (lpsOriginalFrickeMatrix_pos N hN) lpsOriginalJHolomorphic =
        lpsOriginalJNHolomorphic N hN := by
  apply Subtype.ext
  funext τ
  change lpsOriginalJInvariant
    ((Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S * lpsE2AffineMatrix N hN 0) • τ) =
      lpsOriginalJInvariant (lpsE2AffineMatrix N hN 0 • τ)
  rw [mul_smul]
  exact lpsOriginalJInvariant_SL_invariant _ ⟨ModularGroup.S, rfl⟩ _
lemma lpsOriginalFrickeMatrix_action (N : ℕ) (hN : 0 < N) (τ : ℍ) :
    ((lpsOriginalFrickeMatrix N hN • τ : ℍ) : ℂ) =
      (-((N : ℂ) * (τ : ℂ)))⁻¹ := by
  rw [lpsOriginalFrickeMatrix, mul_smul]
  change ((ModularGroup.S • (lpsE2AffineMatrix N hN 0 • τ) : ℍ) : ℂ) = _
  rw [UpperHalfPlane.modular_S_smul]
  simp only [lpsOriginalJDilated_coe]
lemma lpsOriginalDilation_fricke (N : ℕ) (hN : 0 < N) (τ : ℍ) :
    lpsE2AffineMatrix N hN 0 • (lpsOriginalFrickeMatrix N hN • τ) =
      Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • τ := by
  apply UpperHalfPlane.ext
  rw [lpsOriginalJDilated_coe, lpsOriginalFrickeMatrix_action]
  change (N : ℂ) * (-((N : ℂ) * (τ : ℂ)))⁻¹ = ((ModularGroup.S • τ : ℍ) : ℂ)
  rw [UpperHalfPlane.modular_S_smul]
  change (N : ℂ) * (-((N : ℂ) * (τ : ℂ)))⁻¹ = (-(τ : ℂ))⁻¹
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
lemma lpsOriginalPositiveHolomorphicPullback_fricke_jN
    (N : ℕ) (hN : 0 < N) :
    lpsOriginalPositiveHolomorphicPullback (lpsOriginalFrickeMatrix N hN)
      (lpsOriginalFrickeMatrix_pos N hN) (lpsOriginalJNHolomorphic N hN) =
        lpsOriginalJHolomorphic := by
  apply Subtype.ext
  funext τ
  change lpsOriginalJInvariant (lpsE2AffineMatrix N hN 0 •
      (lpsOriginalFrickeMatrix N hN • τ)) = lpsOriginalJInvariant τ
  rw [lpsOriginalDilation_fricke]
  exact lpsOriginalJInvariant_SL_invariant _ ⟨ModularGroup.S, rfl⟩ _
lemma lpsOriginalDilation_fricke_product (N p : ℕ) (hN : 0 < N) (hp : 0 < p)
    (τ : ℍ) :
    lpsE2AffineMatrix N hN 0 •
      (lpsOriginalFrickeMatrix (N*p) (Nat.mul_pos hN hp) • τ) =
    Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S • (lpsE2AffineMatrix p hp 0 • τ) := by
  apply UpperHalfPlane.ext
  rw [lpsOriginalJDilated_coe, lpsOriginalFrickeMatrix_action]
  change (N : ℂ) * (-(((N*p : ℕ) : ℂ) * (τ : ℂ)))⁻¹ =
    ((ModularGroup.S • (lpsE2AffineMatrix p hp 0 • τ) : ℍ) : ℂ)
  rw [UpperHalfPlane.modular_S_smul]
  simp only [lpsOriginalJDilated_coe, Nat.cast_mul]
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
lemma lpsOriginalPositiveHolomorphicPullback_fricke_product_jN
    (N p : ℕ) (hN : 0 < N) (hp : 0 < p) :
    lpsOriginalPositiveHolomorphicPullback
      (lpsOriginalFrickeMatrix (N*p) (Nat.mul_pos hN hp))
      (lpsOriginalFrickeMatrix_pos (N*p) (Nat.mul_pos hN hp))
      (lpsOriginalJNHolomorphic N hN) = lpsOriginalJNHolomorphic p hp := by
  apply Subtype.ext
  funext τ
  change lpsOriginalJInvariant (lpsE2AffineMatrix N hN 0 •
    (lpsOriginalFrickeMatrix (N*p) (Nat.mul_pos hN hp) • τ)) =
      lpsOriginalJInvariant (lpsE2AffineMatrix p hp 0 • τ)
  rw [lpsOriginalDilation_fricke_product]
  exact lpsOriginalJInvariant_SL_invariant _ ⟨ModularGroup.S, rfl⟩ _
def lpsOriginalJInFractionField : LPSOriginalHolomorphicFractionField :=
  algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField lpsOriginalJHolomorphic
lemma lpsOriginalPositiveFractionPullback_fricke_j (N : ℕ) (hN : 0 < N) :
    lpsOriginalPositiveFractionPullback (lpsOriginalFrickeMatrix N hN)
      (lpsOriginalFrickeMatrix_pos N hN) lpsOriginalJInFractionField =
        lpsOriginalJNInFractionField N hN := by
  rw [lpsOriginalJInFractionField, lpsOriginalPositiveFractionPullback_localization,
    lpsOriginalPositiveHolomorphicPullback_fricke_j]
  rfl
lemma lpsOriginalPositiveFractionPullback_fricke_jN (N : ℕ) (hN : 0 < N) :
    lpsOriginalPositiveFractionPullback (lpsOriginalFrickeMatrix N hN)
      (lpsOriginalFrickeMatrix_pos N hN) (lpsOriginalJNInFractionField N hN) =
        lpsOriginalJInFractionField := by
  rw [lpsOriginalJNInFractionField, lpsOriginalPositiveFractionPullback_localization,
    lpsOriginalPositiveHolomorphicPullback_fricke_jN]
  rfl
lemma lpsOriginalPositiveFractionPullback_fricke_product_jN
    (N p : ℕ) (hN : 0 < N) (hp : 0 < p) :
    lpsOriginalPositiveFractionPullback
      (lpsOriginalFrickeMatrix (N*p) (Nat.mul_pos hN hp))
      (lpsOriginalFrickeMatrix_pos (N*p) (Nat.mul_pos hN hp))
      (lpsOriginalJNInFractionField N hN) = lpsOriginalJNInFractionField p hp := by
  rw [lpsOriginalJNInFractionField, lpsOriginalPositiveFractionPullback_localization,
    lpsOriginalPositiveHolomorphicPullback_fricke_product_jN]
  rfl
lemma lpsOriginalJHolomorphicEvalQ_localization (P : Polynomial ℚ) :
    algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
      (lpsOriginalJHolomorphicEvalQ P) =
        P.eval₂ (algebraMap ℚ LPSOriginalHolomorphicFractionField) lpsOriginalJInFractionField := by
  have he : (algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField).comp
      lpsOriginalJHolomorphicEvalQ =
        Polynomial.eval₂RingHom (algebraMap ℚ LPSOriginalHolomorphicFractionField)
          lpsOriginalJInFractionField := by
    apply Polynomial.ringHom_ext
    · intro q
      simp [lpsOriginalJHolomorphicEvalQ, lpsOriginalJHolomorphicEval,
        Polynomial.aeval_def]
      exact map_ratCast ((algebraMap LPSOriginalHolomorphicRing
        LPSOriginalHolomorphicFractionField).comp
          (algebraMap ℂ LPSOriginalHolomorphicRing)) q
    · simp [lpsOriginalJHolomorphicEvalQ, lpsOriginalJHolomorphicEval,
        Polynomial.aeval_def, lpsOriginalJInFractionField]
  exact RingHom.congr_fun he P
lemma lpsOriginalJFractionEmbeddingQ_mem (S : Subfield LPSOriginalHolomorphicFractionField)
    (hj : lpsOriginalJInFractionField ∈ S) (a : FractionRing (Polynomial ℚ)) :
    lpsOriginalJFractionEmbeddingQ a ∈ S := by
  have hm (P : Polynomial ℚ) :
      algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        (lpsOriginalJHolomorphicEvalQ P) ∈ S := by
    rw [lpsOriginalJHolomorphicEvalQ_localization]
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ => rw [Polynomial.eval₂_add]; exact S.add_mem hP hQ
    | monomial n q =>
      rw [Polynomial.eval₂_monomial]
      exact S.mul_mem (by simpa only [eq_ratCast] using
        (SubfieldClass.ratCast_mem S q)) (S.pow_mem hj n)
  obtain ⟨A, B, _, hAB⟩ := IsFractionRing.div_surjective (Polynomial ℚ) a
  rw [←hAB, map_div₀, lpsOriginalJFractionEmbeddingQ_polynomial,
    lpsOriginalJFractionEmbeddingQ_polynomial]
  exact S.div_mem (hm A) (hm B)
lemma lpsOriginalGeneratedFunctionFieldQ_toSubfield_eq_closure (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield =
      Subfield.closure {lpsOriginalJInFractionField, lpsOriginalJNInFractionField N hN} := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  apply le_antisymm
  · intro x hx
    change x ∈ IntermediateField.adjoin (FractionRing (Polynomial ℚ))
      {lpsOriginalJNInFractionField N hN} at hx
    let S := Subfield.closure {lpsOriginalJInFractionField, lpsOriginalJNInFractionField N hN}
    have hj : lpsOriginalJInFractionField ∈ S := Subfield.subset_closure (by simp)
    refine IntermediateField.adjoin_induction (FractionRing (Polynomial ℚ))
      (fun y hy => ?_) (fun a => ?_)
      (fun y z _ _ hy hz => S.add_mem hy hz)
      (fun y _ hy => S.inv_mem hy)
      (fun y z _ _ hy hz => S.mul_mem hy hz) hx
    · have he := Set.mem_singleton_iff.mp hy
      subst y
      exact Subfield.subset_closure (by simp)
    · exact lpsOriginalJFractionEmbeddingQ_mem S hj a
  · apply Subfield.closure_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      have he : lpsOriginalJInFractionField = lpsOriginalJFractionEmbeddingQ
          (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X) := by
        rw [lpsOriginalJFractionEmbeddingQ_polynomial, lpsOriginalJHolomorphicEvalQ_localization]
        simp
      rw [he]
      exact IntermediateField.algebraMap_mem _ _
    · have he := Set.mem_singleton_iff.mp hx
      subst x
      exact IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
lemma lpsOriginalGeneratedFunctionFieldQ_fricke_map (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield.map
      (lpsOriginalPositiveFractionPullback (lpsOriginalFrickeMatrix N hN)
        (lpsOriginalFrickeMatrix_pos N hN)).toRingHom =
          (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  simp only [lpsOriginalGeneratedFunctionFieldQ_toSubfield_eq_closure, RingHom.map_field_closure,
    Set.image_insert_eq, Set.image_singleton, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, lpsOriginalPositiveFractionPullback_fricke_j,
    lpsOriginalPositiveFractionPullback_fricke_jN, Set.pair_comm]
lemma lpsOriginalDilation_product (N p : ℕ) (hN : 0 < N) (hp : 0 < p) (τ : ℍ) :
    lpsE2AffineMatrix N hN 0 • (lpsE2AffineMatrix p hp 0 • τ) =
      lpsE2AffineMatrix (N*p) (Nat.mul_pos hN hp) 0 • τ := by
  apply UpperHalfPlane.ext
  simp only [lpsOriginalJDilated_coe, Nat.cast_mul, mul_assoc]
def lpsOriginalDilationFractionPullback (p : ℕ) (hp : 0 < p) :
    LPSOriginalHolomorphicFractionField ≃+* LPSOriginalHolomorphicFractionField :=
  lpsOriginalPositiveFractionPullback (lpsE2AffineMatrix p hp 0)
    (by rw [lpsE2AffineMatrix_det]; exact_mod_cast hp)
lemma lpsOriginalDilationFractionPullback_j (p : ℕ) (hp : 0 < p) :
    lpsOriginalDilationFractionPullback p hp lpsOriginalJInFractionField =
      lpsOriginalJNInFractionField p hp := by
  rw [lpsOriginalDilationFractionPullback, lpsOriginalJInFractionField,
    lpsOriginalPositiveFractionPullback_localization]
  rfl
lemma lpsOriginalPositiveHolomorphicPullback_dilation_jN
    (N p : ℕ) (hN : 0 < N) (hp : 0 < p) :
    lpsOriginalPositiveHolomorphicPullback (lpsE2AffineMatrix p hp 0)
      (by rw [lpsE2AffineMatrix_det]; exact_mod_cast hp)
      (lpsOriginalJNHolomorphic N hN) =
        lpsOriginalJNHolomorphic (N*p) (Nat.mul_pos hN hp) := by
  apply Subtype.ext
  funext τ
  change lpsOriginalJInvariant (lpsE2AffineMatrix N hN 0 •
    (lpsE2AffineMatrix p hp 0 • τ)) =
      lpsOriginalJInvariant (lpsE2AffineMatrix (N*p) (Nat.mul_pos hN hp) 0 • τ)
  rw [lpsOriginalDilation_product]
lemma lpsOriginalDilationFractionPullback_jN
    (N p : ℕ) (hN : 0 < N) (hp : 0 < p) :
    lpsOriginalDilationFractionPullback p hp (lpsOriginalJNInFractionField N hN) =
      lpsOriginalJNInFractionField (N*p) (Nat.mul_pos hN hp) := by
  rw [lpsOriginalDilationFractionPullback, lpsOriginalJNInFractionField,
    lpsOriginalPositiveFractionPullback_localization,
    lpsOriginalPositiveHolomorphicPullback_dilation_jN]
  rfl
lemma lpsOriginalGeneratedFunctionFieldQ_dilation_image_eq_fricke
    (N p : ℕ) (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield.map
      (lpsOriginalDilationFractionPullback p hp).toRingHom =
    (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield.map
      (lpsOriginalPositiveFractionPullback
        (lpsOriginalFrickeMatrix (N*p) (Nat.mul_pos hN hp))
        (lpsOriginalFrickeMatrix_pos (N*p) (Nat.mul_pos hN hp))).toRingHom := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  simp only [lpsOriginalGeneratedFunctionFieldQ_toSubfield_eq_closure,
    RingHom.map_field_closure, Set.image_insert_eq, Set.image_singleton,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    lpsOriginalDilationFractionPullback_j, lpsOriginalDilationFractionPullback_jN,
    lpsOriginalPositiveFractionPullback_fricke_j,
    lpsOriginalPositiveFractionPullback_fricke_product_jN N p hN hp, Set.pair_comm]
lemma lpsOriginalGeneratedFunctionFieldQ_dilation_image_le
    (N p : ℕ) [NeZero N] [NeZero p] (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield.map
      (lpsOriginalDilationFractionPullback p hp).toRingHom ≤
        (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)).toSubfield := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield.map
    (lpsOriginalDilationFractionPullback p hp).toRingHom ≤
      (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)).toSubfield
  rw [lpsOriginalGeneratedFunctionFieldQ_dilation_image_eq_fricke]
  have hle := lpsOriginalGeneratedFunctionFieldQ_level_le N (N*p)
    (dvd_mul_right N p) h4N hN (Nat.mul_pos hN hp)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subfield.mem_map.mp hy
  have hm := Subfield.map_mem_map
    (lpsOriginalPositiveFractionPullback
      (lpsOriginalFrickeMatrix (N*p) (Nat.mul_pos hN hp))
      (lpsOriginalFrickeMatrix_pos (N*p) (Nat.mul_pos hN hp))).toRingHom
    (s := (lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp)).toSubfield)
    (x := x)
  rw [lpsOriginalGeneratedFunctionFieldQ_fricke_map] at hm
  exact hm.mpr (hle hx)
def lpsOriginalRationalHeckePullback (N p : ℕ) [NeZero N] [NeZero p]
    (hN : 0 < N) (hp : 0 < p) (h4N : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ N hN →+*
      lpsOriginalGeneratedFunctionFieldQ (N*p) (Nat.mul_pos hN hp) := by
  letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
  exact
    { toFun := fun x => ⟨lpsOriginalDilationFractionPullback p hp x,
        lpsOriginalGeneratedFunctionFieldQ_dilation_image_le N p hN hp h4N
          (Subfield.mem_map.mpr ⟨x, x.property, rfl⟩)⟩
      map_one' := Subtype.ext (map_one (lpsOriginalDilationFractionPullback p hp))
      map_mul' := fun x y => Subtype.ext (map_mul (lpsOriginalDilationFractionPullback p hp)
        (x : LPSOriginalHolomorphicFractionField) (y : LPSOriginalHolomorphicFractionField))
      map_zero' := Subtype.ext (map_zero (lpsOriginalDilationFractionPullback p hp))
      map_add' := fun x y => Subtype.ext (map_add (lpsOriginalDilationFractionPullback p hp)
        (x : LPSOriginalHolomorphicFractionField) (y : LPSOriginalHolomorphicFractionField)) }
lemma lpsOriginalJInFractionField_mem_generatedQ (N : ℕ) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalJInFractionField ∈ lpsOriginalGeneratedFunctionFieldQ N hN := by
  let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  change lpsOriginalJInFractionField ∈ (lpsOriginalGeneratedFunctionFieldQ N hN).toSubfield
  rw [lpsOriginalGeneratedFunctionFieldQ_toSubfield_eq_closure]
  exact Subfield.subset_closure (by simp)
end
end QEC.Coding.TannerLiftedProduct


