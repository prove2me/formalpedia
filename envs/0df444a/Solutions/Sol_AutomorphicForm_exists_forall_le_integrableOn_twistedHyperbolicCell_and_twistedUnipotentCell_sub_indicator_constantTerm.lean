-- Prove2me | solution 1 for AutomorphicForm.exists_forall_le_integrableOn_twistedHyperbolicCell_and_twistedUnipotentCell_sub_indicator_constantTerm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6c206314-4f27-5708-bfdc-432393703fdb

import Theorems.Thm_AutomorphicForm_exists_forall_norm_finsum_sub_indicator_highSet_constantTerm_finsum_borel_le_of_subset_centreCutSiegelSet_translates
import Theorems.Thm_AutomorphicForm_integrable_mul_finsum_sub_indicator_highSet_constantTerm_finsum_prod_of_forall_norm_le
import Theorems.Thm_AutomorphicForm_integrableOn_mul_finsum_sub_indicator_highSet_constantTerm_finsum_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_exists_forall_le_integrableOn_setIntegral_mul_finsum_unipotentNormClass_sub_indicator_constantTerm_canonicalTruncationDomain
import Theorems.Thm_LT_TwistedNorm_exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_le_integrableOn_twistedHyperbolicCell_and_twistedUnipotentCell_sub_indicator_constantTerm
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply ContinuousAddEquiv.preimage_mulLeft_smul M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk AutomorphicForm.mem_inducedSectionSubmodule_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace R1IntCellsL

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHeight NumberField.TateGlobal IsDedekindDomain
p2m_open "AutomorphicForm~ideleNorm_det_sigmaAdelicAct AutomorphicForm.WindowedSiegel Filter Function Set"
open scoped Topology ENNReal NNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

section Modulus

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

def actEquiv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) :
    AdeleRing (𝓞 L) L ≃ₜ+ AdeleRing (𝓞 L) L :=
  { ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv with
    continuous_toFun := D.continuous_act σ
    continuous_invFun := by
      have h : Continuous (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := D.continuous_act σ⁻¹
      have heq : (((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm :
          AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) = (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := by
        funext a
        rw [map_inv]
        rfl
      show Continuous ((((D.act σ : RingAut (AdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L).toAddEquiv.symm))
      rw [heq]; exact h }

theorem actEquiv_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L) :
    actEquiv K L D σ a = (D.act σ : RingAut (AdeleRing (𝓞 L) L)) a := rfl

theorem ideleNorm_unitsMap_act (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    ideleNorm L (Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _) z) =
      ideleNorm L z := by
  classical
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := ⟨rfl⟩
  set θ := actEquiv K L D σ with hθ
  set μ : Measure (AdeleRing (𝓞 L) L) := Measure.addHaar with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  set ν : Measure (AdeleRing (𝓞 L) L) := Measure.map θ.symm μ with hν
  haveI hνH : ν.IsAddHaarMeasure := θ.symm.isAddHaarMeasure_map μ
  haveI : μ.Regular := by rw [hμ]; infer_instance
  haveI : ν.Regular := Measure.Regular.map θ.symm.toHomeomorph
  obtain ⟨s, hs_compact, hs_mem⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 L) L)
  have hs0 : μ s ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hs_mem).ne'
  have hstop : μ s ≠ ⊤ := hs_compact.measure_lt_top.ne
  set w : (AdeleRing (𝓞 L) L)ˣ := Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
    AdeleRing (𝓞 L) L →* _) z with hw
  have hθsymm : ∀ b, (D.act σ : RingAut (AdeleRing (𝓞 L) L)) (θ.symm b) = b := fun b => θ.apply_symm_apply b
  have hset : (w • s : Set (AdeleRing (𝓞 L) L)) = θ '' (z • (θ.symm '' s)) := by
    ext a
    simp only [Set.mem_smul_set, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨(z : AdeleRing (𝓞 L) L) * θ.symm b, ⟨θ.symm b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
      rw [actEquiv_apply, map_mul, hθsymm, Units.smul_def, smul_eq_mul]
      rfl
    · rintro ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
      refine ⟨b, hb, ?_⟩
      rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, actEquiv_apply, map_mul, hθsymm]
      rfl
  have himg : ∀ B : Set (AdeleRing (𝓞 L) L), μ (θ '' B) = ν B := by
    intro B
    have hmap : ν B = μ (θ.symm ⁻¹' B) := (θ.symm.toHomeomorph.measurableEmbedding).map_apply μ B
    rw [hmap]
    congr 1
    ext a
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rwa [θ.symm_apply_apply]
    · intro ha
      exact ⟨θ.symm a, ha, θ.apply_symm_apply a⟩
  have himg' : θ '' (θ.symm '' s) = s := by
    rw [← Set.image_comp]
    convert Set.image_id s <;> first | rfl | (funext a; exact θ.apply_symm_apply a) | exact θ.apply_symm_apply _
  have h1 := distribHaarChar_mul μ w s
  have h2 := distribHaarChar_mul ν z (θ.symm '' s)
  rw [hset, himg, ← h2, ← himg, himg'] at h1
  have hcancel : distribHaarChar (AdeleRing (𝓞 L) L) w = distribHaarChar (AdeleRing (𝓞 L) L) z := by
    have := congrArg (fun t => t / μ s) h1
    beta_reduce at this
    rwa [ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.mul_div_cancel_right hs0 hstop, ENNReal.coe_inj] at this
  unfold NumberField.TateGlobal.ideleNorm
  rw [hw] at hcancel
  exact_mod_cast congrArg (fun t : ℝ≥0 => (t : ℝ)) hcancel

theorem ideleNorm_det_sigmaAdelicAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AdelicGL2 (𝓞 L) L) :
    ideleNorm L (Matrix.GeneralLinearGroup.det (sigmaAdelicAct K L D σ g)) =
      ideleNorm L (Matrix.GeneralLinearGroup.det g) := by
  unfold sigmaAdelicAct
  rw [Matrix.GeneralLinearGroup.map_det]
  exact ideleNorm_unitsMap_act K L D σ _

end Modulus

section Cells

open Polynomial Matrix

variable {F : Type*} [Field F]

theorem diag_ne_zero (γ : GL (Fin 2) F) (h10 : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (γ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 ∧ (γ : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
  have hdet : (γ : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det γ).ne_zero
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

theorem charpoly_upper (γ : GL (Fin 2) F) (h10 : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (γ : Matrix (Fin 2) (Fin 2) F).charpoly =
      (X - C ((γ : Matrix (Fin 2) (Fin 2) F) 0 0)) * (X - C ((γ : Matrix (Fin 2) (Fin 2) F) 1 1)) := by
  rw [Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two, h10, mul_zero, sub_zero, map_add,
    map_mul]
  ring

theorem eq_of_mul_eq_sq {a b e : F} (h : (X - C a) * (X - C b) = (X - C e) * (X - C e)) : a = e ∧ b = e := by
  have ha := congrArg (Polynomial.eval a) h
  have hb := congrArg (Polynomial.eval b) h
  simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, mul_zero] at ha hb
  exact ⟨sub_eq_zero.mp (mul_self_eq_zero.mp ha.symm), sub_eq_zero.mp (mul_self_eq_zero.mp hb.symm)⟩

theorem trace_det_of_charpoly_eq (M : Matrix (Fin 2) (Fin 2) F) (r₁ r₂ : F)
    (h : M.charpoly = (X - C r₁) * (X - C r₂)) : M.trace = r₁ + r₂ ∧ M.det = r₁ * r₂ := by
  have key : (X ^ 2 - C M.trace * X + C M.det : F[X]) = X ^ 2 - C (r₁ + r₂) * X + C (r₁ * r₂) := by
    rw [← Matrix.charpoly_fin_two, h, map_add, map_mul]; ring
  have h1 := congrArg (fun p : F[X] => p.coeff 1) key
  have h0 := congrArg (fun p : F[X] => p.coeff 0) key
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_one, coeff_C_zero, coeff_C_succ,
    coeff_X_zero, mul_one, mul_zero] at h1 h0
  norm_num at h1 h0
  refine ⟨?_, h0⟩
  have := neg_inj.mpr h1
  simp only [neg_neg, neg_add, add_comm] at this ⊢
  exact this

theorem charpoly_smul_of_eq (M : Matrix (Fin 2) (Fin 2) F) (a r₁ r₂ : F)
    (h : M.charpoly = (X - C r₁) * (X - C r₂)) :
    (a • M).charpoly = (X - C (a * r₁)) * (X - C (a * r₂)) := by
  obtain ⟨htr, hdet⟩ := trace_det_of_charpoly_eq M r₁ r₂ h
  rw [Matrix.charpoly_fin_two, Matrix.trace_smul, Matrix.det_smul, htr, hdet, Fintype.card_fin, smul_eq_mul]
  simp only [map_add, map_mul, map_pow]
  ring

theorem coe_mul_scalar (γ : GL (Fin 2) F) (a : Fˣ) :
    ((γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (a : F) • (γ : Matrix (Fin 2) (Fin 2) F) := by
  rw [Units.val_mul]
  change (γ : Matrix (Fin 2) (Fin 2) F) * Matrix.scalar (Fin 2) (a : F) = _
  rw [Matrix.scalar_apply, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

theorem isCentralType_smul_iff {M : Matrix (Fin 2) (Fin 2) F} {a : F} (ha : a ≠ 0) :
    IsCentralType (a • M) ↔ IsCentralType M := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨a⁻¹ * c, ?_⟩
    have : M = a⁻¹ • (a • M) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [this, hc, smul_smul]
  · rintro ⟨c, hc⟩
    exact ⟨a * c, by rw [hc, smul_smul]⟩

theorem mul_scalar_mem_hyperbolicCell (γ : GL (Fin 2) F) (hγ : γ ∈ hyperbolicCell F) (a : Fˣ) :
    γ * Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ hyperbolicCell F := by
  obtain ⟨r₁, r₂, hne, hp⟩ := hγ
  refine ⟨a * r₁, a * r₂, fun h => hne (mul_left_cancel₀ a.ne_zero h), ?_⟩
  rw [coe_mul_scalar]
  exact charpoly_smul_of_eq _ _ _ _ hp

end Cells

section Twisted

open Polynomial Matrix LT.TwistedNorm

variable {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

theorem sigmaPartialNorm_mul_of_forall_commute {G : Type*} [Group G] (σ : G →* G) (x c : G)
    (hc : ∀ (r : ℕ) (g : G), Commute ((⇑σ)^[r] c) g) (r : ℕ) :
    sigmaPartialNorm σ (x * c) r = sigmaPartialNorm σ x r * sigmaPartialNorm σ c r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sigmaPartialNorm_succ', sigmaPartialNorm_succ', sigmaPartialNorm_succ', ih, map_mul]

      have h1 : c * σ (sigmaPartialNorm σ x r) = σ (sigmaPartialNorm σ x r) * c := (hc 0 _).eq
      calc x * c * (σ (sigmaPartialNorm σ x r) * σ (sigmaPartialNorm σ c r))
          = x * (c * σ (sigmaPartialNorm σ x r)) * σ (sigmaPartialNorm σ c r) := by group
        _ = x * (σ (sigmaPartialNorm σ x r) * c) * σ (sigmaPartialNorm σ c r) := by rw [h1]
        _ = x * σ (sigmaPartialNorm σ x r) * (c * σ (sigmaPartialNorm σ c r)) := by group

private theorem _root_.R1IntCellsL.scalar_commute (a : Lˣ) (g : GL (Fin 2) L) : Commute (Matrix.GeneralLinearGroup.scalar (Fin 2) a) g := by
  rw [Commute, SemiconjBy]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (n := Fin 2) (a : L) (fun r' => Commute.all _ r') _).eq

p2m_export "R1IntCellsL" "scalar_commute"
theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : Rˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) a) := by
  refine Units.ext ?_
  change ((Matrix.scalar (Fin 2) (a : R)).map f : Matrix (Fin 2) (Fin 2) S) =
    Matrix.scalar (Fin 2) (f (a : R))
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero f)]

theorem iterate_map_scalar (σ : L →+* L) (r : ℕ) (a : Lˣ) :
    (⇑(Matrix.GeneralLinearGroup.map (n := Fin 2) σ))^[r] (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) ((⇑(Units.map (σ : L →* L)))^[r] a) := by
  induction r with
  | zero => rfl
  | succ r ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_scalar]

theorem sigmaNormPow_mul_scalar {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) (a : Lˣ) (ha : Algebra.norm F (a : L) ≠ 0) :
    sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L)
        (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ *
        Matrix.GeneralLinearGroup.map (algebraMap F L)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 _ ha)) := by
  rw [sigmaNormPow_def, sigmaNormPow_def,
    sigmaPartialNorm_mul_of_forall_commute _ _ _ (fun r g => by rw [iterate_map_scalar]; exact scalar_commute _ _)]
  congr 1
  rw [← sigmaNormPow_def, ← hom_sigmaNormPow (Units.map ((σ : L →+* L) : L →* L))
    (Matrix.GeneralLinearGroup.map (n := Fin 2) (σ : L →+* L)) (Matrix.GeneralLinearGroup.scalar (Fin 2))
    (fun x => (map_scalar (σ : L →+* L) x).symm), map_scalar]
  congr 1
  refine Units.ext ?_
  rw [coe_sigmaNormPow_units_eq_algebraMap_norm hgen a]
  rfl

theorem charpoly_conj (c γ : GL (Fin 2) F) :
    ((c * γ * c⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).charpoly =
      ((γ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj c _

theorem mem_hyperbolicCell_of_isConj {δ γ : GL (Fin 2) F} (h : IsConj δ γ) (hγ : γ ∈ hyperbolicCell F) :
    δ ∈ hyperbolicCell F := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  obtain ⟨a, b, hab, hp⟩ := hγ
  refine ⟨a, b, hab, ?_⟩
  rw [← charpoly_conj c δ, hc]
  exact hp

theorem mul_scalar_mem_hyperbolicNormClass {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (hcell : ∀ (γ : GL (Fin 2) F), γ ∈ hyperbolicCell F → ∀ b : Fˣ, γ * Matrix.GeneralLinearGroup.scalar (Fin 2) b ∈ hyperbolicCell F)
    (δ : GL (Fin 2) L)
    (hδ : ∃ γ : GL (Fin 2) F, γ ∈ hyperbolicCell F ∧ normClassMap hgen (SigmaConjClasses.mk σ δ) = ConjClasses.mk γ)
    (a : Lˣ) :
    ∃ γ : GL (Fin 2) F, γ ∈ hyperbolicCell F ∧
      normClassMap hgen (SigmaConjClasses.mk σ (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) a)) = ConjClasses.mk γ := by
  obtain ⟨γ, hγ, hN⟩ := hδ
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj] at hN
  set γ' := normRep hgen δ with hγ'
  have hγ'h : γ' ∈ hyperbolicCell F := mem_hyperbolicCell_of_isConj hN hγ
  obtain ⟨P, hP⟩ := isNormRep_normRep hgen δ
  have ha : Algebra.norm F (a : L) ≠ 0 := Algebra.norm_ne_zero_iff.mpr a.ne_zero
  set b : Fˣ := Units.mk0 _ ha with hb
  refine ⟨γ' * Matrix.GeneralLinearGroup.scalar (Fin 2) b, hcell γ' hγ'h b, ?_⟩
  refine normClassMap_mk_eq_of_isNormRep hgen ⟨P, ?_⟩
  rw [sigmaNormPow_mul_scalar hgen δ a ha, map_mul, ← hP, map_scalar]
  have hcomm := (scalar_commute (Units.map (algebraMap F L : F →* L) b) P).eq
  simp only [mul_assoc]
  rw [hcomm]

end Twisted

section Slab

variable (L : Type) [Field L] [NumberField L]

theorem nullMeasurableSet_of_restrict {α : Type*} [MeasurableSpace α] (μ : Measure α) {s t : Set α}
    (ht : MeasurableSet t) (hst : s ⊆ t) (h : NullMeasurableSet s (μ.restrict t)) : NullMeasurableSet s μ := by
  obtain ⟨s', hs'm, hs'⟩ := h
  refine ⟨s' ∩ t, hs'm.inter ht, ?_⟩
  have h2 : ∀ᵐ x ∂μ, x ∈ t → (x ∈ s) = (x ∈ s') := (ae_restrict_iff' ht).mp hs'
  filter_upwards [h2] with x hx
  by_cases hxt : x ∈ t
  · have := hx hxt
    show (x ∈ s) = (x ∈ s' ∩ t)
    rw [this]; simp [hxt]
  · have hxs : x ∉ s := fun h => hxt (hst h)
    show (x ∈ s) = (x ∈ s' ∩ t)
    simp [hxs, hxt]

def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 L) L) :=
  {g | ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem measurableSet_slab (α β : ℝ) : MeasurableSet (slab L α β) :=
  measurableSet_preimage (NumberField.TateGlobal.continuous_ideleNorm_det L).measurable measurableSet_Icc

theorem nullMeasurableSet_and_measure_lt_top_of_isFundamentalDomain_slab {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    {Φ : Set (AdelicGL2 (𝓞 L) L)} (hΦs : Φ ⊆ slab L α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β))) :
    NullMeasurableSet Φ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧ adelicGLHaar (Fin 2) (𝓞 L) L Φ < ⊤ := by
  refine ⟨nullMeasurableSet_of_restrict _ (measurableSet_slab L α β) hΦs hΦ.nullMeasurableSet, ?_⟩
  have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
    L α β hα hαβ Φ hΦ
  rwa [Set.inter_eq_self_of_subset_left (show Φ ⊆ {g | ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈
    Set.Icc α β} from hΦs)] at h

end Slab

section Main

theorem exp_ge_of_log_max_le {T₀ R : ℝ} (hR : Real.log (max T₀ 1) ≤ R) : T₀ ≤ Real.exp R := by
  have h1 : (0 : ℝ) < max T₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  calc T₀ ≤ max T₀ 1 := le_max_left _ _
    _ = Real.exp (Real.log (max T₀ 1)) := (Real.exp_log h1).symm
    _ ≤ Real.exp R := Real.exp_le_exp.mpr hR

theorem mainL
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφf : IsFactorizableTestFn L φ) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x))) -
        Set.indicator (highSet (adelicHeight L) (Real.exp R))
        (@constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ y)))
        (centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x))) -
        Set.indicator (highSet (adelicHeight L) (Real.exp R))
        (@constantTerm _ (adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ y)))
        (centralScalar (𝓞 L) L z * x)) ∂νZL))
        (canonicalTruncationDomain L α β) (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x))) -
        Set.indicator (highSet (adelicHeight L) (Real.exp R))
        (@constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ y)))
        (centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x))) -
        Set.indicator (highSet (adelicHeight L) (Real.exp R))
        (@constantTerm _ (adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ y)))
        (centralScalar (𝓞 L) L z * x)) ∂νZL))
        (canonicalTruncationDomain L α β) (adelicGLHaar (Fin 2) (𝓞 L) L) := by
  classical

  obtain ⟨hc, hTc, hcov, hslab, hfd⟩ := canonicalTruncationData_isTruncationDatum L α β hα hαβ
  obtain ⟨hΦm, hΦμ⟩ := nullMeasurableSet_and_measure_lt_top_of_isFundamentalDomain_slab L hα hαβ hslab hfd

  obtain ⟨T₀, hT₀⟩ :=
    AutomorphicForm.exists_forall_norm_finsum_sub_indicator_highSet_constantTerm_finsum_borel_le_of_subset_centreCutSiegelSet_translates
      K L D σ _ _ _ _ hc _ hTc _ hcov φ hφf

  obtain ⟨R_U, hR_U⟩ :=
    AutomorphicForm.exists_forall_le_integrableOn_setIntegral_mul_finsum_unipotentNormClass_sub_indicator_constantTerm_canonicalTruncationDomain
      K L α β hα hαβ νZL ΩL hΩL D σ hgen ξL hξc hξt φ hφf
  refine ⟨max (Real.log (max T₀ 1)) R_U, fun R hR => ?_⟩
  have hR1 : Real.log (max T₀ 1) ≤ R := (le_max_left _ _).trans hR
  have hR2 : R_U ≤ R := (le_max_right _ _).trans hR
  obtain ⟨C, hC⟩ := hT₀ (Real.exp R) (exp_ge_of_log_max_le hR1)

  have hH : ∀ x ∈ canonicalTruncationDomain L α β, ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
          φ (x⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x))) -
          Set.indicator (highSet (adelicHeight L) (Real.exp R))
            (constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L))
              (fun t => unipotentGL2 t)
              (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) L |
                  (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈
                      {r : L | Algebra.norm K r ≠ 1}},
                φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ y)))
            (centralScalar (𝓞 L) L z * x)‖ ≤ C :=
    hC {r : L | Algebra.norm K r ≠ 1} _
      (fun δ hδ a => mul_scalar_mem_hyperbolicNormClass hgen
        (fun γ hγ b => mul_scalar_mem_hyperbolicCell γ hγ b) δ hδ a)
      (fun δ h10 => LT.TwistedNorm.exists_mem_hyperbolicCell_and_normClassMap_eq_iff_norm_div_ne_one hgen δ h10)
  have hHint :=
    AutomorphicForm.integrable_mul_finsum_sub_indicator_highSet_constantTerm_finsum_prod_of_forall_norm_le
      L (sigmaAdelicAct K L D σ) (continuous_sigmaAdelicAct K L D σ) (ideleNorm_det_sigmaAdelicAct K L D σ)
      _ hΦμ hΦm νZL ΩL hΩL ξL hξc hξt φ hφ hφc
      {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ}
      {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
        (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ {r : L | Algebra.norm K r ≠ 1}}
      (Real.exp R) C hH

  have hHi : ∀ x : AdelicGL2 (𝓞 L) L, _ := fun x =>
    AutomorphicForm.integrableOn_mul_finsum_sub_indicator_highSet_constantTerm_finsum_of_hasCompactSupport
      K L ΦL νZL ΩL hΩL D σ ξL hξc hξt φ hφ hφc
      {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ}
      {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
        Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1} R x
  have hUi : ∀ x : AdelicGL2 (𝓞 L) L, _ := fun x =>
    AutomorphicForm.integrableOn_mul_finsum_sub_indicator_highSet_constantTerm_finsum_of_hasCompactSupport
      K L ΦL νZL ΩL hΩL D σ ξL hξc hξt φ hφ hφc
      {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ unipotentCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ}
      {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
        Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1} R x
  exact ⟨hHi, hHint.2, hUi, hR_U R hR2⟩

end Main

end R1IntCellsL

end

section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option linter.unusedVariables false in
p2m_open "AutomorphicForm~ideleNorm_det_sigmaAdelicAct" in
open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (hfac : IsSemiLocalFactorization K L S φ φa φf φS) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        (AutomorphicForm.canonicalTruncationDomain L α β) (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        (AutomorphicForm.canonicalTruncationDomain L α β) (adelicGLHaar (Fin 2) (𝓞 L) L) := by
  have hφfac : AutomorphicForm.IsFactorizableTestFn L φ := ⟨φa, φf, hfac.1, hfac.2.1, hfac.2.2.2.2.2⟩
  exact R1IntCellsL.mainL K L α β hα hαβ ΦL νZL ΩL hΩL D σ hgen ξL hξc hξt φ hφ hφc hφfac

end

end S_AutomorphicForm_exists_forall_le_integrableOn_twistedHyperbolicCell_and_twistedUnipotentCell_sub_indicator_constantTerm
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_le_integrableOn_twistedHyperbolicCell_and_twistedUnipotentCell_sub_indicator_constantTerm (solution)
