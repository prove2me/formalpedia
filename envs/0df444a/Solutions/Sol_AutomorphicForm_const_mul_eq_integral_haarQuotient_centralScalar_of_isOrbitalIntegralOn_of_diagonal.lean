-- Prove2me | solution 1 for AutomorphicForm.const_mul_eq_integral_haarQuotient_centralScalar_of_isOrbitalIntegralOn_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f39b44e0-4360-529e-a2ef-d6c334bf3673

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
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_exists_mem_mul_of_inv_mul_globalPoints_mul_sigmaAdelicAct_centralScalar_mul_mem_of_diagonal
import Theorems.Thm_MeasureTheory_exists_nonneg_hasCompactSupport_forall_integral_subgroup_translate_eq_one_of_isCompact
import Theorems.Thm_MeasureTheory_integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
import Theorems.Thm_HaarQuotient_integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdelicHeight_neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_diagonal_mul_and_continuous
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_const_mul_eq_integral_haarQuotient_centralScalar_of_isOrbitalIntegralOn_of_diagonal
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace OQAux

open AutomorphicForm

section Algebra
variable {A : Type*} [CommRing A]

theorem mem_centralizer_diag_iff (γ : GL (Fin 2) A) (d₁ d₂ : A)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) A) = !![d₁, 0; 0, d₂]) (hreg : IsUnit (d₁ - d₂)) (h : GL (Fin 2) A) :
    h ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) ↔
      ((h : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 ∧ (h : Matrix (Fin 2) (Fin 2) A) 0 1 = 0) := by
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro hc
    have hm : (γ : Matrix (Fin 2) (Fin 2) A) * h = h * γ := by
      rw [← Units.val_mul, hc, Units.val_mul]
    rw [hγ] at hm
    have e10 := congrFun (congrFun hm 1) 0
    have e01 := congrFun (congrFun hm 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e10 e01
    obtain ⟨u, hu⟩ := hreg
    constructor
    · have : (d₁ - d₂) * (h : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := by rw [sub_mul]; linear_combination (-1 : A) * e10
      rw [← hu] at this
      simpa using (Units.mul_right_eq_zero u).mp this
    · have : (d₁ - d₂) * (h : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := by rw [sub_mul]; linear_combination e01
      rw [← hu] at this
      simpa using (Units.mul_right_eq_zero u).mp this
  · rintro ⟨h10, h01⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hγ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h01, mul_comm]

end Algebra

variable (K : Type) [Field K] [NumberField K]

theorem mem_centralizer_globalPoints_iff (γ : GL (Fin 2) K)
    (h10 : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h01 : (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (hreg : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (h : AdelicGL2 (𝓞 K) K) :
    h ∈ Subgroup.centralizer ({globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)) ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧ (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0) := by
  have hne : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 - (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
    intro h0
    have h11 : (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
      intro hz
      have hdet : (γ : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det γ).ne_zero
      rw [Matrix.det_fin_two, hz, h10] at hdet
      simp at hdet
    exact hreg (by rw [sub_eq_zero.mp h0, div_self h11])
  refine mem_centralizer_diag_iff _ (algebraMap K (AdeleRing (𝓞 K) K) ((γ : Matrix (Fin 2) (Fin 2) K) 0 0))
    (algebraMap K (AdeleRing (𝓞 K) K) ((γ : Matrix (Fin 2) (Fin 2) K) 1 1)) ?_ ?_ h
  · show (γ : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (AdeleRing (𝓞 K) K)) = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h01]
  · rw [← map_sub]
    exact (IsUnit.mk0 _ hne).map _

theorem centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    centralScalar (𝓞 K) K z * g = g * centralScalar (𝓞 K) K z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [centralScalar, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem centralScalar_mul_diagUnits2_one (z a : (AdeleRing (𝓞 K) K)ˣ) :
    centralScalar (𝓞 K) K z * diagUnits2 a 1 = diagUnits2 (z * a) z := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [centralScalar, diagUnits2, Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]

theorem integral_centralScalar_mul_diagUnits2_eq
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsHaarMeasure]
    (g : AdelicGL2 (𝓞 K) K → ℂ) :
    ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (centralScalar (𝓞 K) K p.1 * diagUnits2 p.2 1) ∂(ν.prod ν) =
      ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(ν.prod ν) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  simp_rw [centralScalar_mul_diagUnits2_one]
  let e : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ ≃ᵐ (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ :=
    (MeasurableEquiv.shearMulRight _).trans MeasurableEquiv.prodComm
  have he : (⇑e) = fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ => (p.1 * p.2, p.1) := by
    funext p
    simp [e, MeasurableEquiv.trans_apply, MeasurableEquiv.shearMulRight, MeasurableEquiv.prodComm]
  have hmp : MeasurePreserving (fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ => (p.1 * p.2, p.1))
      (ν.prod ν) (ν.prod ν) :=
    (Measure.measurePreserving_swap (μ := ν) (ν := ν)).comp (measurePreserving_prod_mul ν ν)
  have hφ : MeasurableEmbedding (fun p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ => (p.1 * p.2, p.1)) := by
    have := e.measurableEmbedding; rwa [he] at this
  exact hmp.integral_comp hφ (fun p => g (diagUnits2 p.1 p.2))

end OQAux

namespace OQAux
open AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

theorem t2Space_adelicGL2 : T2Space (AdelicGL2 (𝓞 K) K) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  exact Units.isEmbedding_embedProduct.t2Space

theorem locallyCompactSpace_adelicGL2 : LocallyCompactSpace (AdelicGL2 (𝓞 K) K) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance subsingleton_algEquiv_self : Subsingleton (K ≃ₐ[K] K) :=
  ⟨fun a b => AlgEquiv.ext fun x => (a.commutes x).trans (b.commutes x).symm⟩

theorem exists_isCompact_forall_exists_mem_mul
    (HK : Subgroup (AdelicGL2 (𝓞 K) K))
    (hHK : ∀ h : AdelicGL2 (𝓞 K) K, h ∈ HK ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0))
    (γ : GL (Fin 2) K) (h10 : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h01 : (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (hreg : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (C : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) :
    ∃ C' : Set (AdelicGL2 (𝓞 K) K), IsCompact C' ∧
      ∀ (y : AdelicGL2 (𝓞 K) K) (z : (AdeleRing (𝓞 K) K)ˣ),
        y⁻¹ * globalPoints (𝓞 K) K γ * (centralScalar (𝓞 K) K z * y) ∈ C →
          ∃ h k : AdelicGL2 (𝓞 K) K, h ∈ HK ∧ k ∈ C' ∧ y = h * k := by
  let DK := M4aHerbrand.identityDescent (𝓞 K) K K
  have hgen : ∀ τ : K ≃ₐ[K] K, τ ∈ Subgroup.zpowers (1 : K ≃ₐ[K] K) := fun τ => by
    rw [Subsingleton.elim τ 1]; exact Subgroup.mem_zpowers _
  have hHK' : ∀ h : AdelicGL2 (𝓞 K) K, h ∈ HK ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0 ∧
       sigmaAdelicAct K K DK 1 h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 K) K)) := by
    intro h
    rw [hHK, sigmaAdelicAct_one, MonoidHom.id_apply, mul_inv_cancel]
    exact ⟨fun hh => ⟨hh.1, hh.2, Subgroup.one_mem _⟩, fun hh => ⟨hh.1, hh.2.1⟩⟩
  have hreg' : Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 1 := by
    have hn : ∀ t : K, Algebra.norm K t = t := fun t => by
      rw [Algebra.norm_self]; rfl
    rwa [hn]
  obtain ⟨C', hC'c, hC'⟩ :=
    exists_isCompact_forall_exists_mem_mul_of_inv_mul_globalPoints_mul_sigmaAdelicAct_centralScalar_mul_mem_of_diagonal
      K K 1 hgen DK HK hHK' γ h10 h01 hreg' C hC
  refine ⟨C', hC'c, fun y z hy => hC' y z ?_⟩
  rwa [sigmaAdelicAct_one, MonoidHom.id_apply]

end OQAux
p2m_reactivate "P2MW.S_AutomorphicForm_const_mul_eq_integral_haarQuotient_centralScalar_of_isOrbitalIntegralOn_of_diagonal.OQAux"

open AutomorphicForm OQAux in
theorem plain_part
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νZK.IsHaarMeasure]

    (HK : Subgroup (AdelicGL2 (𝓞 K) K)) (hHKc : IsClosed (HK : Set (AdelicGL2 (𝓞 K) K)))
    (hHK : ∀ h : AdelicGL2 (𝓞 K) K, h ∈ HK ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0))
    (μHK : Measure HK) [μHK.IsHaarMeasure] [μHK.IsMulRightInvariant]
    (cHK : ℝ) (hcHK : 0 < cHK)
    (hHKμ : ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ h : HK, g (h : AdelicGL2 (𝓞 K) K) ∂μHK =
        cHK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.centralScalar (𝓞 K) K p.1 * diagUnits2 p.2 1) ∂(νZK.prod νZK))
    (cτK : ℝ) (hcτK : 0 < cτK)
    (γ : GL (Fin 2) K) (h10 : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h01 : (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (hreg : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (τ : @Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)))
        (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) (AutomorphicForm.globalPoints (𝓞 K) K γ)))
    (hτ : @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) (AutomorphicForm.globalPoints (𝓞 K) K γ)) τ)
    (hτc : ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
        ∫ s : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)),
            g (s : AdelicGL2 (𝓞 K) K) ∂τ =
          cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (z : (AdeleRing (𝓞 K) K)ˣ) (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ) τ
          (fun g : AdelicGL2 (𝓞 K) K => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) I) :
    ((cτK / cHK : ℝ) : ℂ) * I =
        ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K),
              f (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K))))
            ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK) := by
  classical

  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : T2Space (AdelicGL2 (𝓞 K) K) := t2Space_adelicGL2 K
  haveI : LocallyCompactSpace (AdelicGL2 (𝓞 K) K) := locallyCompactSpace_adelicGL2 K
  haveI hμG : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SigmaCompactSpace (AdelicGL2 (𝓞 K) K) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 K) K) := Measure.IsHaarMeasure.sigmaFinite _
  haveI : SFinite (adelicGLHaar (Fin 2) (𝓞 K) K) := instSFiniteOfSigmaFinite

  have hTmem : ∀ h : AdelicGL2 (𝓞 K) K, h ∈ Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)) ↔ h ∈ HK := by
    intro h; rw [mem_centralizer_globalPoints_iff K γ h10 h01 hreg, hHK]
  have hTHK : Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)) = HK := Subgroup.ext hTmem
  have hTc : IsClosed ((Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)) : Subgroup (AdelicGL2 (𝓞 K) K)) :
      Set (AdelicGL2 (𝓞 K) K)) := by rw [hTHK]; exact hHKc
  haveI : BorelSpace (Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) := ⟨rfl⟩
  haveI hτi : τ.IsHaarMeasure := hτ
  have hcomm : ∀ s t : Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)), s * t = t * s := by
    intro s t
    apply Subtype.ext
    have hs := (hTmem s).mp s.2
    have ht := (hTmem t).mp t.2
    rw [hHK] at hs ht
    show (s : AdelicGL2 (𝓞 K) K) * t = t * s
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hs.1, hs.2, ht.1, ht.2, mul_comm]
  haveI : τ.IsMulRightInvariant := ⟨fun g => by
    have : (fun h : Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)) => h * g) = fun h => g * h :=
      funext fun h => hcomm h g
    rw [this]; exact map_mul_left_eq_self τ g⟩
  haveI : τ.IsInvInvariant := by
    letI : CommGroup (Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) := { mul_comm := hcomm }
    haveI : LocallyCompactSpace (Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) := hTc.locallyCompactSpace
    haveI : SecondCountableTopology (Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) :=
      Topology.IsEmbedding.subtypeVal.secondCountableTopology
    haveI : SigmaCompactSpace (Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) :=
      sigmaCompactSpace_of_locallyCompact_secondCountable
    exact Measure.IsHaarMeasure.isInvInvariant_of_innerRegular τ

  set F : AdelicGL2 (𝓞 K) K → ℂ := fun g => f (AutomorphicForm.centralScalar (𝓞 K) K z * g) with hF
  have hFc : Continuous F := hf.comp (continuous_const.mul continuous_id)
  have hFs : HasCompactSupport F := hfc.comp_homeomorph (Homeomorph.mulLeft (AutomorphicForm.centralScalar (𝓞 K) K z))
  obtain ⟨Cf, hCf⟩ := hf.bounded_above_of_compact_support hfc
  have hconjc : Continuous fun x : AdelicGL2 (𝓞 K) K => x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x :=
    (continuous_id.inv.mul continuous_const).mul continuous_id
  have hFconj : ∀ x : AdelicGL2 (𝓞 K) K, F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) = f (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * (AutomorphicForm.centralScalar (𝓞 K) K z * x)) := by
    intro x
    simp only [hF]
    rw [centralScalar_comm K z (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x), mul_assoc, mul_assoc, ← centralScalar_comm K z x, ← mul_assoc]

  obtain ⟨C', hC'c, hC'⟩ := exists_isCompact_forall_exists_mem_mul K HK hHK γ h10 h01 hreg (tsupport f) hfc
  obtain ⟨W, hW0, hWm, hWs, ⟨B, hWB⟩, hW1⟩ :=
    MeasureTheory.exists_nonneg_hasCompactSupport_forall_integral_subgroup_translate_eq_one_of_isCompact
      (Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) hTc τ C' hC'c
  have hsec : ∀ x : AdelicGL2 (𝓞 K) K, F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) ≠ 0 →
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)), W ((t : AdelicGL2 (𝓞 K) K) * x) ∂τ = 1 := by
    intro x hx
    refine hW1 x ?_
    rw [hFconj] at hx
    obtain ⟨h, k, hh, hk, rfl⟩ := hC' x z (subset_tsupport _ hx)
    exact ⟨⟨h, (hTmem h).mpr hh⟩, k, hk, rfl⟩

  obtain ⟨w, ⟨hw0, hwm, hws, hw1⟩, rfl⟩ := hI
  have hFm : Measurable fun x : AdelicGL2 (𝓞 K) K => F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) := (hFc.comp hconjc).measurable
  have hFb : ∃ C : ℝ, ∀ x : AdelicGL2 (𝓞 K) K, ‖F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x)‖ ≤ C := ⟨Cf, fun x => hCf _⟩
  have hFT : ∀ (t : Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) (x : AdelicGL2 (𝓞 K) K),
      F (((t : AdelicGL2 (𝓞 K) K) * x)⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * ((t : AdelicGL2 (𝓞 K) K) * x)) = F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) := by
    intro t x
    have ht : (t : AdelicGL2 (𝓞 K) K)⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * t = (AutomorphicForm.globalPoints (𝓞 K) K γ) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp t.2
      rw [mul_assoc, ← this, ← mul_assoc, inv_mul_cancel, one_mul]
    have key : ((t : AdelicGL2 (𝓞 K) K) * x)⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * ((t : AdelicGL2 (𝓞 K) K) * x) = x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x := by
      rw [mul_inv_rev]
      calc x⁻¹ * (t : AdelicGL2 (𝓞 K) K)⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * ((t : AdelicGL2 (𝓞 K) K) * x)
          = x⁻¹ * ((t : AdelicGL2 (𝓞 K) K)⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * (t : AdelicGL2 (𝓞 K) K)) * x := by simp only [mul_assoc]
        _ = x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x := by rw [ht]
    rw [key]
  have hswap := MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
    (Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) hTc (adelicGLHaar (Fin 2) (𝓞 K) K) τ
    (fun x => F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x)) hFm hFb hFT w W ⟨hw0, hwm, hws, hw1⟩ ⟨hW0, hWm, hWs, hsec⟩
  rw [hswap]

  set Φ : AdelicGL2 (𝓞 K) K → ℂ := fun g => F (g⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * g) * (W g : ℂ) with hΦ
  have hΦm : Measurable Φ := hFm.mul (Complex.measurable_ofReal.comp hWm)
  have hCf0 : 0 ≤ Cf := le_trans (norm_nonneg _) (hCf 1)
  have hΦbound : ∀ g : AdelicGL2 (𝓞 K) K, ‖Φ g‖ ≤ (tsupport W).indicator (fun _ => Cf * B) g := by
    intro g
    by_cases hg : g ∈ tsupport W
    · rw [Set.indicator_of_mem hg, hΦ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hW0 g)]
      exact mul_le_mul (hCf _) (hWB g) (hW0 g) hCf0
    · rw [Set.indicator_of_notMem hg]
      have hWg : W g = 0 := image_eq_zero_of_notMem_tsupport hg
      simp only [hΦ, hWg, Complex.ofReal_zero, mul_zero, norm_zero, le_refl]
  have hΦint : Integrable Φ (adelicGLHaar (Fin 2) (𝓞 K) K) := by
    refine Integrable.mono' (g := (tsupport W).indicator (fun _ => Cf * B)) ?_ hΦm.aestronglyMeasurable
      (Filter.Eventually.of_forall hΦbound)
    refine IntegrableOn.integrable_indicator ?_ hWs.isCompact.measurableSet
    exact integrableOn_const (hWs.isCompact.measure_lt_top).ne enorm_ne_top
  obtain ⟨-, -, hC0⟩ :=
    HaarQuotient.integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
      (adelicGLHaar (Fin 2) (𝓞 K) K) HK hHKc μHK Φ hΦm hΦint.2

  have hTW : ∀ q : AdelicGL2 (𝓞 K) K,
      ∫ h : HK, (W ((h : AdelicGL2 (𝓞 K) K) * q) : ℂ) ∂μHK =
        ((cHK / cτK : ℝ) : ℂ) *
          ∫ t : Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)),
            (W ((t : AdelicGL2 (𝓞 K) K) * q) : ℂ) ∂τ := by
    intro q
    rw [hHKμ (fun x => (W (x * q) : ℂ)), hτc (fun x => (W (x * q) : ℂ)),
      integral_centralScalar_mul_diagUnits2_eq K νZK (fun x => (W (x * q) : ℂ))]
    have hτ0 : (cτK : ℂ) ≠ 0 := by exact_mod_cast hcτK.ne'
    push_cast
    field_simp
  have hfib : ∀ q : AdelicGL2 (𝓞 K) K,
      ∫ h : HK, Φ ((h : AdelicGL2 (𝓞 K) K) * q) ∂μHK =
        ((cHK / cτK : ℝ) : ℂ) * F (q⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * q) := by
    intro q
    have h1 : ∀ h : HK, Φ ((h : AdelicGL2 (𝓞 K) K) * q) =
        F (q⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * q) * (W ((h : AdelicGL2 (𝓞 K) K) * q) : ℂ) := by
      intro h
      simp only [hΦ]
      rw [hFT ⟨h, (hTmem h).mpr h.2⟩ q]
    simp_rw [h1]
    rw [integral_const_mul, hTW q]
    by_cases hz : F (q⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * q) = 0
    · simp [hz]
    · rw [integral_complex_ofReal, hsec q hz]
      push_cast
      ring

  rw [hC0]
  have hfun : (fun q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K) =>
      ∫ h : HK, Φ ((h : AdelicGL2 (𝓞 K) K) * q.out) ∂μHK) =
      fun q => ((cHK / cτK : ℝ) : ℂ) * F ((q.out)⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * q.out) :=
    funext fun q => hfib q.out
  rw [hfun, integral_const_mul, ← mul_assoc]
  have hc : ((cτK / cHK : ℝ) : ℂ) * ((cHK / cτK : ℝ) : ℂ) = 1 := by
    have hτ0 : (cτK : ℂ) ≠ 0 := by exact_mod_cast hcτK.ne'
    have hH0 : (cHK : ℂ) ≠ 0 := by exact_mod_cast hcHK.ne'
    push_cast
    field_simp
  rw [hc, one_mul]
  congr 1
  funext q
  exact hFconj q.out

open AutomorphicForm OQAux in
theorem weighted_part
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νZK.IsHaarMeasure]

    (HK : Subgroup (AdelicGL2 (𝓞 K) K)) (hHKc : IsClosed (HK : Set (AdelicGL2 (𝓞 K) K)))
    (hHK : ∀ h : AdelicGL2 (𝓞 K) K, h ∈ HK ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0))
    (μHK : Measure HK) [μHK.IsHaarMeasure] [μHK.IsMulRightInvariant]
    (cHK : ℝ) (hcHK : 0 < cHK)
    (hHKμ : ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ h : HK, g (h : AdelicGL2 (𝓞 K) K) ∂μHK =
        cHK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.centralScalar (𝓞 K) K p.1 * diagUnits2 p.2 1) ∂(νZK.prod νZK))
    (cτK : ℝ) (hcτK : 0 < cτK)
    (γ : GL (Fin 2) K) (h10 : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h01 : (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (hreg : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (τ : @Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)))
        (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) (AutomorphicForm.globalPoints (𝓞 K) K γ)))
    (hτ : @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) (AutomorphicForm.globalPoints (𝓞 K) K γ)) τ)
    (hτc : ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
        ∫ s : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)),
            g (s : AdelicGL2 (𝓞 K) K) ∂τ =
          cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (z : (AdeleRing (𝓞 K) K)ˣ) (J : ℂ)
    (hJ : AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (fun x : AdelicGL2 (𝓞 K) K =>
            -Real.log (NumberField.AdelicHeight.adelicHeight K x)
              - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)))
          (AutomorphicForm.globalPoints (𝓞 K) K γ) τ
          (fun g : AdelicGL2 (𝓞 K) K => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) J) :
    ((cτK / cHK : ℝ) : ℂ) * J =
        ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K),
              ((-Real.log (NumberField.AdelicHeight.adelicHeight K (q.out : AdelicGL2 (𝓞 K) K))
              - Real.log (NumberField.AdelicHeight.adelicHeight K
                  (AutomorphicForm.adelicWeyl (𝓞 K) K * (q.out : AdelicGL2 (𝓞 K) K))) : ℝ) : ℂ) *
              f (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K))))
            ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK) := by
  classical

  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : T2Space (AdelicGL2 (𝓞 K) K) := t2Space_adelicGL2 K
  haveI : LocallyCompactSpace (AdelicGL2 (𝓞 K) K) := locallyCompactSpace_adelicGL2 K
  haveI hμG : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI : SigmaCompactSpace (AdelicGL2 (𝓞 K) K) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 K) K) := Measure.IsHaarMeasure.sigmaFinite _
  haveI : SFinite (adelicGLHaar (Fin 2) (𝓞 K) K) := instSFiniteOfSigmaFinite

  have hTmem : ∀ h : AdelicGL2 (𝓞 K) K, h ∈ Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)) ↔ h ∈ HK := by
    intro h; rw [mem_centralizer_globalPoints_iff K γ h10 h01 hreg, hHK]
  have hTHK : Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)) = HK := Subgroup.ext hTmem
  have hTc : IsClosed ((Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)) : Subgroup (AdelicGL2 (𝓞 K) K)) :
      Set (AdelicGL2 (𝓞 K) K)) := by rw [hTHK]; exact hHKc
  haveI : BorelSpace (Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) := ⟨rfl⟩
  haveI hτi : τ.IsHaarMeasure := hτ
  have hcomm : ∀ s t : Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)), s * t = t * s := by
    intro s t
    apply Subtype.ext
    have hs := (hTmem s).mp s.2
    have ht := (hTmem t).mp t.2
    rw [hHK] at hs ht
    show (s : AdelicGL2 (𝓞 K) K) * t = t * s
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hs.1, hs.2, ht.1, ht.2, mul_comm]
  haveI : τ.IsMulRightInvariant := ⟨fun g => by
    have : (fun h : Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)) => h * g) = fun h => g * h :=
      funext fun h => hcomm h g
    rw [this]; exact map_mul_left_eq_self τ g⟩
  haveI : τ.IsInvInvariant := by
    letI : CommGroup (Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) := { mul_comm := hcomm }
    haveI : LocallyCompactSpace (Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) := hTc.locallyCompactSpace
    haveI : SecondCountableTopology (Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) :=
      Topology.IsEmbedding.subtypeVal.secondCountableTopology
    haveI : SigmaCompactSpace (Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) :=
      sigmaCompactSpace_of_locallyCompact_secondCountable
    exact Measure.IsHaarMeasure.isInvInvariant_of_innerRegular τ

  set F : AdelicGL2 (𝓞 K) K → ℂ := fun g => f (AutomorphicForm.centralScalar (𝓞 K) K z * g) with hF
  have hFc : Continuous F := hf.comp (continuous_const.mul continuous_id)
  have hFs : HasCompactSupport F := hfc.comp_homeomorph (Homeomorph.mulLeft (AutomorphicForm.centralScalar (𝓞 K) K z))
  obtain ⟨Cf, hCf⟩ := hf.bounded_above_of_compact_support hfc
  have hconjc : Continuous fun x : AdelicGL2 (𝓞 K) K => x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x :=
    (continuous_id.inv.mul continuous_const).mul continuous_id
  have hFconj : ∀ x : AdelicGL2 (𝓞 K) K, F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) = f (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * (AutomorphicForm.centralScalar (𝓞 K) K z * x)) := by
    intro x
    simp only [hF]
    rw [centralScalar_comm K z (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x), mul_assoc, mul_assoc, ← centralScalar_comm K z x, ← mul_assoc]

  obtain ⟨C', hC'c, hC'⟩ := exists_isCompact_forall_exists_mem_mul K HK hHK γ h10 h01 hreg (tsupport f) hfc
  obtain ⟨W, hW0, hWm, hWs, ⟨B, hWB⟩, hW1⟩ :=
    MeasureTheory.exists_nonneg_hasCompactSupport_forall_integral_subgroup_translate_eq_one_of_isCompact
      (Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) hTc τ C' hC'c
  have hsec : ∀ x : AdelicGL2 (𝓞 K) K, F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) ≠ 0 →
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)), W ((t : AdelicGL2 (𝓞 K) K) * x) ∂τ = 1 := by
    intro x hx
    refine hW1 x ?_
    rw [hFconj] at hx
    obtain ⟨h, k, hh, hk, rfl⟩ := hC' x z (subset_tsupport _ hx)
    exact ⟨⟨h, (hTmem h).mpr hh⟩, k, hk, rfl⟩

  set wt : AdelicGL2 (𝓞 K) K → ℝ := fun x =>
    -Real.log (NumberField.AdelicHeight.adelicHeight K x)
      - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)) with hwt
  obtain ⟨hwtinv, hwtc⟩ :=
    NumberField.AdelicHeight.neg_log_adelicHeight_sub_log_adelicHeight_adelicWeyl_mul_diagonal_mul_and_continuous K
  have hwtT : ∀ (t : Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)))
      (x : AdelicGL2 (𝓞 K) K), wt ((t : AdelicGL2 (𝓞 K) K) * x) = wt x := by
    intro t x
    have ht := (hTmem t).mp t.2
    rw [hHK] at ht
    exact hwtinv t ht.1 ht.2 x
  have hwtc' : Continuous wt := hwtc

  have hFm : Measurable fun x : AdelicGL2 (𝓞 K) K => F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) :=
    (hFc.comp hconjc).measurable
  have hF'm : Measurable fun x : AdelicGL2 (𝓞 K) K =>
      F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) * (wt x : ℂ) :=
    hFm.mul (Complex.measurable_ofReal.comp hwtc'.measurable)
  have hFT : ∀ (t : Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) (x : AdelicGL2 (𝓞 K) K),
      F (((t : AdelicGL2 (𝓞 K) K) * x)⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * ((t : AdelicGL2 (𝓞 K) K) * x)) = F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) := by
    intro t x
    have ht : (t : AdelicGL2 (𝓞 K) K)⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * t = (AutomorphicForm.globalPoints (𝓞 K) K γ) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp t.2
      rw [mul_assoc, ← this, ← mul_assoc, inv_mul_cancel, one_mul]
    have key : ((t : AdelicGL2 (𝓞 K) K) * x)⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * ((t : AdelicGL2 (𝓞 K) K) * x) = x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x := by
      rw [mul_inv_rev]
      calc x⁻¹ * (t : AdelicGL2 (𝓞 K) K)⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * ((t : AdelicGL2 (𝓞 K) K) * x)
          = x⁻¹ * ((t : AdelicGL2 (𝓞 K) K)⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * (t : AdelicGL2 (𝓞 K) K)) * x := by simp only [mul_assoc]
        _ = x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x := by rw [ht]
    rw [key]
  have hF'T : ∀ (t : Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) (x : AdelicGL2 (𝓞 K) K),
      F (((t : AdelicGL2 (𝓞 K) K) * x)⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * ((t : AdelicGL2 (𝓞 K) K) * x)) *
          (wt ((t : AdelicGL2 (𝓞 K) K) * x) : ℂ) =
        F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) * (wt x : ℂ) := by
    intro t x; rw [hFT t x, hwtT t x]

  obtain ⟨M, hM⟩ := hC'c.exists_bound_of_continuousOn (f := wt) hwtc'.continuousOn
  have hF'b : ∃ C : ℝ, ∀ x : AdelicGL2 (𝓞 K) K,
      ‖F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) * (wt x : ℂ)‖ ≤ C := by
    have hCf0 : 0 ≤ Cf := le_trans (norm_nonneg _) (hCf 1)
    refine ⟨max (Cf * M) 0, fun x => ?_⟩
    by_cases hx : F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) = 0
    · rw [hx, zero_mul, norm_zero]
      exact le_max_right _ _
    · have hx' := hx
      rw [hFconj] at hx'
      obtain ⟨h, k, hh, hk, rfl⟩ := hC' x z (subset_tsupport _ hx')
      rw [norm_mul, hwtT ⟨h, (hTmem h).mpr hh⟩ k, Complex.norm_real]
      exact le_trans (mul_le_mul (hCf _) (hM k hk) (norm_nonneg _) hCf0) (le_max_left _ _)

  obtain ⟨w, ⟨hw0, hwm, hws, hw1⟩, rfl⟩ := hJ
  have hw1' : ∀ x : AdelicGL2 (𝓞 K) K,
      F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) * (wt x : ℂ) ≠ 0 →
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)), w ((t : AdelicGL2 (𝓞 K) K) * x) ∂τ = 1 :=
    fun x hx => hw1 x (left_ne_zero_of_mul hx)
  have hsec' : ∀ x : AdelicGL2 (𝓞 K) K,
      F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) * (wt x : ℂ) ≠ 0 →
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)), W ((t : AdelicGL2 (𝓞 K) K) * x) ∂τ = 1 :=
    fun x hx => hsec x (left_ne_zero_of_mul hx)
  have hswap := MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one
    (Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K))) hTc (adelicGLHaar (Fin 2) (𝓞 K) K) τ
    (fun x => F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) * (wt x : ℂ)) hF'm hF'b hF'T w W
    ⟨hw0, hwm, hws, hw1'⟩ ⟨hW0, hWm, hWs, hsec'⟩
  rw [show (∫ x, F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) * (wt x : ℂ) * (w x : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
      ∫ x, F (x⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * x) * (wt x : ℂ) * (W x : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) from hswap]

  set Φ : AdelicGL2 (𝓞 K) K → ℂ := fun g =>
    F (g⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * g) * (wt g : ℂ) * (W g : ℂ) with hΦ
  have hΦm : Measurable Φ := hF'm.mul (Complex.measurable_ofReal.comp hWm)
  have hCf0 : 0 ≤ Cf := le_trans (norm_nonneg _) (hCf 1)
  obtain ⟨M', hM'⟩ := hWs.isCompact.exists_bound_of_continuousOn (f := wt) hwtc'.continuousOn
  have hM'0 : 0 ≤ max M' 0 := le_max_right _ _
  have hΦbound : ∀ g : AdelicGL2 (𝓞 K) K, ‖Φ g‖ ≤ (tsupport W).indicator (fun _ => Cf * max M' 0 * B) g := by
    intro g
    by_cases hg : g ∈ tsupport W
    · rw [Set.indicator_of_mem hg, hΦ, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs (W g), abs_of_nonneg (hW0 g)]
      have h1 : ‖F (g⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * g)‖ * ‖wt g‖ ≤ Cf * max M' 0 :=
        mul_le_mul (hCf _) (le_trans (hM' g hg) (le_max_left _ _)) (norm_nonneg _) hCf0
      exact mul_le_mul h1 (hWB g) (hW0 g) (mul_nonneg hCf0 hM'0)
    · rw [Set.indicator_of_notMem hg]
      have hWg : W g = 0 := image_eq_zero_of_notMem_tsupport hg
      simp only [hΦ, hWg, Complex.ofReal_zero, mul_zero, norm_zero, le_refl]
  have hΦint : Integrable Φ (adelicGLHaar (Fin 2) (𝓞 K) K) := by
    refine Integrable.mono' (g := (tsupport W).indicator (fun _ => Cf * max M' 0 * B)) ?_ hΦm.aestronglyMeasurable
      (Filter.Eventually.of_forall hΦbound)
    refine IntegrableOn.integrable_indicator ?_ hWs.isCompact.measurableSet
    exact integrableOn_const (hWs.isCompact.measure_lt_top).ne enorm_ne_top
  obtain ⟨-, -, hC0⟩ :=
    HaarQuotient.integrable_integral_comp_mul_out_and_integral_eq_integral_integral_comp_mul_out
      (adelicGLHaar (Fin 2) (𝓞 K) K) HK hHKc μHK Φ hΦm hΦint.2

  have hTW : ∀ q : AdelicGL2 (𝓞 K) K,
      ∫ h : HK, (W ((h : AdelicGL2 (𝓞 K) K) * q) : ℂ) ∂μHK =
        ((cHK / cτK : ℝ) : ℂ) *
          ∫ t : Subgroup.centralizer ({(AutomorphicForm.globalPoints (𝓞 K) K γ)} : Set (AdelicGL2 (𝓞 K) K)),
            (W ((t : AdelicGL2 (𝓞 K) K) * q) : ℂ) ∂τ := by
    intro q
    rw [hHKμ (fun x => (W (x * q) : ℂ)), hτc (fun x => (W (x * q) : ℂ)),
      integral_centralScalar_mul_diagUnits2_eq K νZK (fun x => (W (x * q) : ℂ))]
    have hτ0 : (cτK : ℂ) ≠ 0 := by exact_mod_cast hcτK.ne'
    push_cast
    field_simp
  have hfib : ∀ q : AdelicGL2 (𝓞 K) K,
      ∫ h : HK, Φ ((h : AdelicGL2 (𝓞 K) K) * q) ∂μHK =
        ((cHK / cτK : ℝ) : ℂ) * (F (q⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * q) * (wt q : ℂ)) := by
    intro q
    have h1 : ∀ h : HK, Φ ((h : AdelicGL2 (𝓞 K) K) * q) =
        (F (q⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * q) * (wt q : ℂ)) * (W ((h : AdelicGL2 (𝓞 K) K) * q) : ℂ) := by
      intro h
      simp only [hΦ]
      rw [hF'T ⟨h, (hTmem h).mpr h.2⟩ q]
    simp_rw [h1]
    rw [integral_const_mul, hTW q]
    by_cases hz : F (q⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * q) = 0
    · simp [hz]
    · rw [integral_complex_ofReal, hsec q hz]
      push_cast
      ring

  rw [hC0]
  have hfun : (fun q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K) =>
      ∫ h : HK, Φ ((h : AdelicGL2 (𝓞 K) K) * q.out) ∂μHK) =
      fun q => ((cHK / cτK : ℝ) : ℂ) * (F ((q.out)⁻¹ * (AutomorphicForm.globalPoints (𝓞 K) K γ) * q.out) * (wt q.out : ℂ)) :=
    funext fun q => hfib q.out
  rw [hfun, integral_const_mul, ← mul_assoc]
  have hc : ((cτK / cHK : ℝ) : ℂ) * ((cHK / cτK : ℝ) : ℂ) = 1 := by
    have hτ0 : (cτK : ℂ) ≠ 0 := by exact_mod_cast hcτK.ne'
    have hH0 : (cHK : ℂ) ≠ 0 := by exact_mod_cast hcHK.ne'
    push_cast
    field_simp
  rw [hc, one_mul]
  congr 1
  funext q
  rw [hFconj q.out, mul_comm]

open AutomorphicForm OQAux in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νZK.IsHaarMeasure]

    (HK : Subgroup (AdelicGL2 (𝓞 K) K)) (hHKc : IsClosed (HK : Set (AdelicGL2 (𝓞 K) K)))
    (hHK : ∀ h : AdelicGL2 (𝓞 K) K, h ∈ HK ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 1 = 0))
    (μHK : Measure HK) [μHK.IsHaarMeasure] [μHK.IsMulRightInvariant]
    (cHK : ℝ) (hcHK : 0 < cHK)
    (hHKμ : ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
      ∫ h : HK, g (h : AdelicGL2 (𝓞 K) K) ∂μHK =
        cHK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.centralScalar (𝓞 K) K p.1 * diagUnits2 p.2 1) ∂(νZK.prod νZK))
    (cτK : ℝ) (hcτK : 0 < cτK) :
    ∀ (γ : GL (Fin 2) K), (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 → (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 →
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1 →
    ∀ (τ : @Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)))
        (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) (AutomorphicForm.globalPoints (𝓞 K) K γ))),
      @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) (AutomorphicForm.globalPoints (𝓞 K) K γ)) τ →
      (∀ g : AdelicGL2 (𝓞 K) K → ℂ,
        ∫ s : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)),
            g (s : AdelicGL2 (𝓞 K) K) ∂τ =
          cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK)) →
    ∀ (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous f → HasCompactSupport f →

    (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (I : ℂ),
      AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.globalPoints (𝓞 K) K γ) τ
          (fun g : AdelicGL2 (𝓞 K) K => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) I →
      ((cτK / cHK : ℝ) : ℂ) * I =
        ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K),
              f (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K))))
            ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK)) ∧

    (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (J : ℂ),
      AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
          (fun x : AdelicGL2 (𝓞 K) K =>
          -Real.log (NumberField.AdelicHeight.adelicHeight K x)
            - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)))
          (AutomorphicForm.globalPoints (𝓞 K) K γ) τ
          (fun g : AdelicGL2 (𝓞 K) K => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) J →
      ((cτK / cHK : ℝ) : ℂ) * J =
        ∫ q : MulAction.orbitRel.Quotient HK (AdelicGL2 (𝓞 K) K),
              ((-Real.log (NumberField.AdelicHeight.adelicHeight K (q.out : AdelicGL2 (𝓞 K) K))
              - Real.log (NumberField.AdelicHeight.adelicHeight K
                  (AutomorphicForm.adelicWeyl (𝓞 K) K * (q.out : AdelicGL2 (𝓞 K) K))) : ℝ) : ℂ) *
              f (((q.out : AdelicGL2 (𝓞 K) K))⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
                (AutomorphicForm.centralScalar (𝓞 K) K z * ((q.out : AdelicGL2 (𝓞 K) K))))
            ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 K) K) HK μHK)) := by
  intro γ h10 h01 hreg τ hτ hτc f hf hfc
  exact ⟨fun z I hI => plain_part K νZK HK hHKc hHK μHK cHK hcHK hHKμ cτK hcτK γ h10 h01 hreg τ hτ hτc f hf hfc z I hI,
    fun z J hJ => weighted_part K νZK HK hHKc hHK μHK cHK hcHK hHKμ cτK hcτK γ h10 h01 hreg τ hτ hτc f hf hfc z J hJ⟩

end S_AutomorphicForm_const_mul_eq_integral_haarQuotient_centralScalar_of_isOrbitalIntegralOn_of_diagonal
end P2MW
export P2MW.S_AutomorphicForm_const_mul_eq_integral_haarQuotient_centralScalar_of_isOrbitalIntegralOn_of_diagonal (solution)
