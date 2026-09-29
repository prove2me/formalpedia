-- Prove2me | solution 1 for AutomorphicForm.exists_forall_le_setIntegral_lambdaT_twistedAdelicKernel_sub_centralElliptic_eq_setIntegral_parabolic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/571eef4b-37bd-5072-82ba-8d52a38635b9

import Theorems.Thm_AutomorphicForm_lintegral_lintegral_tsum_enorm_twistedKernel_normClass_elliptic_or_central_lt_top
import Theorems.Thm_AutomorphicForm_exists_forall_le_integrableOn_mul_lambdaT_twistedAdelicKernel_canonicalTruncationDomain_prod
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
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

namespace P2MW.S_AutomorphicForm_exists_forall_le_setIntegral_lambdaT_twistedAdelicKernel_sub_centralElliptic_eq_setIntegral_parabolic
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply ContinuousAddEquiv.preimage_mulLeft_smul M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.mem_inducedSectionSubmodule_iff"

set_option autoImplicit false

noncomputable section

namespace R3TwCoarse

open MeasureTheory NumberField NumberField.AdelicHaar

section Instances

variable (L : Type) [Field L] [NumberField L]

theorem secondCountableTopology_adeleRing : SecondCountableTopology (AdeleRing (𝓞 L) L) :=
  NumberField.AdeleRing.secondCountableTopology L

theorem secondCountableTopology_mulOpposite {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology

theorem secondCountableTopology_units {M : Type*} [TopologicalSpace M] [Monoid M]
    [SecondCountableTopology M] : SecondCountableTopology Mˣ := by
  haveI : SecondCountableTopology Mᵐᵒᵖ := secondCountableTopology_mulOpposite
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem secondCountableTopology_ideles : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := secondCountableTopology_adeleRing L
  exact secondCountableTopology_units

theorem secondCountableTopology_adelicGL2 :
    SecondCountableTopology (AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := secondCountableTopology_adeleRing L
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 L) L))
  exact secondCountableTopology_units

theorem countable_GL2 : Countable (GL (Fin 2) L) := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) L → _)) Units.val_injective

theorem countable_range_globalPoints : Countable (AutomorphicForm.globalPoints (𝓞 L) L).range := by
  haveI := countable_GL2 L
  exact (MonoidHom.rangeRestrict_surjective (AutomorphicForm.globalPoints (𝓞 L) L)).countable

end Instances

section Algebra

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

theorem sigmaAdelicAct_centralScalar (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z) =
      AutomorphicForm.centralScalar (𝓞 L) L
        (Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _) z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  simp only [AutomorphicForm.sigmaAdelicAct, AutomorphicForm.centralScalar,
    Matrix.GeneralLinearGroup.map_apply]
  change ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom)
      (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) (((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (z : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem centralScalar_comm (w : (AdeleRing (𝓞 L) L)ˣ) (y : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.centralScalar (𝓞 L) L w * y = y * AutomorphicForm.centralScalar (𝓞 L) L w := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (w : AdeleRing (𝓞 L) L) (fun r' => mul_comm _ r')
    (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq i) j

theorem mul_cs (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    g * AutomorphicForm.centralScalar (𝓞 L) L w = AutomorphicForm.centralScalar (𝓞 L) L w * g :=
  (centralScalar_comm L w g).symm

theorem mul_cs_left (g y : AutomorphicForm.AdelicGL2 (𝓞 L) L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    g * (AutomorphicForm.centralScalar (𝓞 L) L w * y) =
      AutomorphicForm.centralScalar (𝓞 L) L w * (g * y) := by
  rw [← mul_assoc, mul_cs, mul_assoc]

theorem continuous_centralScalar :
    Continuous (AutomorphicForm.centralScalar (𝓞 L) L :
      (AdeleRing (𝓞 L) L)ˣ → AutomorphicForm.AdelicGL2 (𝓞 L) L) := by
  have hsc : Continuous (Matrix.scalar (Fin 2) : AdeleRing (𝓞 L) L → Matrix (Fin 2) (Fin 2) _) := by
    refine continuous_matrix fun i j => ?_
    by_cases hij : i = j
    · subst hij; first | simpa [Matrix.scalar_apply] using continuous_id | (simp [Matrix.scalar_apply]; exact continuous_id)
    · simpa [Matrix.scalar_apply, hij] using continuous_const
  exact Continuous.units_map _ hsc

def kfun (σ : L ≃ₐ[K] L) (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (δ : GL (Fin 2) L)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))

theorem kfun_sigmaConj (σ : L ≃ₐ[K] L) (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (h δ : GL (Fin 2) L)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    kfun K L D σ φ (h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h) x z =
      kfun K L D σ φ δ (AutomorphicForm.globalPoints (𝓞 L) L h * x) z := by
  unfold kfun
  congr 1
  have h3 : AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.globalPoints (𝓞 L) L h) =
      AutomorphicForm.globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) h) :=
    AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ h
  rw [map_mul, map_mul, map_inv, mul_inv_rev, map_mul (AutomorphicForm.sigmaAdelicAct K L D σ),
    map_mul (AutomorphicForm.sigmaAdelicAct K L D σ), map_mul (AutomorphicForm.sigmaAdelicAct K L D σ),
    h3, sigmaAdelicAct_centralScalar]
  simp only [mul_assoc, mul_cs_left]

end Algebra

section Slab

variable (L : Type) [Field L] [NumberField L]

def slab (α β : ℝ) : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem ideleNorm_det_globalPoints (γ : GL (Fin 2) L) :
    NumberField.TateGlobal.ideleNorm L
      (Matrix.GeneralLinearGroup.det (AutomorphicForm.globalPoints (𝓞 L) L γ)) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := ⟨rfl⟩
  unfold NumberField.TateGlobal.ideleNorm AutomorphicForm.globalPoints
  rw [Matrix.GeneralLinearGroup.map_det]
  have := NumberField.AdeleRing.distribHaarChar_algebraMap L (Matrix.GeneralLinearGroup.det γ)
  simp only [RingHom.toMonoidHom_eq_coe] at this
  rw [this]
  simp

theorem globalPoints_mul_mem_slab_iff (α β : ℝ) (γ : GL (Fin 2) L)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    AutomorphicForm.globalPoints (𝓞 L) L γ * g ∈ slab L α β ↔ g ∈ slab L α β := by
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    ideleNorm_det_globalPoints, one_mul]

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem borelSpace_adelicGL2 : BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L) :=
  NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L

attribute [local instance] borelSpace_adelicGL2

theorem smulInvariantMeasure_restrict_slab (α β : ℝ) :
    SMulInvariantMeasure (AutomorphicForm.globalPoints (𝓞 L) L).range
      (AutomorphicForm.AdelicGL2 (𝓞 L) L)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  refine ⟨fun γ s hs => ?_⟩
  obtain ⟨_, γ, rfl⟩ := γ
  have hmeas : MeasurableSet ((fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      AutomorphicForm.globalPoints (𝓞 L) L γ * x) ⁻¹' s) := (measurable_const_mul _) hs
  change ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β))
      ((fun x => AutomorphicForm.globalPoints (𝓞 L) L γ * x) ⁻¹' s) = _
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hs]
  have hset : (fun x => AutomorphicForm.globalPoints (𝓞 L) L γ * x) ⁻¹' s ∩ slab L α β =
      (fun x => AutomorphicForm.globalPoints (𝓞 L) L γ * x) ⁻¹' (s ∩ slab L α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, globalPoints_mul_mem_slab_iff]
  rw [hset, measure_preimage_mul]

end Slab

section LocalFiniteness

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem globalPoints_eq_of_eq (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ)
    (δ : GL (Fin 2) L) :
    AutomorphicForm.globalPoints (𝓞 L) L δ =
      x * (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) *
        (AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))⁻¹ := by
  group

theorem finite_setOf_exists_apply_ne_zero
    {N : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ)}
    (hN : IsCompact N) {φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ} (hφc : HasCompactSupport φ) :
    {δ : GL (Fin 2) L | ∃ p ∈ N, φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1)) ≠ 0}.Finite := by
  set F : (AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AutomorphicForm.AdelicGL2 (𝓞 L) L →
      AutomorphicForm.AdelicGL2 (𝓞 L) L := fun q =>
    q.1.1 * q.2 * (AutomorphicForm.sigmaAdelicAct K L D σ
      (AutomorphicForm.centralScalar (𝓞 L) L q.1.2 * q.1.1))⁻¹ with hF
  have hFc : Continuous F := by
    have h1 : Continuous fun q : (AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) ×
        AutomorphicForm.AdelicGL2 (𝓞 L) L => q.1.1 := continuous_fst.comp continuous_fst
    have h2 : Continuous fun q : (AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) ×
        AutomorphicForm.AdelicGL2 (𝓞 L) L => q.1.2 := continuous_snd.comp continuous_fst
    have h3 : Continuous fun q : (AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) ×
        AutomorphicForm.AdelicGL2 (𝓞 L) L =>
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L q.1.2 * q.1.1) :=
      (AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp
        (((continuous_centralScalar L).comp h2).mul h1)
    exact ((h1.mul continuous_snd).mul h3.inv)
  have hC : IsCompact (F '' (N ×ˢ tsupport φ)) := (hN.prod hφc).image hFc
  have hfin := AutomorphicForm.adelicKernelLocalFiniteness L _ hC 1 1
  refine hfin.subset fun δ hδ => ?_
  obtain ⟨p, hp, hne⟩ := hδ
  simp only [Set.mem_setOf_eq, inv_one, one_mul, mul_one]
  refine ⟨⟨p, _⟩, ⟨hp, subset_tsupport _ (Function.mem_support.2 hne)⟩, ?_⟩
  simp only [hF]
  exact (globalPoints_eq_of_eq K L D σ p.1 p.2 δ).symm

theorem finite_support_kfun {φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ} (hφc : HasCompactSupport φ)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    (Function.support fun δ : GL (Fin 2) L => kfun K L D σ φ δ x z).Finite := by
  refine (finite_setOf_exists_apply_ne_zero K L D σ (isCompact_singleton (x := (x, z))) hφc).subset ?_
  intro δ hδ
  exact ⟨(x, z), Set.mem_singleton _, hδ⟩

end LocalFiniteness

section ClassSums

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

def hfun (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ)
    (δ : GL (Fin 2) L) (p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  ((ξ ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) *
    φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1))

theorem continuous_twistArg (δ : GL (Fin 2) L) :
    Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1) :=
  ((continuous_fst.inv).mul continuous_const).mul
    ((AutomorphicForm.continuous_sigmaAdelicAct K L D σ).comp
      (((continuous_centralScalar L).comp continuous_snd).mul continuous_fst))

theorem continuous_hfun {ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ}
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    {φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ) (δ : GL (Fin 2) L) :
    Continuous (hfun K L D σ ξ φ δ) :=
  (hξc.comp continuous_snd).mul (hφ.comp (continuous_twistArg K L D σ δ))

theorem exists_finset_tsum_eq_sum {ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ}
    {φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ} (hφc : HasCompactSupport φ) (P : GL (Fin 2) L → Prop)
    {N : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ)} (hN : IsCompact N) :
    ∃ S : Finset {δ : GL (Fin 2) L // P δ}, ∀ p ∈ N,
      (∀ δ : {δ : GL (Fin 2) L // P δ}, δ ∉ S → hfun K L D σ ξ φ δ p = 0) ∧
      ∑' δ : {δ : GL (Fin 2) L // P δ}, hfun K L D σ ξ φ δ p =
        ∑ δ ∈ S, hfun K L D σ ξ φ δ p := by
  have hfin := finite_setOf_exists_apply_ne_zero K L D σ hN hφc
  have hfin' : (Subtype.val ⁻¹' {δ : GL (Fin 2) L | ∃ p ∈ N, φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1)) ≠ 0} :
      Set {δ : GL (Fin 2) L // P δ}).Finite := hfin.preimage Subtype.val_injective.injOn
  refine ⟨hfin'.toFinset, fun p hp => ?_⟩
  have hzero : ∀ δ : {δ : GL (Fin 2) L // P δ}, δ ∉ hfin'.toFinset → hfun K L D σ ξ φ δ p = 0 := by
    intro δ hδ
    rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq, not_exists] at hδ
    have := hδ p
    rw [not_and, not_not] at this
    simp only [hfun, this hp, mul_zero]
  refine ⟨hzero, tsum_eq_sum' ?_⟩
  intro δ hδ
  by_contra h
  exact hδ (hzero δ h)

theorem continuous_tsum_hfun {ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ}
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    {φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (P : GL (Fin 2) L → Prop) :
    Continuous fun p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ∑' δ : {δ : GL (Fin 2) L // P δ}, hfun K L D σ ξ φ δ p := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨N, hN, hNp⟩ := exists_compact_mem_nhds p₀
  obtain ⟨S, hS⟩ := exists_finset_tsum_eq_sum K L D σ hφc P hN
  have hcont : Continuous fun p => ∑ δ ∈ S, hfun K L D σ ξ φ δ p :=
    continuous_finsetSum S fun δ _ => continuous_hfun K L D σ hξc hφ δ
  have hon : ContinuousOn (fun p => ∑' δ : {δ : GL (Fin 2) L // P δ}, hfun K L D σ ξ φ δ p) N :=
    hcont.continuousOn.congr fun p hp => (hS p hp).2
  exact hon.continuousAt hNp

theorem tsum_hfun_eq_mul_finsum {ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ}
    {φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ} (hφc : HasCompactSupport φ) (P : GL (Fin 2) L → Prop)
    (p : AutomorphicForm.AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) :
    ∑' δ : {δ : GL (Fin 2) L // P δ}, hfun K L D σ ξ φ δ p =
      ((ξ ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) *
        ∑ᶠ δ ∈ {δ : GL (Fin 2) L | P δ}, φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
          AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1)) := by
  have hfin := finite_setOf_exists_apply_ne_zero K L D σ (isCompact_singleton (x := p)) hφc
  set g : GL (Fin 2) L → ℂ := fun δ => φ (p.1⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
    AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L p.2 * p.1)) with hg
  have hsupp : (Function.support fun δ : {δ : GL (Fin 2) L // P δ} => g δ).Finite := by
    refine (hfin.preimage Subtype.val_injective.injOn).subset fun δ hδ => ?_
    exact ⟨p, Set.mem_singleton p, hδ⟩
  have h1 : ∑' δ : {δ : GL (Fin 2) L // P δ}, hfun K L D σ ξ φ δ p =
      ((ξ ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) * ∑' δ : {δ : GL (Fin 2) L // P δ}, g δ := by
    rw [← tsum_mul_left]; rfl
  rw [h1, tsum_eq_finsum hsupp]
  congr 1
  exact finsum_set_coe_eq_finsum_mem (s := {δ | P δ}) (f := g)

end ClassSums

section Cells

p2m_open "Polynomial AutomorphicForm~ideleNorm_det_globalPoints"

variable {K : Type*} [Field K]

theorem charpoly_eq_mul_of_isRoot (M : Matrix (Fin 2) (Fin 2) K) {a : K} (ha : M.charpoly.IsRoot a) :
    M.charpoly = (X - C a) * (X - C (M.trace - a)) := by
  have hdet : M.det = a * (M.trace - a) := by
    rw [Polynomial.IsRoot, Matrix.charpoly_fin_two] at ha
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C] at ha
    linear_combination ha
  rw [Matrix.charpoly_fin_two, hdet, map_sub, map_mul, map_sub]
  ring

theorem cells_cover (γ : GL (Fin 2) K) :
    (γ ∈ ellipticCell K ∨ γ ∈ centralCell K) ∨ (γ ∈ hyperbolicCell K ∨ γ ∈ unipotentCell K) := by
  set M : Matrix (Fin 2) (Fin 2) K := ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hM
  by_cases hc : IsCentralType M
  · exact Or.inl (Or.inr hc)
  by_cases he : IsEllipticType M
  · exact Or.inl (Or.inl he)
  right
  unfold IsEllipticType at he
  push Not at he
  obtain ⟨a, ha⟩ := he
  by_cases hab : a = M.trace - a
  · refine Or.inr ⟨hc, a, ?_⟩
    rw [charpoly_eq_mul_of_isRoot M ha, ← hab, sq]
  · exact Or.inl ⟨a, M.trace - a, hab, charpoly_eq_mul_of_isRoot M ha⟩

theorem charpoly_conj (c γ : GL (Fin 2) K) :
    ((c * γ * c⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly =
      ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj c _

theorem isCentralType_conj {c γ : GL (Fin 2) K}
    (h : IsCentralType ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) :
    IsCentralType ((c * γ * c⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, ha, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_nonsing_inv _ (Matrix.isUnits_det_units c)]

theorem eval_charpoly_smul_one (d t : K) :
    ((d • (1 : Matrix (Fin 2) (Fin 2) K)).charpoly).eval t = (t - d) ^ 2 := by
  rw [Matrix.charpoly_fin_two]
  simp
  ring

theorem eq_of_isRoot_of_isCentralType {M : Matrix (Fin 2) (Fin 2) K} (h : IsCentralType M) {a b : K}
    (ha : M.charpoly.IsRoot a) (hb : M.charpoly.IsRoot b) : a = b := by
  obtain ⟨d, rfl⟩ := h
  rw [IsRoot, eval_charpoly_smul_one] at ha hb
  have ha' : a = d := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp ha)
  have hb' : b = d := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hb)
  exact ha'.trans hb'.symm

theorem cells_disjoint {γ₁ γ₂ : GL (Fin 2) K}
    (h₁ : γ₁ ∈ ellipticCell K ∨ γ₁ ∈ centralCell K)
    (h₂ : γ₂ ∈ hyperbolicCell K ∨ γ₂ ∈ unipotentCell K) (hc : IsConj γ₁ γ₂) : False := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hc

  have hchar : ((γ₂ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly =
      ((γ₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly := by
    rw [← hc]; exact charpoly_conj c γ₁

  have hroot : ∃ a : K, ((γ₂ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly.IsRoot a := by
    rcases h₂ with ⟨a, b, _, hab⟩ | ⟨_, a, ha⟩
    · exact ⟨a, by rw [hab, IsRoot, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]⟩
    · exact ⟨a, by rw [ha, IsRoot, eval_pow, eval_sub, eval_X, eval_C, sub_self, zero_pow two_ne_zero]⟩
  rcases h₁ with he | hce
  · obtain ⟨a, ha⟩ := hroot
    rw [hchar] at ha
    exact he a ha
  · have hc2 : IsCentralType ((γ₂ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
      rw [← hc]; exact isCentralType_conj hce
    rcases h₂ with ⟨a, b, hab, habp⟩ | ⟨hnc, _⟩
    · have hra : ((γ₂ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly.IsRoot a := by
        rw [habp, IsRoot, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
      have hrb : ((γ₂ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).charpoly.IsRoot b := by
        rw [habp, IsRoot, eval_mul, eval_sub, eval_sub, eval_X, eval_C, eval_C, sub_self, mul_zero]
      exact hab (eq_of_isRoot_of_isCentralType hc2 hra hrb)
    · exact hnc hc2

variable {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

def QCE {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : LT.TwistedNorm.SigmaConjClasses σ) : Prop :=
  ∃ γ : GL (Fin 2) K, (γ ∈ ellipticCell K ∨ γ ∈ centralCell K) ∧
    LT.TwistedNorm.normClassMap hgen c = ConjClasses.mk γ

def QHU {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c : LT.TwistedNorm.SigmaConjClasses σ) : Prop :=
  ∃ γ : GL (Fin 2) K, (γ ∈ hyperbolicCell K ∨ γ ∈ unipotentCell K) ∧
    LT.TwistedNorm.normClassMap hgen c = ConjClasses.mk γ

theorem qce_or_qhu {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) :
    QCE hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) ∨ QHU hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) := by
  have hn := LT.TwistedNorm.normClassMap_mk hgen δ
  rcases cells_cover (LT.TwistedNorm.normRep hgen δ) with h | h
  · exact Or.inl ⟨_, h, hn⟩
  · exact Or.inr ⟨_, h, hn⟩

theorem not_qce_of_qhu {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {c : LT.TwistedNorm.SigmaConjClasses σ} (h₁ : QCE hgen c) (h₂ : QHU hgen c) : False := by
  obtain ⟨γ₁, hγ₁, e₁⟩ := h₁
  obtain ⟨γ₂, hγ₂, e₂⟩ := h₂
  exact cells_disjoint hγ₁ hγ₂ (ConjClasses.mk_eq_mk_iff_isConj.mp (e₁.symm.trans e₂))

theorem setOf_qce_union_setOf_qhu {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    {δ : GL (Fin 2) L | QCE hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ)} ∪
      {δ : GL (Fin 2) L | QHU hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ)} = Set.univ :=
  Set.eq_univ_of_forall fun δ => qce_or_qhu hgen δ

theorem disjoint_setOf_qce_setOf_qhu {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    Disjoint {δ : GL (Fin 2) L | QCE hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ)}
      {δ : GL (Fin 2) L | QHU hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ)} :=
  Set.disjoint_left.mpr fun _ h₁ h₂ => not_qce_of_qhu hgen h₁ h₂

omit [FiniteDimensional K L] [IsGalois K L] in

theorem mk_sigmaConj (σ : L ≃ₐ[K] L) (h δ : GL (Fin 2) L) :
    LT.TwistedNorm.SigmaConjClasses.mk σ (h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h) =
      LT.TwistedNorm.SigmaConjClasses.mk σ δ :=
  (LT.TwistedNorm.SigmaConjClasses.mk_eq_mk_iff_exists_eq_inv_mul_mul_map.mpr ⟨h, rfl⟩).symm

omit [FiniteDimensional K L] [IsGalois K L] in

theorem bijOn_sigmaConj (σ : L ≃ₐ[K] L) (Q : LT.TwistedNorm.SigmaConjClasses σ → Prop) (h : GL (Fin 2) L) :
    Set.BijOn (fun δ : GL (Fin 2) L => h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h)
      {δ | Q (LT.TwistedNorm.SigmaConjClasses.mk σ δ)} {δ | Q (LT.TwistedNorm.SigmaConjClasses.mk σ δ)} := by
  refine ⟨fun δ hδ => ?_, fun δ _ δ' _ hh => ?_, fun δ hδ => ?_⟩
  · simp only [Set.mem_setOf_eq, mk_sigmaConj]; exact hδ
  · have := congrArg (fun y => h * y * (Matrix.GeneralLinearGroup.map (σ : L →+* L) h)⁻¹) hh
    simpa [mul_assoc] using this
  · refine ⟨h * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) h)⁻¹, ?_, by group⟩
    simp only [Set.mem_setOf_eq]
    have e : LT.TwistedNorm.SigmaConjClasses.mk σ (h * δ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) h)⁻¹) =
        LT.TwistedNorm.SigmaConjClasses.mk σ δ := by
      have := mk_sigmaConj σ h⁻¹ δ
      rw [inv_inv, map_inv] at this
      exact this
    rw [e]; exact hδ

end Cells

section Split

p2m_open "AutomorphicForm~ideleNorm_det_globalPoints"

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

def pieceSum (σ : L ≃ₐ[K] L) (Q : LT.TwistedNorm.SigmaConjClasses σ → Prop)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  ∑ᶠ δ ∈ {δ : GL (Fin 2) L | Q (LT.TwistedNorm.SigmaConjClasses.mk σ δ)}, kfun K L D σ φ δ x z

theorem twistedAdelicKernel_eq_pieceSum_add {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {φ : AdelicGL2 (𝓞 L) L → ℂ} (hφc : HasCompactSupport φ)
    (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    twistedAdelicKernel L (sigmaAdelicAct K L D σ) φ x (centralScalar (𝓞 L) L z * x) =
      pieceSum K L D σ (QCE hgen) φ x z + pieceSum K L D σ (QHU hgen) φ x z := by
  have hfin := finite_support_kfun K L D σ hφc x z
  unfold twistedAdelicKernel pieceSum
  rw [← finsum_mem_univ, ← setOf_qce_union_setOf_qhu hgen]
  exact finsum_mem_union' (disjoint_setOf_qce_setOf_qhu hgen) (hfin.subset Set.inter_subset_right)
    (hfin.subset Set.inter_subset_right)

omit [FiniteDimensional K L] [IsGalois K L] in

theorem pieceSum_globalPoints_mul (σ : L ≃ₐ[K] L) (Q : LT.TwistedNorm.SigmaConjClasses σ → Prop)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (h : GL (Fin 2) L) (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    pieceSum K L D σ Q φ (globalPoints (𝓞 L) L h * x) z = pieceSum K L D σ Q φ x z := by
  unfold pieceSum
  exact finsum_mem_eq_of_bijOn _ (bijOn_sigmaConj σ Q h) fun δ _ => (kfun_sigmaConj K L D σ φ h δ x z).symm

end Split

section Bochner

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]

theorem integral_integral_sub_of_split (μ : Measure X) (ν : Measure Z) [SFinite μ] [SFinite ν]
    (ξ : Z → ℂ) (Kf CE HU IND : X → Z → ℂ)
    (hsplit : ∀ x z, Kf x z = CE x z + HU x z)
    (hCE : Integrable (fun p : X × Z => ξ p.2 * CE p.1 p.2) (μ.prod ν))
    (hT : Integrable (fun p : X × Z => ξ p.2 * (Kf p.1 p.2 - IND p.1 p.2)) (μ.prod ν)) :
    (∫ x, (∫ z, ξ z * (Kf x z - IND x z) ∂ν) ∂μ) - (∫ x, (∫ z, ξ z * CE x z ∂ν) ∂μ) =
      ∫ x, (∫ z, ξ z * (HU x z - IND x z) ∂ν) ∂μ := by
  rw [← integral_sub hT.integral_prod_left hCE.integral_prod_left]
  refine integral_congr_ae ?_
  filter_upwards [hT.prod_right_ae, hCE.prod_right_ae] with x hxT hxCE
  rw [← integral_sub hxT hxCE]
  congr 1
  funext z
  rw [hsplit]
  ring

end Bochner

section Main

p2m_open "AutomorphicForm~ideleNorm_det_globalPoints"
open scoped ENNReal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] borelSpace_adelicGL2

theorem main
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ slab L α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
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
    (IND : ℝ → AdelicGL2 (𝓞 L) L → (AdeleRing (𝓞 L) L)ˣ → ℂ)
    (hT : ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      IntegrableOn (fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
          ((ξL ⟨p.2, Subgroup.mem_top p.2⟩ : ℂˣ) : ℂ) *
            (twistedAdelicKernel L (sigmaAdelicAct K L D σ) φ p.1 (centralScalar (𝓞 L) L p.2 * p.1) -
              IND R p.1 p.2))
        (canonicalTruncationDomain L α β ×ˢ ΩL) ((adelicGLHaar (Fin 2) (𝓞 L) L).prod νZL)) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∫ x in canonicalTruncationDomain L α β,
          (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (twistedAdelicKernel L (sigmaAdelicAct K L D σ) φ x (centralScalar (𝓞 L) L z * x) - IND R x z)
            ∂νZL) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
      (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          pieceSum K L D σ (QCE hgen) φ x z ∂νZL) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      ∫ x in canonicalTruncationDomain L α β,
          (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (pieceSum K L D σ (QHU hgen) φ x z - IND R x z) ∂νZL) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by

  haveI hSCG : SecondCountableTopology (AdelicGL2 (𝓞 L) L) := secondCountableTopology_adelicGL2 L
  haveI hSCZ : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_ideles L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI : SigmaCompactSpace (AdelicGL2 (𝓞 L) L) := inferInstance
  haveI : SigmaCompactSpace (AdeleRing (𝓞 L) L)ˣ := inferInstance
  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 L) L) := inferInstance
  haveI : SigmaFinite νZL := inferInstance
  haveI := smulInvariantMeasure_restrict_slab L α β
  haveI : Countable (GL (Fin 2) L) := countable_GL2 L
  haveI : Countable (globalPoints (𝓞 L) L).range := countable_range_globalPoints L

  set Haar := adelicGLHaar (Fin 2) (𝓞 L) L with hHaar
  set Φ₀ := canonicalTruncationDomain L α β with hΦ₀
  set ξ' : (AdeleRing (𝓞 L) L)ˣ → ℂ := fun z => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) with hξ'
  set Kσ : AdelicGL2 (𝓞 L) L → (AdeleRing (𝓞 L) L)ˣ → ℂ := fun x z =>
    twistedAdelicKernel L (sigmaAdelicAct K L D σ) φ x (centralScalar (𝓞 L) L z * x) with hKσ
  set CE : AdelicGL2 (𝓞 L) L → (AdeleRing (𝓞 L) L)ˣ → ℂ := pieceSum K L D σ (QCE hgen) φ with hCE
  set HU : AdelicGL2 (𝓞 L) L → (AdeleRing (𝓞 L) L)ˣ → ℂ := pieceSum K L D σ (QHU hgen) φ with hHU

  have hdat := canonicalTruncationData_isTruncationDatum L α β hα hαβ
  have hΦ₀s : Φ₀ ⊆ slab L α β := hdat.2.2.2.1
  have hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀ (Haar.restrict (slab L α β)) := hdat.2.2.2.2

  have hsplit : ∀ x z, Kσ x z = CE x z + HU x z := fun x z =>
    twistedAdelicKernel_eq_pieceSum_add K L D hgen hφc x z

  set I := {δ : GL (Fin 2) L // QCE hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ)} with hI
  set h : GL (Fin 2) L → AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ → ℂ := hfun K L D σ ξL φ with hh
  have habs : ∫⁻ x in Φ₀, ∫⁻ z in ΩL, ∑' δ : I, ‖h δ (x, z)‖ₑ ∂νZL ∂Haar < ⊤ :=
    lintegral_lintegral_tsum_enorm_twistedKernel_normClass_elliptic_or_central_lt_top K L hgen D α β hα Φ₀
      hΦ₀s hΦ₀ νZL ΩL hΩL ξL hξc hξt φ hφ hφc
  have hcont : Continuous fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => ∑' δ : I, h δ p :=
    continuous_tsum_hfun K L D σ hξc hφ hφc _
  have hCEt : Integrable (fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => ∑' δ : I, h δ p)
      ((Haar.restrict Φ₀).prod (νZL.restrict ΩL)) := by
    refine ⟨hcont.aestronglyMeasurable, ?_⟩
    dsimp only [HasFiniteIntegral]
    rw [lintegral_prod (fun p => ‖(fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => ∑' δ : I, h δ p) p‖ₑ)
      hcont.measurable.enorm.aemeasurable]
    refine lt_of_le_of_lt ?_ habs
    exact lintegral_mono fun x => lintegral_mono fun z => enorm_tsum_le_tsum_enorm
  have hCEint : Integrable (fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => ξ' p.2 * CE p.1 p.2)
      ((Haar.restrict Φ₀).prod (νZL.restrict ΩL)) := by
    refine hCEt.congr (ae_of_all _ fun p => ?_)
    exact tsum_hfun_eq_mul_finsum K L D σ hφc _ p

  set F : AdelicGL2 (𝓞 L) L → ℂ := fun x => ∫ z in ΩL, ξ' z * CE x z ∂νZL with hF
  have hinv : ∀ (g : (globalPoints (𝓞 L) L).range) (x : AdelicGL2 (𝓞 L) L), F (g • x) = F x := by
    rintro ⟨_, γ, rfl⟩ x
    show F (globalPoints (𝓞 L) L γ * x) = F x
    simp only [hF, hCE, pieceSum_globalPoints_mul]
  have hdom : ∫ x in ΦL, F x ∂Haar = ∫ x in Φ₀, F x ∂Haar := by
    have key := IsFundamentalDomain.setIntegral_eq hΦ hΦ₀ (f := F) hinv
    rw [Measure.restrict_restrict_of_subset hΦs, Measure.restrict_restrict_of_subset hΦ₀s] at key
    exact key

  obtain ⟨R₀, hR₀⟩ := hT
  refine ⟨R₀, fun R hR => ?_⟩
  have hTR : Integrable (fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ξ' p.2 * (Kσ p.1 p.2 - IND R p.1 p.2)) ((Haar.restrict Φ₀).prod (νZL.restrict ΩL)) := by
    have := hR₀ R hR
    rw [IntegrableOn, ← Measure.prod_restrict] at this
    exact this
  rw [hdom]
  exact integral_integral_sub_of_split (Haar.restrict Φ₀) (νZL.restrict ΩL) ξ' Kσ CE HU (IND R)
    hsplit hCEint hTR

end Main

end R3TwCoarse

end

section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in
p2m_open "AutomorphicForm~ideleNorm_det_globalPoints" in

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
    (hφf : IsFactorizableTestFn L φ) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (@AutomorphicForm.lambdaT _
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
              (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (fun y => AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ) φ x y)
              (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
      (∫ x in ΦL, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
              (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
              LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      ∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
                (γ ∈ AutomorphicForm.hyperbolicCell K ∨ γ ∈ AutomorphicForm.unipotentCell K) ∧
                LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
              Set.indicator
                (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y =>
                    AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ) φ x y))
                (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by
  exact R3TwCoarse.main K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen ξL hξc hξt φ hφ hφc
    (fun R x z =>
      Set.indicator
        (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y =>
            AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ) φ x y))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))
    (AutomorphicForm.exists_forall_le_integrableOn_mul_lambdaT_twistedAdelicKernel_canonicalTruncationDomain_prod
      K L α β hα hαβ νZL ΩL hΩL D σ ξL hξc hξt φ hφ hφc hφf)

end

end S_AutomorphicForm_exists_forall_le_setIntegral_lambdaT_twistedAdelicKernel_sub_centralElliptic_eq_setIntegral_parabolic
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_le_setIntegral_lambdaT_twistedAdelicKernel_sub_centralElliptic_eq_setIntegral_parabolic (solution)
