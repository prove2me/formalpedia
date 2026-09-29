-- Prove2me | solution 1 for AutomorphicForm.finsum_setIntegral_convOp_mul_conj_eq_cutTrace_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/384a1e6e-d376-5019-b999-20f60a5ec2d7

import Theorems.Thm_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_finsum_setIntegral_convOp_mul_conj_eq_cutTrace_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace R5CuspPrincipal

variable {L : Type} [Field L] [NumberField L]

theorem isHaar : (adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L

attribute [local instance] isHaar

theorem countable_numberField : Countable L :=
  (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance

theorem countable_gl2 : Countable (GL (Fin 2) L) := by
  haveI := countable_numberField (L := L)
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) L → _)) Units.val_injective

scoped instance countable_range : Countable (globalPoints (𝓞 L) L).range := by
  haveI := countable_gl2 (L := L)
  exact Function.Surjective.countable (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 L) L))

def slab (L : Type) [Field L] [NumberField L] (α β : ℝ) : Set (AdelicGL2 (𝓞 L) L) :=
  {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem globalPoints_mul_mem_slab_iff {α β : ℝ} (γ : GL (Fin 2) L) (x : AdelicGL2 (𝓞 L) L) :
    globalPoints (𝓞 L) L γ * x ∈ slab L α β ↔ x ∈ slab L α β := by
  simp only [slab, Set.mem_setOf_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

scoped instance smulInvariantMeasure_slab (α β : ℝ) :
    SMulInvariantMeasure (globalPoints (𝓞 L) L).range (AdelicGL2 (𝓞 L) L)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
  refine ⟨fun γ s hs => ?_⟩
  obtain ⟨g, γ₀, rfl⟩ := γ
  have hslab : MeasurableSet (slab L α β) :=
    measurableSet_Icc.preimage (NumberField.TateGlobal.continuous_ideleNorm_det L).measurable
  have hpre : (fun x : AdelicGL2 (𝓞 L) L =>
      (⟨globalPoints (𝓞 L) L γ₀, γ₀, rfl⟩ : (globalPoints (𝓞 L) L).range) • x) ⁻¹' s =
      (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' s := rfl
  rw [hpre, Measure.restrict_apply ((measurable_const_mul _) hs), Measure.restrict_apply hs]
  have hset : (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' s ∩ slab L α β =
      (fun x => globalPoints (𝓞 L) L γ₀ * x) ⁻¹' (s ∩ slab L α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, globalPoints_mul_mem_slab_iff]
  rw [hset, measure_preimage_mul]

theorem setIntegral_eq_of_isFundamentalDomain {α β : ℝ} {Φ₀ ΦL : Set (AdelicGL2 (𝓞 L) L)}
    (hΦ₀s : Φ₀ ⊆ slab L α β)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (hΦs : ΦL ⊆ slab L α β)
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)))
    (F : AdelicGL2 (𝓞 L) L → ℂ) (hF : ∀ (γ : GL (Fin 2) L) (x), F (globalPoints (𝓞 L) L γ * x) = F x) :
    ∫ x in Φ₀, F x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = ∫ x in ΦL, F x ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by
  have h := hΦ₀.setIntegral_eq hΦ (f := F) (fun γ x => by
    obtain ⟨g, γ₀, rfl⟩ := γ
    exact hF γ₀ x)
  rwa [Measure.restrict_restrict_of_subset hΦ₀s, Measure.restrict_restrict_of_subset hΦs] at h

section Members

variable {ΦL : Set (AdelicGL2 (𝓞 L) L)} {U : Ideal (𝓞 L) → Subgroup (AdelicGL2 (𝓞 L) L)}
  {gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L} {B : Set (AdeleRing (𝓞 L) L)}
  {ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ} {N : Ideal (𝓞 L)}
  {SL : Finset (HeightOneSpectrum (𝓞 L))} {π : HeckeEigensystem L ℂ}

theorem lsXiMemberAt_of_isIsotypicCuspFormAt {u : AdelicGL2 (𝓞 L) L → ℂ}
    (h : IsIsotypicCuspFormAt L (productionPinsOf L ΦL U gen B) ξL N SL π u) :
    IsLsXiFunction (𝓞 L) L ⊤ ξL u ∧ MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL) := by
  have h1 : LsXiMemberAt (𝓞 L) L (adelicGLHaar (Fin 2) (𝓞 L) L) ⊤ ξL ΦL u := h.smoothCusp.1.1
  exact (lsXiMemberAt_iff (𝓞 L) L _ ⊤ ξL ΦL u).1 h1

theorem isLsXiFunction_and_memLp_of_mem {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ isotypicCuspSubmodule L (productionPinsOf L ΦL U gen B) ξL N SL π) :
    IsLsXiFunction (𝓞 L) L ⊤ ξL u ∧ MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL) := by
  refine Submodule.span_induction (p := fun u _ =>
    IsLsXiFunction (𝓞 L) L ⊤ ξL u ∧ MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL))
    ?_ ?_ ?_ ?_ hu
  · exact fun u h => lsXiMemberAt_of_isIsotypicCuspFormAt h
  · exact ⟨⟨fun _ _ => rfl, fun _ _ => by simp⟩, MemLp.zero'⟩
  · rintro u w - - ⟨⟨hul, huc⟩, hu2⟩ ⟨⟨hwl, hwc⟩, hw2⟩
    refine ⟨⟨fun γ g => ?_, fun z g => ?_⟩, hu2.add hw2⟩
    · simp only [Pi.add_apply, hul, hwl]
    · simp only [Pi.add_apply, huc, hwc, mul_add]
  · rintro c u - ⟨⟨hul, huc⟩, hu2⟩
    refine ⟨⟨fun γ g => ?_, fun z g => ?_⟩, hu2.const_smul c⟩
    · simp only [Pi.smul_apply, hul]
    · simp only [Pi.smul_apply, huc, smul_eq_mul]
      ring

theorem isLsXiFunction_of_mem {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ isotypicCuspSubmodule L (productionPinsOf L ΦL U gen B) ξL N SL π) :
    IsLsXiFunction (𝓞 L) L ⊤ ξL u :=
  (isLsXiFunction_and_memLp_of_mem hu).1

theorem memLp_of_mem {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ isotypicCuspSubmodule L (productionPinsOf L ΦL U gen B) ξL N SL π) :
    MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL) :=
  (isLsXiFunction_and_memLp_of_mem hu).2

theorem apply_globalPoints_mul_of_mem {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ isotypicCuspSubmodule L (productionPinsOf L ΦL U gen B) ξL N SL π)
    (γ : GL (Fin 2) L) (g : AdelicGL2 (𝓞 L) L) : u (globalPoints (𝓞 L) L γ * g) = u g :=
  (isLsXiFunction_of_mem hu).left_invariant γ g

end Members

section Pairing

variable (Φ : Set (AdelicGL2 (𝓞 L) L))

def ip (u v : AdelicGL2 (𝓞 L) L → ℂ) : ℂ :=
  ∫ x in Φ, u x * conj (v x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)

variable {Φ}

theorem integrable_mul_conj {u v : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ))
    (hv : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ)) :
    Integrable (fun x => u x * conj (v x)) ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ) := by
  have hv' : MemLp (star v) 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ) := hv.star
  exact hu.integrable_mul hv'

theorem ip_add_left {u w v : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ))
    (hw : MemLp w 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ))
    (hv : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ)) :
    ip Φ (u + w) v = ip Φ u v + ip Φ w v := by
  unfold ip
  simp only [Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_conj hu hv) (integrable_mul_conj hw hv)

theorem ip_smul_left (c : ℂ) (u v : AdelicGL2 (𝓞 L) L → ℂ) :
    ip Φ (c • u) v = c * ip Φ u v := by
  unfold ip
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem ip_zero_left (v : AdelicGL2 (𝓞 L) L → ℂ) : ip Φ 0 v = 0 := by
  simp [ip]

theorem ip_sum_smul_left {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → AdelicGL2 (𝓞 L) L → ℂ)
    (v : AdelicGL2 (𝓞 L) L → ℂ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ))
    (hv : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ)) :
    ip Φ (∑ i ∈ s, c i • f i) v = ∑ i ∈ s, c i * ip Φ (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ip_zero_left]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      ip_add_left ((hf a (Finset.mem_insert_self a s)).const_smul (c a))
        (memLp_finsetSum' s fun i hi => (hf i (Finset.mem_insert_of_mem hi)).const_smul (c i)) hv,
      ip_smul_left, ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

end Pairing

theorem convOp_globalPoints_mul {ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ}
    (φ u : AdelicGL2 (𝓞 L) L → ℂ) (hu : IsLsXiFunction (𝓞 L) L ⊤ ξL u)
    (γ : GL (Fin 2) L) (x : AdelicGL2 (𝓞 L) L) :
    convOp L φ u (globalPoints (𝓞 L) L γ * x) = convOp L φ u x := by
  rw [convOp_apply, rightConv_apply, rightConv_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [mul_assoc, hu.left_invariant]

end R5CuspPrincipal
p2m_reactivate "P2MW.S_AutomorphicForm_finsum_setIntegral_convOp_mul_conj_eq_cutTrace_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R5CuspPrincipal"

end
p2m_reactivate "P2MW.S_AutomorphicForm_finsum_setIntegral_convOp_mul_conj_eq_cutTrace_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R5CuspPrincipal"

open R5CuspPrincipal in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (tys : ArchTypeFamily K)
    (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
    (hb : ∀ i, cls i ∈ cuspClasses K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S ∧
      b i ∈ isotypicCuspSubmodule K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S (cls i) ⊓ archCutSubmodule K tys)
    (hb₁ : ∀ i, ∫ g in Φ, b i g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ g in Φ, b i g * conj (b j g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0)
    (hbs : ∀ π ∈ cuspClasses K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S,
      {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π ⊓ archCutSubmodule K tys)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
    (hft : IsArchBiFinite K tys f)
    (Ψ : HeckeEigensystem K ℂ)
    (hΨ : Ψ ∈ cuspClasses K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S) :
    ∑ᶠ i : {i // cls i = Ψ},
        ∫ x in Φ₀, convOp K f (b i) x * conj (b i x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      cutTrace K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ tys f hf hfc := by
  classical
  haveI := isHaar (L := K)

  set W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := isotypicCuspSubmodule K
      (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ ⊓ archCutSubmodule K tys with hW
  set A : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) := convOp K f with hA

  obtain ⟨hfin, hspan⟩ := hbs Ψ hΨ
  haveI : Finite {i // cls i = Ψ} := hfin.to_subtype
  letI : Fintype {i // cls i = Ψ} := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]

  have hbW : ∀ i : {i // cls i = Ψ}, b i ∈ W := by
    intro i
    have h := (hb i.1).2
    rwa [i.2] at h
  have hV : ∀ u ∈ W, u ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ :=
    fun u hu => (Submodule.mem_inf.mp hu).1
  have hbV : ∀ i : ι, b i ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S (cls i) :=
    fun i => (Submodule.mem_inf.mp (hb i).2).1
  have hb2 : ∀ i : ι, MemLp (b i) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) :=
    fun i => memLp_of_mem (hbV i)
  have hip₁ : ∀ i : ι, ip Φ (b i) (b i) = 1 := fun i => hb₁ i
  have hip₀ : ∀ i j : ι, i ≠ j → ip Φ (b i) (b j) = 0 := fun i j h => hb₀ i j h

  have hFD : ∀ {u v : AdelicGL2 (𝓞 K) K → ℂ} {π π' : HeckeEigensystem K ℂ},
      u ∈ isotypicCuspSubmodule K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π →
      v ∈ isotypicCuspSubmodule K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π' →
      ∫ x in Φ₀, u x * conj (v x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = ip Φ u v := by
    intro u v π π' hu hv
    exact setIntegral_eq_of_isFundamentalDomain (α := α) (β := β) hΦ₀s hΦ₀ hΦs hΦ
      (fun x => u x * conj (v x)) fun γ x => by
        simp only [apply_globalPoints_mul_of_mem hu, apply_globalPoints_mul_of_mem hv]

  have hmaps : ∀ u ∈ W, A u ∈ W :=
    AutomorphicForm.convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
      K α β hα hαβ Φ hΦs hΦ ξ S N hN tys Ψ f hf hfc hfU hft

  have hL2 : ∀ u ∈ W, MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ) :=
    fun u hu => memLp_of_mem (hV u hu)
  rw [cutTrace_eq, convTraceOn_eq_traceOn K _ hf hfc hmaps, traceOn_eq]

  let e : {i // cls i = Ψ} → W := fun i => ⟨b i, hbW i⟩
  have hip_e : ∀ i j : {i // cls i = Ψ}, ip Φ (b j) (b i) = if j = i then 1 else 0 := by
    intro i j
    split_ifs with h
    · rw [h]; exact hip₁ i
    · exact hip₀ j i fun h' => h (Subtype.ext h')
  have hli : LinearIndependent ℂ e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg' : ∑ j, g j • b (j : ι) = 0 := by
      have := congrArg (Subtype.val : W → AdelicGL2 (𝓞 K) K → ℂ) hg
      simpa [e, Submodule.coe_sum, Submodule.coe_smul] using this
    have h := congrArg (fun u => ip Φ u (b i)) hg'
    rw [ip_sum_smul_left Finset.univ g (fun j : {i // cls i = Ψ} => b (j : ι)) (b i)
      (fun j _ => hb2 j) (hb2 i), ip_zero_left] at h
    simp only [hip_e i, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at h
    exact h
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range e) := by
    rintro w -
    have hw : (w : AdelicGL2 (𝓞 K) K → ℂ) ∈ Submodule.span ℂ (b '' {i | cls i = Ψ}) := by
      rw [hspan]; exact w.2
    have hrange : W.subtype '' Set.range e = b '' {i | cls i = Ψ} := by
      ext u
      simp only [Set.mem_image, Set.mem_range, Set.mem_setOf_eq, Submodule.coe_subtype]
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, i.2, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨e ⟨i, hi⟩, ⟨⟨i, hi⟩, rfl⟩, rfl⟩
    rw [← Submodule.apply_mem_span_image_iff_mem_span (Submodule.injective_subtype W), hrange]
    exact hw
  let B : Module.Basis {i // cls i = Ψ} ℂ W := Module.Basis.mk hli hsp
  have hB : ∀ i, B i = e i := fun i => Module.Basis.mk_apply hli hsp i

  have hcoord : ∀ (i : {i // cls i = Ψ}) (w : W), B.repr w i = ip Φ w (b i) := by
    intro i
    let fW : W →ₗ[ℂ] ℂ :=
      { toFun := fun w => ip Φ (w : AdelicGL2 (𝓞 K) K → ℂ) (b i)
        map_add' := fun w w' => by
          simp only [Submodule.coe_add]
          exact ip_add_left (hL2 _ w.2) (hL2 _ w'.2) (hb2 i)
        map_smul' := fun c w => by
          simp only [Submodule.coe_smul, RingHom.id_apply]
          exact ip_smul_left c _ _ }
    have key : B.coord i = fW := by
      refine B.ext fun j => ?_
      show (Module.Basis.mk hli hsp).coord i ((Module.Basis.mk hli hsp) j) =
        ip Φ ((Module.Basis.mk hli hsp j : W) : AdelicGL2 (𝓞 K) K → ℂ) (b i)
      rw [Module.Basis.mk_apply, Module.Basis.mk_coord_apply]
      exact (hip_e i j).symm
    intro w
    have := congrArg (fun g : W →ₗ[ℂ] ℂ => g w) key
    simp [Module.Basis.coord_apply] at this
    exact this
  rw [LinearMap.trace_eq_matrix_trace ℂ B, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hcoord, hB]
  show ∫ x in Φ₀, A (b i) x * conj (b i x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
    ip Φ (A (b i)) (b i)
  exact hFD (hV _ (hmaps _ (hbW i))) (hV _ (hbW i))

end S_AutomorphicForm_finsum_setIntegral_convOp_mul_conj_eq_cutTrace_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_finsum_setIntegral_convOp_mul_conj_eq_cutTrace_of_orthonormal_principalLevel_of_isFundamentalDomain_slab (solution)
