-- Prove2me | solution 1 for AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b105ad1b-6af6-5723-83c8-9f0bd7c92149

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Theorems.Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_isFundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalConstituent.rightRegular_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one"
p2m_attr_erase "simp" "LanglandsTunnell.ComplexArchParam.mk.injEq AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.TateLocal.conductorExponentAt_one"

set_option autoImplicit false

open AutomorphicForm

noncomputable section

namespace ArchCutLanding

variable {H G : Type*} [Group H] [Group G]

section Cosets

variable (ι : H →* G)

private noncomputable def _root_.ArchCutLanding.rep (x : G) : G := (QuotientGroup.mk x : G ⧸ ι.range).out

p2m_export "ArchCutLanding" "rep"
private theorem rep_spec (x : G) : (rep ι x)⁻¹ * x ∈ ι.range := by
  have h : (QuotientGroup.mk (rep ι x) : G ⧸ ι.range) = QuotientGroup.mk x := by
    unfold rep
    exact QuotientGroup.out_eq' _
  exact QuotientGroup.eq.mp h

private theorem rep_mul (x : G) (h : H) : rep ι (x * ι h) = rep ι x := by
  unfold rep
  congr 1
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  rw [inv_mul_cancel_left]
  exact ⟨h, rfl⟩

private noncomputable def cok (x : G) : H := (rep_spec ι x).choose

private theorem cok_spec (x : G) : ι (cok ι x) = (rep ι x)⁻¹ * x := (rep_spec ι x).choose_spec

private theorem rep_mul_cok (x : G) : rep ι x * ι (cok ι x) = x := by
  rw [cok_spec, mul_inv_cancel_left]

variable {ι}

private theorem cok_mul (hι : Function.Injective ι) (x : G) (h : H) :
    cok ι (x * ι h) = cok ι x * h := by
  apply hι
  rw [map_mul, cok_spec, cok_spec, rep_mul, mul_assoc]

end Cosets

section Extend

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem exists_extend_equivariant {ι : H →* G} (hι : Function.Injective ι)
    (ρ' : Representation ℂ H V) (A : Submodule ℂ V) (hA : ∀ (h : H), ∀ a ∈ A, ρ' h a ∈ A)
    (M₀ : A →ₗ[ℂ] (G → ℂ))
    (hM₀ : ∀ (h : H) (a : A) (x : G), M₀ ⟨ρ' h a, hA h a a.2⟩ x = M₀ a (x * ι h)) :
    ∃ M : V →ₗ[ℂ] (G → ℂ), IsRightEquivariant ι ρ' M ∧ ∀ a : A, M a = M₀ a := by
  obtain ⟨M₁, hM₁⟩ := LinearMap.exists_extend M₀
  have hM₁' : ∀ a : A, M₁ a = M₀ a := fun a => by
    rw [← hM₁]
    rfl
  let M : V →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun v x => M₁ (ρ' (cok ι x) v) (rep ι x)
      map_add' := fun v w => by
        funext x
        simp only [map_add, Pi.add_apply]
      map_smul' := fun c v => by
        funext x
        simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
  refine ⟨M, ?_, ?_⟩
  · intro h v x
    show M₁ (ρ' (cok ι x) (ρ' h v)) (rep ι x) = M₁ (ρ' (cok ι (x * ι h)) v) (rep ι (x * ι h))
    rw [cok_mul hι, rep_mul, map_mul, Module.End.mul_apply]
  · intro a
    funext x
    show M₁ (ρ' (cok ι x) a) (rep ι x) = M₀ a x
    have h1 : M₁ (ρ' (cok ι x) a) = M₀ ⟨ρ' (cok ι x) a, hA (cok ι x) a a.2⟩ :=
      hM₁' ⟨ρ' (cok ι x) a, hA (cok ι x) a a.2⟩
    rw [h1, hM₀, rep_mul_cok]

end Extend

section FunctionSpace

variable (ι : H →* G)

private def regRep : Representation ℂ H (G → ℂ) where
  toFun k :=
    { toFun := fun u x => u (x * ι k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := LinearMap.ext fun u => funext fun x => by simp
  map_mul' a b := LinearMap.ext fun u => funext fun x => by simp [mul_assoc]

variable {ι}

private theorem exists_linear_equivariant_extension (hι : Function.Injective ι) (N : Submodule ℂ (G → ℂ))
    (hN : ∀ (k : H), ∀ u ∈ N, (fun x => u (x * ι k)) ∈ N) (Φ : (G → ℂ) → (G → ℂ))
    (hadd : ∀ u ∈ N, ∀ u' ∈ N, Φ (u + u') = Φ u + Φ u')
    (hsmul : ∀ (c : ℂ), ∀ u ∈ N, Φ (c • u) = c • Φ u)
    (hequiv : ∀ (k : H), ∀ u ∈ N, Φ (fun x => u (x * ι k)) = fun x => Φ u (x * ι k)) :
    ∃ Ψ : (G → ℂ) →ₗ[ℂ] (G → ℂ),
      (∀ (k : H) (u : G → ℂ), Ψ (fun x => u (x * ι k)) = fun x => Ψ u (x * ι k)) ∧ ∀ u ∈ N, Ψ u = Φ u := by
  have hN' : ∀ (k : H), ∀ u ∈ N, regRep ι k u ∈ N := fun k u hu => hN k u hu
  let M₀ : N →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun u => Φ u
      map_add' := fun u v => hadd u u.2 v v.2
      map_smul' := fun c u => hsmul c u u.2 }
  have hM₀ : ∀ (k : H) (u : N) (x : G), M₀ ⟨regRep ι k u, hN' k u u.2⟩ x = M₀ u (x * ι k) := by
    intro k u x
    exact congrFun (hequiv k u u.2) x
  obtain ⟨Ψ, hΨ, hΨN⟩ := exists_extend_equivariant hι (regRep ι) N hN' M₀ hM₀
  exact ⟨Ψ, fun k u => funext fun x => hΨ k u x, fun u hu => hΨN ⟨u, hu⟩⟩

private theorem typeSubmodule_le_comap {Ψ : (G → ℂ) →ₗ[ℂ] (G → ℂ)}
    (hΨ : ∀ (k : H) (u : G → ℂ), Ψ (fun x => u (x * ι k)) = fun x => Ψ u (x * ι k))
    {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W) :
    typeSubmodule ι ρ ≤ (typeSubmodule ι ρ).comap Ψ := by
  unfold typeSubmodule
  refine Submodule.span_le.mpr ?_
  rintro f ⟨T, hT, hmem⟩
  obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hmem
  have hcomp : IsRightEquivariant ι ρ (Ψ.comp T) := by
    intro k w x
    have h1 : T (ρ k w) = fun y => T w (y * ι k) := funext fun y => hT k w y
    show Ψ (T (ρ k w)) x = Ψ (T w) (x * ι k)
    rw [h1]
    exact congrFun (hΨ k (T w)) x
  exact mem_typeSubmodule_of_isRightEquivariant hcomp v

private theorem iSup_typeSubmodule_le_comap {Ψ : (G → ℂ) →ₗ[ℂ] (G → ℂ)}
    (hΨ : ∀ (k : H) (u : G → ℂ), Ψ (fun x => u (x * ι k)) = fun x => Ψ u (x * ι k))
    {κ : Type*} {W : κ → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i)) :
    (⨆ i, typeSubmodule ι (ρ i)) ≤ (⨆ i, typeSubmodule ι (ρ i)).comap Ψ :=
  iSup_le fun i =>
    (typeSubmodule_le_comap hΨ (ρ i)).trans (Submodule.comap_mono (le_iSup (fun j => typeSubmodule ι (ρ j)) i))

private theorem map_mem_iSup_typeSubmodule (hι : Function.Injective ι) (N : Submodule ℂ (G → ℂ))
    (hN : ∀ (k : H), ∀ u ∈ N, (fun x => u (x * ι k)) ∈ N) (Φ : (G → ℂ) → (G → ℂ))
    (hadd : ∀ u ∈ N, ∀ u' ∈ N, Φ (u + u') = Φ u + Φ u')
    (hsmul : ∀ (c : ℂ), ∀ u ∈ N, Φ (c • u) = c • Φ u)
    (hequiv : ∀ (k : H), ∀ u ∈ N, Φ (fun x => u (x * ι k)) = fun x => Φ u (x * ι k))
    {κ : Type*} {W : κ → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i)) {u : G → ℂ} (hu : u ∈ ⨆ i, typeSubmodule ι (ρ i)) (huN : u ∈ N) :
    Φ u ∈ ⨆ i, typeSubmodule ι (ρ i) := by
  obtain ⟨Ψ, hΨ, hΨN⟩ := exists_linear_equivariant_extension hι N hN Φ hadd hsmul hequiv
  rw [← hΨN u huN]
  exact iSup_typeSubmodule_le_comap hΨ ρ hu

end FunctionSpace

section Pins

open NumberField

variable (F : Type) [Field F] [NumberField F]

private theorem archComponent_glArch_rowIsometryInclAt₀ (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    AdelicLevel.archComponent F w (AdelicLevel.glArch (𝓞 F) F (rowIsometryInclAt₀ F w k))
      = (k : GL (Fin 2) w.Completion) := by
  rw [glArch_rowIsometryInclAt₀]
  exact archComponent_archGLIncl_self F w (k : GL (Fin 2) w.Completion)

private theorem rowIsometryInclAt₀_injective (w : InfinitePlace F) :
    Function.Injective (rowIsometryInclAt₀ F w) := by
  intro a b h
  have ha := archComponent_glArch_rowIsometryInclAt₀ F w a
  have hb := archComponent_glArch_rowIsometryInclAt₀ F w b
  rw [h] at ha
  exact Subtype.ext (ha.symm.trans hb)

private theorem map_mem_archCutSubmodule (N : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hN : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ u ∈ N,
      (fun x => u (x * rowIsometryInclAt₀ F w k)) ∈ N)
    (Φ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (hadd : ∀ u ∈ N, ∀ u' ∈ N, Φ (u + u') = Φ u + Φ u')
    (hsmul : ∀ (c : ℂ), ∀ u ∈ N, Φ (c • u) = c • Φ u)
    (hequiv : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ u ∈ N,
      Φ (fun x => u (x * rowIsometryInclAt₀ F w k)) = fun x => Φ u (x * rowIsometryInclAt₀ F w k))
    (tys : ArchTypeFamily F) {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : u ∈ archCutSubmodule F tys) (huN : u ∈ N) :
    Φ u ∈ archCutSubmodule F tys := by
  unfold archCutSubmodule at hu ⊢
  rw [Submodule.mem_iInf] at hu ⊢
  intro w
  have hw := hu w
  unfold archTypeSubmoduleAt at hw ⊢
  exact map_mem_iSup_typeSubmodule (rowIsometryInclAt₀_injective F w) N (hN w) Φ hadd hsmul (hequiv w)
    (fun i => (tys.rep w i).ρ) hw huN

end Pins

section ConvAlgebra

open MeasureTheory

variable {G : Type*} [Group G]

private theorem conv_integrand_eq (u θ : G → ℂ) (k y x : G) :
    u (y * k * (k⁻¹ * x)) * θ (k⁻¹ * x)⁻¹ = u (y * x) * θ (x⁻¹ * k) := by
  rw [mul_assoc, mul_inv_cancel_left, mul_inv_rev, inv_inv]

variable [MeasurableSpace G] (μ : Measure G) (u : G → ℂ)

private def convDomain : Submodule ℂ (G → ℂ) where
  carrier := {θ | ∀ y : G, Integrable (fun x => u (y * x) * θ x⁻¹) μ}
  zero_mem' := by
    intro y
    simp
  add_mem' := by
    intro θ₁ θ₂ h₁ h₂ y
    have e : (fun x => u (y * x) * (θ₁ + θ₂) x⁻¹) =
        fun x => u (y * x) * θ₁ x⁻¹ + u (y * x) * θ₂ x⁻¹ :=
      funext fun x => by simp only [Pi.add_apply, mul_add]
    rw [e]
    exact (h₁ y).add (h₂ y)
  smul_mem' := by
    intro c θ h y
    have e : (fun x => u (y * x) * (c • θ) x⁻¹) = fun x => c * (u (y * x) * θ x⁻¹) :=
      funext fun x => by simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    rw [e]
    exact (h y).const_mul c

private theorem mem_convDomain_iff (θ : G → ℂ) :
    θ ∈ convDomain μ u ↔ ∀ y : G, Integrable (fun x => u (y * x) * θ x⁻¹) μ :=
  Iff.rfl

private def convFn (θ : G → ℂ) : G → ℂ :=
  fun y => ∫ x, u (y * x) * θ x⁻¹ ∂μ

private theorem convFn_add {θ₁ θ₂ : G → ℂ} (h₁ : θ₁ ∈ convDomain μ u) (h₂ : θ₂ ∈ convDomain μ u) :
    convFn μ u (θ₁ + θ₂) = convFn μ u θ₁ + convFn μ u θ₂ := by
  funext y
  have e : (fun x => u (y * x) * (θ₁ + θ₂) x⁻¹) = fun x => u (y * x) * θ₁ x⁻¹ + u (y * x) * θ₂ x⁻¹ :=
    funext fun x => by simp only [Pi.add_apply, mul_add]
  show (∫ x, u (y * x) * (θ₁ + θ₂) x⁻¹ ∂μ) = (∫ x, u (y * x) * θ₁ x⁻¹ ∂μ) + ∫ x, u (y * x) * θ₂ x⁻¹ ∂μ
  rw [e, integral_add (h₁ y) (h₂ y)]

private theorem convFn_smul (c : ℂ) (θ : G → ℂ) : convFn μ u (c • θ) = c • convFn μ u θ := by
  funext y
  have e : (fun x => u (y * x) * (c • θ) x⁻¹) = fun x => c * (u (y * x) * θ x⁻¹) :=
    funext fun x => by simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
  show (∫ x, u (y * x) * (c • θ) x⁻¹ ∂μ) = c * ∫ x, u (y * x) * θ x⁻¹ ∂μ
  rw [e, integral_const_mul]

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

private theorem comp_mul_mem_convDomain {θ : G → ℂ} (hθ : θ ∈ convDomain μ u) (k : G) :
    (fun x => θ (x * k)) ∈ convDomain μ u := by
  rw [mem_convDomain_iff] at hθ ⊢
  intro y
  refine ((hθ (y * k)).comp_mul_left k⁻¹).congr (Filter.Eventually.of_forall fun x => ?_)
  exact conv_integrand_eq u θ k y x

private theorem convFn_comp_mul (θ : G → ℂ) (k : G) :
    convFn μ u (fun x => θ (x * k)) = fun y => convFn μ u θ (y * k) := by
  funext y
  show (∫ x, u (y * x) * θ (x⁻¹ * k) ∂μ) = ∫ x, u (y * k * x) * θ x⁻¹ ∂μ
  rw [← integral_mul_left_eq_self (fun x => u (y * k * x) * θ x⁻¹) k⁻¹]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (conv_integrand_eq u θ k y x).symm)

end ConvAlgebra

section ArchCutMembership

open MeasureTheory NumberField

variable (F : Type) [Field F] [NumberField F]

private theorem isFactorizableTestFn_of_isUnitFactorizableAboveOfType
    {tys : ArchTypeFamily F} {U : Subgroup (AdelicGL2 (𝓞 F) F)}
    {SK : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsUnitFactorizableAboveOfType F F tys U SK φ) : IsFactorizableTestFn F φ := by
  obtain ⟨φa, φf, φS, h₁, h₂, -, -, -, h₆⟩ := hφ.1.2
  exact ⟨φa, φf, h₁, h₂, h₆⟩

private theorem rightConv_mem_archCutSubmodule {tys : ArchTypeFamily F} {U : Subgroup (AdelicGL2 (𝓞 F) F)}
    {SK : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F))} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsUnitFactorizableAboveOfType F F tys U SK φ) {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : Continuous u) :
    rightConv F u φ ∈ archCutSubmodule F tys := by
  obtain ⟨hφc, hφs⟩ :=
    continuous_and_hasCompactSupport_of_isFactorizableTestFn F φ
      (isFactorizableTestFn_of_isUnitFactorizableAboveOfType F hφ)
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set μ : Measure (AdelicGL2 (𝓞 F) F) := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  have hdom : (fun x => φ x⁻¹) ∈ convDomain μ u := by
    rw [mem_convDomain_iff]
    intro y
    simp only [inv_inv]
    exact ((hu.comp (continuous_const.mul continuous_id)).mul hφc).integrable_of_hasCompactSupport
      hφs.mul_left
  have hconv : convFn μ u (fun x => φ x⁻¹) = rightConv F u φ := by
    funext y
    show (∫ x, u (y * x) * φ x⁻¹⁻¹ ∂μ) = ∫ x, u (y * x) * φ x ∂μ
    simp only [inv_inv]
  rw [← hconv]
  refine map_mem_archCutSubmodule F (convDomain μ u) ?_ (convFn μ u) ?_ ?_ ?_ tys hφ.2.1 hdom
  · intro w k θ hθ
    exact comp_mul_mem_convDomain μ u hθ _
  · intro θ₁ h₁ θ₂ h₂
    exact convFn_add μ u h₁ h₂
  · intro c θ _
    exact convFn_smul μ u c θ
  · intro w k θ _
    exact convFn_comp_mul μ u θ _

end ArchCutMembership

end ArchCutLanding

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.SmoothCusp HeckeIntegralSeam FLT.SmoothVectors

noncomputable section

namespace SpanClause

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

variable (F : Type) [Field F] [NumberField F]

private abbrev pinsOf (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) : CarrierPins F :=
  productionPinsOf F D U gen (adelicBox F)

private abbrev boxMeasure : Measure (AdeleRing (𝓞 F) F) :=
  ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)

variable {F}

section Clauses

private theorem isLsXi_add {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ} {u v : AdelicGL2 (𝓞 F) F → ℂ}
    (hu : IsLsXiFunction (𝓞 F) F Z ξ u) (hv : IsLsXiFunction (𝓞 F) F Z ξ v) :
    IsLsXiFunction (𝓞 F) F Z ξ (u + v) :=
  ⟨fun γ g => by simp only [Pi.add_apply, hu.left_invariant, hv.left_invariant],
    fun z g => by simp only [Pi.add_apply, hu.central_transform, hv.central_transform, mul_add]⟩

private theorem isLsXi_smul {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ} (c : ℂ)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsLsXiFunction (𝓞 F) F Z ξ u) :
    IsLsXiFunction (𝓞 F) F Z ξ (c • u) :=
  ⟨fun γ g => by simp only [Pi.smul_apply, hu.left_invariant],
    fun z g => by simp only [Pi.smul_apply, hu.central_transform, smul_eq_mul, mul_left_comm]⟩

private theorem mem_stabilizer_iff_forall {u : AdelicGL2 (𝓞 F) F → ℂ} (k : finiteAdelicGL2Subgroup F) :
    k ∈ MulAction.stabilizer (finiteAdelicGL2Subgroup F)
        (RightTranslationFn.mk u : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) ↔
      ∀ x, u (x * (k : AdelicGL2 (𝓞 F) F)) = u x := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro hk x
    exact congrArg (fun f : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ => RightTranslationFn.toFun f x) hk
  · intro hk
    exact RightTranslationFn.ext fun x => hk x

private theorem isKfSmooth_add {u v : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsKfSmooth F u) (hv : IsKfSmooth F v) :
    IsKfSmooth F (u + v) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer] at hu hv ⊢
  refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer _ (RightTranslationFn.mk u) ⊓
    MulAction.stabilizer _ (RightTranslationFn.mk v)) ?_ (hu.inter hv)
  intro k hk
  rw [mem_stabilizer_iff_forall]
  intro x
  simp only [Pi.add_apply, (mem_stabilizer_iff_forall k).1 (Subgroup.mem_inf.1 hk).1 x,
    (mem_stabilizer_iff_forall k).1 (Subgroup.mem_inf.1 hk).2 x]

private theorem isKfSmooth_smul (c : ℂ) {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsKfSmooth F u) :
    IsKfSmooth F (c • u) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer] at hu ⊢
  refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer _ (RightTranslationFn.mk u)) ?_ hu
  intro k hk
  rw [mem_stabilizer_iff_forall]
  intro x
  simp only [Pi.smul_apply, (mem_stabilizer_iff_forall k).1 hk x]

variable (F) in

private theorem integrable_unipotent_translate {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : Continuous u)
    (g : AdelicGL2 (𝓞 F) F) : Integrable (fun q => u (unipotentGL2 q * g)) (boxMeasure F) := by
  have hcont : Continuous fun q : AdeleRing (𝓞 F) F => u (unipotentGL2 q * g) :=
    hu.comp (continuous_unipotentGL2.mul continuous_const)
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  have hint : IntegrableOn (fun q => u (unipotentGL2 q * g)) (adelicBox F) (adelicAddHaar (𝓞 F) F) :=
    (hcont.continuousOn.integrableOn_compact hC).mono_set hsub
  obtain ⟨O, hO, hOne, hOsub⟩ := exists_isOpen_subset_adelicBox F
  have hpos : adelicAddHaar (𝓞 F) F (adelicBox F) ≠ 0 :=
    ((hO.measure_pos (adelicAddHaar (𝓞 F) F) hOne).trans_le (measure_mono hOsub)).ne'
  simp only [boxMeasure, ProbabilityTheory.cond]
  exact hint.smul_measure (ENNReal.inv_ne_top.2 hpos)

variable (F) in
private theorem isCuspidalFn_add {u v : AdelicGL2 (𝓞 F) F → ℂ} (hu : Continuous u) (hv : Continuous v)
    (hcu : IsCuspidalFn (boxMeasure F) unipotentGL2 u) (hcv : IsCuspidalFn (boxMeasure F) unipotentGL2 v) :
    IsCuspidalFn (boxMeasure F) unipotentGL2 (u + v) := by
  intro g
  have h1 := hcu g
  have h2 := hcv g
  simp only [constantTerm, constantTermIntegrand, Pi.add_apply] at h1 h2 ⊢
  rw [integral_add (integrable_unipotent_translate F hu g) (integrable_unipotent_translate F hv g), h1, h2,
    add_zero]

variable (F) in
private theorem isCuspidalFn_smul (c : ℂ) {u : AdelicGL2 (𝓞 F) F → ℂ}
    (hcu : IsCuspidalFn (boxMeasure F) unipotentGL2 u) : IsCuspidalFn (boxMeasure F) unipotentGL2 (c • u) := by
  intro g
  have h1 := hcu g
  simp only [constantTerm, constantTermIntegrand, Pi.smul_apply, smul_eq_mul] at h1 ⊢
  rw [integral_const_mul, h1, mul_zero]

private theorem smoothCusp_add {D : Set (AdelicGL2 (𝓞 F) F)} {U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)}
    {gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F} {ξ : (pinsOf F D U gen).Z →* ℂˣ}
    {u v : AdelicGL2 (𝓞 F) F → ℂ} (hcu : Continuous u) (hcv : Continuous v)
    (hu : IsSmoothCuspAutomorphicFnAt F (pinsOf F D U gen) ξ u)
    (hv : IsSmoothCuspAutomorphicFnAt F (pinsOf F D U gen) ξ v) :
    IsSmoothCuspAutomorphicFnAt F (pinsOf F D U gen) ξ (u + v) := by
  obtain ⟨⟨hua, hucusp⟩, huk⟩ := hu
  obtain ⟨⟨hva, hvcusp⟩, hvk⟩ := hv
  have hua' := (lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _).1 hua
  have hva' := (lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _).1 hva
  refine ⟨⟨(lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _).2 ⟨isLsXi_add hua'.1 hva'.1, hua'.2.add hva'.2⟩, ?_⟩,
    isKfSmooth_add huk hvk⟩
  exact isCuspidalFn_add F hcu hcv hucusp hvcusp

private theorem smoothCusp_smul {D : Set (AdelicGL2 (𝓞 F) F)} {U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)}
    {gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F} {ξ : (pinsOf F D U gen).Z →* ℂˣ} (c : ℂ)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : IsSmoothCuspAutomorphicFnAt F (pinsOf F D U gen) ξ u) :
    IsSmoothCuspAutomorphicFnAt F (pinsOf F D U gen) ξ (c • u) := by
  obtain ⟨⟨hua, hucusp⟩, huk⟩ := hu
  have hua' := (lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _).1 hua
  refine ⟨⟨(lsXiMemberAt_iff (𝓞 F) F _ _ _ _ _).2 ⟨isLsXi_smul c hua'.1, hua'.2.const_smul c⟩, ?_⟩,
    isKfSmooth_smul c huk⟩
  exact isCuspidalFn_smul F c hucusp

end Clauses

section SpanMembers

variable {D : Set (AdelicGL2 (𝓞 F) F)} {U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)}
  {gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F} {ξ : (pinsOf F D U gen).Z →* ℂˣ} {N : Ideal (𝓞 F)}
  {S : Finset (HeightOneSpectrum (𝓞 F))} {Ψ : HeckeEigensystem F ℂ} {u : AdelicGL2 (𝓞 F) F → ℂ}

private theorem continuous_and_smoothCusp_of_mem (hu : u ∈ isotypicCuspSubmodule F (pinsOf F D U gen) ξ N S Ψ) :
    Continuous u ∧ IsSmoothCuspAutomorphicFnAt F (pinsOf F D U gen) ξ u := by
  refine Submodule.span_induction (p := fun u _ => Continuous u ∧
    IsSmoothCuspAutomorphicFnAt F (pinsOf F D U gen) ξ u) ?_ ?_ ?_ ?_ hu
  · exact fun φ hφ => ⟨hφ.continuous, hφ.smoothCusp⟩
  · exact ⟨continuous_zero, isSmoothCuspAutomorphicFnAt_zero F _ ξ⟩
  · intro x y _ _ hx hy
    exact ⟨hx.1.add hy.1, smoothCusp_add hx.1 hy.1 hx.2 hy.2⟩
  · intro c x _ hx
    exact ⟨hx.1.const_smul c, smoothCusp_smul c hx.2⟩

private theorem level_of_mem (hu : u ∈ isotypicCuspSubmodule F (pinsOf F D U gen) ξ N S Ψ) :
    ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U N, u (g * k) = u g := by
  refine Submodule.span_induction (p := fun u _ => ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U N, u (g * k) = u g)
    ?_ ?_ ?_ ?_ hu
  · exact fun φ hφ => hφ.level_invariant
  · intro g k _; rfl
  · intro x y _ _ hx hy g k hk
    simp only [Pi.add_apply, hx g k hk, hy g k hk]
  · intro c x _ hx g k hk
    simp only [Pi.smul_apply, hx g k hk]

private theorem central_of_mem (hu : u ∈ isotypicCuspSubmodule F (pinsOf F D U gen) ξ N S Ψ) :
    ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ g : AdelicGL2 (𝓞 F) F,
      u (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det (gen v)) * g) = Ψ.toRawCentral.b v * u g := by
  refine Submodule.span_induction (p := fun u _ => ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
    ∀ g : AdelicGL2 (𝓞 F) F, u (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det (gen v)) * g)
      = Ψ.toRawCentral.b v * u g) ?_ ?_ ?_ ?_ hu
  · exact fun φ hφ => hφ.central_eigen
  · intro v _ g; simp
  · intro x y _ _ hx hy v hv g
    simp only [Pi.add_apply, hx v hv g, hy v hv g, mul_add]
  · intro c x _ hx v hv g
    simp only [Pi.smul_apply, hx v hv g, smul_eq_mul, mul_left_comm]

private theorem hecke_of_mem (hu : u ∈ isotypicCuspSubmodule F (pinsOf F D U gen) ξ N S Ψ) :
    ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      ∀ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
        IsHeckeCosetSystem (U N) (gen v) reps → ∀ g, heckeCosetSum F reps u g = Ψ.a v * u g := by
  refine Submodule.span_induction (p := fun u _ => ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
    ∀ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
      IsHeckeCosetSystem (U N) (gen v) reps → ∀ g, heckeCosetSum F reps u g = Ψ.a v * u g) ?_ ?_ ?_ ?_ hu
  · intro φ hφ v hv reps hreps g
    obtain ⟨r, hr, hφr⟩ := hφ.hecke_eigen v hv
    have hind : heckeCosetSum F reps φ g = heckeCosetSum F r φ g := by
      simp only [heckeCosetSum]
      exact heckeCosetSum_eq_of_isHeckeCosetSystem hr hreps hφ.level_invariant g
    rw [hind]
    exact hφr g
  · intro v _ reps _ g
    simp [heckeCosetSum]
  · intro x y _ _ hx hy v hv reps hreps g
    have hx' := hx v hv reps hreps g
    have hy' := hy v hv reps hreps g
    simp only [heckeCosetSum, Pi.add_apply] at hx' hy' ⊢
    rw [Finset.sum_add_distrib, hx', hy', mul_add]
  · intro c x _ hx v hv reps hreps g
    have hx' := hx v hv reps hreps g
    simp only [heckeCosetSum, Pi.smul_apply, smul_eq_mul] at hx' ⊢
    rw [← Finset.mul_sum, hx', mul_left_comm]

end SpanMembers

section SpanReturn

private theorem mem_isotypicCuspSubmodule_of_mem_of_mem {D D' : Set (AdelicGL2 (𝓞 F) F)}
    {U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)} {gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F}
    (ξ : (pinsOf F D U gen).Z →* ℂˣ) (N : Ideal (𝓞 F)) {P P' : Finset (HeightOneSpectrum (𝓞 F))}
    (Ψ : HeckeEigensystem F ℂ) {u : AdelicGL2 (𝓞 F) F → ℂ}
    (hu : u ∈ isotypicCuspSubmodule F (pinsOf F D U gen) ξ N P' Ψ)
    (hu' : u ∈ isotypicCuspSubmodule F (pinsOf F D' U gen) ξ N P Ψ) :
    u ∈ isotypicCuspSubmodule F (pinsOf F D U gen) ξ N P Ψ := by
  by_cases h0 : u = 0
  · rw [h0]; exact Submodule.zero_mem _
  have hne : {φ | IsIsotypicCuspFormAt F (pinsOf F D' U gen) ξ N P Ψ φ}.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hbot : u ∈ (⊥ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) := by
      have h := hu'
      simp only [isotypicCuspSubmodule, hempty, Submodule.span_empty] at h
      exact h
    exact h0 ((Submodule.mem_bot ℂ).1 hbot)
  obtain ⟨φ₀, hφ₀⟩ := hne
  obtain ⟨hcont, hsc⟩ := continuous_and_smoothCusp_of_mem hu
  unfold isotypicCuspSubmodule
  refine Submodule.subset_span ⟨hsc, hcont, level_of_mem hu, ?_, central_of_mem hu'⟩
  intro v hv
  obtain ⟨r, hr, -⟩ := hφ₀.hecke_eigen v hv
  exact ⟨r, hr, hecke_of_mem hu' v hv r hr⟩

end SpanReturn

end SpanClause

end

section ConvOne

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp
open AutomorphicForm IsDedekindDomain MeasureTheory FLT.SmoothVectors
open scoped ProbabilityTheory

noncomputable section

namespace SlabWindowTransport

private abbrev pinsL (L : Type) [Field L] [NumberField L] (X : Set (AdelicGL2 (𝓞 L) L)) : CarrierPins L :=
  productionPinsOf L X (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
    (adelicBox L)

private abbrev window (L : Type) [Field L] [NumberField L] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) :
    Set (AdelicGL2 (𝓞 L) L) :=
  ⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂

section Pins

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem mem_Z (X : Set (AdelicGL2 (𝓞 L) L)) (z : (AdeleRing (𝓞 L) L)ˣ) : z ∈ (pinsL L X).Z := by
  show z ∈ (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)
  exact Subgroup.mem_top z

private def toZ (X : Set (AdelicGL2 (𝓞 L) L)) (z : (AdeleRing (𝓞 L) L)ˣ) : (pinsL L X).Z := ⟨z, mem_Z X z⟩

@[scoped simp] private theorem coe_toZ (X : Set (AdelicGL2 (𝓞 L) L)) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((toZ X z : (pinsL L X).Z) : (AdeleRing (𝓞 L) L)ˣ) = z := rfl

private theorem toZ_coe (X : Set (AdelicGL2 (𝓞 L) L)) (z : (pinsL L X).Z) : toZ X (z : (AdeleRing (𝓞 L) L)ˣ) = z :=
  Subtype.ext rfl

end Pins

section Interchange

private noncomputable def integralCLM {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (ρ : Measure Y) [IsFiniteMeasure ρ] :
    C(Y, ℂ) →L[ℝ] ℂ :=
  haveI : IsFiniteMeasureOnCompacts ρ :=
    isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace.mp inferInstance
  have hint : ∀ F : C(Y, ℂ), Integrable (fun y => F y) ρ := fun F =>
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  LinearMap.mkContinuous
    { toFun := fun F => ∫ y, F y ∂ρ
      map_add' := fun F₁ F₂ => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (hint F₁) (hint F₂)
      map_smul' := fun r F => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul r fun y => F y }
    (ρ.real Set.univ) fun F => by
      refine (norm_integral_le_of_norm_le_const (μ := ρ)
        (Filter.Eventually.of_forall fun y => F.norm_coe_le_norm y)).trans ?_
      rw [mul_comm]

private theorem integralCLM_apply {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (ρ : Measure Y) [IsFiniteMeasure ρ]
    (F : C(Y, ℂ)) : integralCLM ρ F = ∫ y, F y ∂ρ :=
  rfl

section Slices

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {Q : Type*} [TopologicalSpace Q] (S : Set Q)
  {u : Q → G} (hu : Continuous u) {φ : G → ℂ} (hφ : Continuous φ) {f : G → ℂ} (hf : Continuous f)
  (g : G)

private def sliceFn : C(G × S, ℂ) :=
  ⟨fun p => φ (u p.2 * g * p.1) * f p.1, by fun_prop⟩

private noncomputable def slice (x : G) : C(S, ℂ) :=
  (sliceFn S hu hφ hf g).curry x

private theorem slice_apply (x : G) (q : S) : slice S hu hφ hf g x q = φ (u q * g * x) * f x :=
  rfl

private theorem continuous_slice : Continuous (slice S hu hφ hf g) :=
  (sliceFn S hu hφ hf g).curry.continuous

private theorem hasCompactSupport_slice (hfs : HasCompactSupport f) :
    HasCompactSupport (slice S hu hφ hf g) := by
  refine hfs.mono fun x hx => ?_
  rw [Function.mem_support] at hx ⊢
  intro hfx
  apply hx
  ext q
  rw [slice_apply, hfx, mul_zero, ContinuousMap.zero_apply]

end Slices

private theorem integral_integral_eq_zero
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {Q : Type*} [TopologicalSpace Q] [T2Space Q] [MeasurableSpace Q] [OpensMeasurableSpace Q]
    (ν : Measure Q) [IsFiniteMeasure ν] {S : Set Q} (hS : IsCompact S) (hνS : ∀ᵐ q ∂ν, q ∈ S)
    {u : Q → G} (hu : Continuous u) {φ : G → ℂ} (hφ : Continuous φ) {f : G → ℂ}
    (hf : Continuous f) (hfs : HasCompactSupport f) (g : G)
    (hzero : ∀ h : G, ∫ q, φ (u q * h) ∂ν = 0) :
    ∫ q, (∫ x, φ (u q * g * x) * f x ∂μ) ∂ν = 0 := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hres : ν.restrict S = ν := Measure.restrict_eq_self_of_ae_mem hνS

  have hsub : ∀ h : Q → ℂ, ∫ q : S, h q ∂(ν.comap Subtype.val) = ∫ q, h q ∂ν := fun h => by
    rw [integral_subtype_comap hSm, hres]
  have hΦi : Integrable (slice S hu hφ hf g) μ :=
    (continuous_slice S hu hφ hf g).integrable_of_hasCompactSupport
      (hasCompactSupport_slice S hu hφ hf g hfs)

  have hJΦ : ∀ x, integralCLM (ν.comap (Subtype.val : S → Q)) (slice S hu hφ hf g x) = 0 :=
    fun x => by
      rw [integralCLM_apply]
      simp only [slice_apply]
      rw [hsub fun q => φ (u q * g * x) * f x, integral_mul_const]
      simp only [mul_assoc]
      rw [hzero (g * x), zero_mul]

  have hev : ∀ q : S, (∫ x, slice S hu hφ hf g x ∂μ) q = ∫ x, φ (u q * g * x) * f x ∂μ :=
    fun q => by
      rw [ContinuousMap.integral_apply hΦi q]
      simp only [slice_apply]
  calc ∫ q, (∫ x, φ (u q * g * x) * f x ∂μ) ∂ν
      = ∫ q : S, (∫ x, slice S hu hφ hf g x ∂μ) q ∂(ν.comap (Subtype.val : S → Q)) := by
        rw [← hsub fun q => ∫ x, φ (u q * g * x) * f x ∂μ]
        exact integral_congr_ae (Filter.Eventually.of_forall fun q => (hev q).symm)
    _ = integralCLM (ν.comap (Subtype.val : S → Q)) (∫ x, slice S hu hφ hf g x ∂μ) :=
        (integralCLM_apply _ _).symm
    _ = ∫ x, integralCLM (ν.comap (Subtype.val : S → Q)) (slice S hu hφ hf g x) ∂μ :=
        (ContinuousLinearMap.integral_comp_comm _ hΦi).symm
    _ = 0 := by simp only [hJΦ, integral_zero]

end Interchange

section Conv

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem isFactorizableTestFn_of_isUnitFactorizableAboveOfType
    {tys : ArchTypeFamily L} {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys U SK φ) : IsFactorizableTestFn L φ := by
  obtain ⟨φa, φf, φS, h₁, h₂, -, -, -, h₆⟩ := hφ.1.2
  exact ⟨φa, φf, h₁, h₂, h₆⟩

private theorem rightConv_mul_eq_of_isUnitFactorizableAboveOfType
    {tys : ArchTypeFamily L} {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys U SK φ) (u : AdelicGL2 (𝓞 L) L → ℂ)
    (g : AdelicGL2 (𝓞 L) L) {k : AdelicGL2 (𝓞 L) L} (hk : k ∈ U) :
    rightConv L u φ (g * k) = rightConv L u φ g := by
  rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply L u φ g k]
  have hφk : (fun y => φ (k⁻¹ * y)) = φ := funext fun y => (hφ.1.1 k⁻¹ (inv_mem hk) y).1
  rw [hφk]

private theorem measurableSet_window (c v d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) :
    (letI := glBorel (Fin 2) (𝓞 L) L; MeasurableSet (window L c v d₁ d₂ T)) := by
  letI := glBorel (Fin 2) (𝓞 L) L
  haveI := borelSpace_glBorel (Fin 2) (𝓞 L) L
  refine Finset.measurableSet_biUnion T fun x _ => ?_
  have himg : (· * x) '' centreCutSiegelSet L c v d₁ d₂ = (· * x⁻¹) ⁻¹' centreCutSiegelSet L c v d₁ d₂ := by
    ext g
    simp [Set.mem_preimage]
  rw [himg]
  exact measurable_mul_const x⁻¹ (measurableSet_centreCutSiegelSet (F := L) c v d₁ d₂)

private theorem measure_window_lt_top {c : ℝ} (hc : 0 < c) (v : ℝ) {d₁ : ℝ} (hd₁ : 0 < d₁) (d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 L) L)) :
    (letI := glBorel (Fin 2) (𝓞 L) L; adelicGLHaar (Fin 2) (𝓞 L) L (window L c v d₁ d₂ T) < ⊤) := by
  letI := glBorel (Fin 2) (𝓞 L) L
  refine (measure_biUnion_finset_le T _).trans_lt (ENNReal.sum_lt_top.mpr fun x _ => ?_)
  exact adelicGLHaar_mul_right_centreCutSiegelSet_lt_top L hc v hd₁ d₂ x

private theorem isIsotypicCuspFormAt_rightConv_of_hecke_slab
    (c v d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (Sdom : Set (AdelicGL2 (𝓞 L) L))
    (hR : ∀ (χ : (pinsL L Sdom).Z →* ℂˣ) (ψ : AdelicGL2 (𝓞 L) L → ℂ),
      IsCuspAutomorphicFnAt L (pinsL L Sdom) χ ψ → Continuous ψ →
      ∀ f : AdelicGL2 (𝓞 L) L → ℂ, IsFactorizableTestFn L f → IsBoundedOnSiegelWindows L (rightConv L ψ f))
    (ξ : (pinsL L (window L c v d₁ d₂ T)).Z →* ℂˣ) (ξ' : (pinsL L Sdom).Z →* ℂˣ)
    (hξ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ' (toZ _ z) = ξ (toZ _ z))
    {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 L))) (Ψ : HeckeEigensystem L ℂ)
    {tys : ArchTypeFamily L} {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : IsIsotypicCuspFormAt L (pinsL L Sdom) ξ' N S Ψ u)
    (hhecke : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      IsHeckeCosetEigenfunctionAt L ((pinsL L (window L c v d₁ d₂ T)).U N) ((pinsL L (window L c v d₁ d₂ T)).gen w)
        w (rightConv L u φ) (Ψ.a w)) :
    IsIsotypicCuspFormAt L (pinsL L (window L c v d₁ d₂ T)) ξ N S Ψ (rightConv L u φ) := by
  have hfact : IsFactorizableTestFn L φ := isFactorizableTestFn_of_isUnitFactorizableAboveOfType hφ
  obtain ⟨hφc, hφs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ hfact
  have hucont : Continuous u := hu.continuous
  letI : MeasurableSpace (AdelicGL2 (𝓞 L) L) := glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := adeleBorel (𝓞 L) L
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := borelSpace_adeleBorel (𝓞 L) L
  haveI : IsProbabilityMeasure ((adelicAddHaar (𝓞 L) L)[|adelicBox L]) :=
    isProbabilityMeasure_cond_adelicBox L

  have hls : IsLsXiFunction (𝓞 L) L (pinsL L Sdom).Z ξ' u :=
    ((lsXiMemberAt_iff (𝓞 L) L _ _ ξ' _ u).mp hu.smoothCusp.1.1).1

  have hlevel : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
      rightConv L u φ (g * k) = rightConv L u φ g := fun g k hk =>
    rightConv_mul_eq_of_isUnitFactorizableAboveOfType hφ u g hk

  have hcont : Continuous (rightConv L u φ) :=
    (continuous_rightConv_and_contDiff_of_isFactorizableTestFn L u hucont φ hfact).1
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hcont, hlevel, hhecke, ?_⟩
  ·

    refine (lsXiMemberAt_iff (𝓞 L) L _ _ ξ _ _).mpr ⟨⟨?_, ?_⟩, ?_⟩
    · intro γ g
      show (∫ x, u (globalPoints (𝓞 L) L γ * g * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        ∫ x, u (g * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [mul_assoc, hls.left_invariant])
    · intro z g
      have hz : ∀ y : AdelicGL2 (𝓞 L) L,
          u (centralScalar (𝓞 L) L (z : (AdeleRing (𝓞 L) L)ˣ) * y) =
            ((ξ' (toZ _ (z : (AdeleRing (𝓞 L) L)ˣ)) : ℂˣ) : ℂ) * u y :=
        fun y => hls.central_transform (toZ _ (z : (AdeleRing (𝓞 L) L)ˣ)) y
      have hval : ((ξ' (toZ _ (z : (AdeleRing (𝓞 L) L)ˣ)) : ℂˣ) : ℂ) = ((ξ z : ℂˣ) : ℂ) := by
        rw [hξ, toZ_coe]
      show (∫ x, u (centralScalar (𝓞 L) L (z : (AdeleRing (𝓞 L) L)ˣ) * g * x) * φ x
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        ((ξ z : ℂˣ) : ℂ) * ∫ x, u (g * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
      rw [← hval]
      exact (integral_congr_ae (Filter.Eventually.of_forall fun x => by
        rw [mul_assoc, hz, mul_assoc])).trans (integral_const_mul _ _)
    ·
      have hbdd : IsBoundedOnSiegelWindows L (rightConv L u φ) := hR ξ' u hu.smoothCusp.1 hucont φ hfact
      obtain ⟨C, hC⟩ := hbdd c v d₁ d₂ T hc hd₁
      have hlt : adelicGLHaar (Fin 2) (𝓞 L) L (window L c v d₁ d₂ T) < ⊤ := measure_window_lt_top hc v hd₁ d₂ T
      haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (window L c v d₁ d₂ T)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hlt⟩
      show MemLp (rightConv L u φ) 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (window L c v d₁ d₂ T))
      refine MemLp.of_bound hcont.aestronglyMeasurable C ?_
      exact ae_restrict_of_forall_mem (measurableSet_window c v d₁ d₂ T) hC
  ·
    intro g
    obtain ⟨S₀, hS₀, hBS⟩ := exists_isCompact_adelicBox_subset L
    have hνS : ∀ᵐ q ∂((adelicAddHaar (𝓞 L) L)[|adelicBox L]), q ∈ S₀ :=
      (ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox L)).mono fun q hq => hBS hq
    have hcusp : ∀ h : AdelicGL2 (𝓞 L) L,
        ∫ q, u (unipotentGL2 q * h) ∂((adelicAddHaar (𝓞 L) L)[|adelicBox L]) = 0 :=
      fun h => hu.smoothCusp.1.2 h
    show ∫ q, rightConv L u φ (unipotentGL2 q * g) ∂((adelicAddHaar (𝓞 L) L)[|adelicBox L]) = 0
    exact integral_integral_eq_zero (adelicGLHaar (Fin 2) (𝓞 L) L) ((adelicAddHaar (𝓞 L) L)[|adelicBox L]) hS₀
      hνS continuous_unipotentGL2 hucont hφc hφs g hcusp
  ·
    rw [isKfSmooth_iff, isSmoothVector_iff_exists_isOpen_subgroup]
    refine ⟨(levelOne (𝓞 L) L N).comap (finiteAdelicGL2Subgroup L).subtype, ?_, ?_⟩
    · rw [Subgroup.coe_comap, Subgroup.coe_subtype]
      exact (isOpen_levelOne (𝓞 L) L hN).preimage continuous_subtype_val
    · intro w hw
      rw [Subgroup.smul_def]
      exact RightTranslationFn.ext fun x =>
        hlevel x w (Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mp hw, w.2⟩)
  ·
    intro w hw g
    have hce : ∀ y : AdelicGL2 (𝓞 L) L,
        u (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) * y) =
          Ψ.toRawCentral.b w * u y :=
      fun y => hu.central_eigen w hw y
    show (∫ x, u (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) * g * x) * φ x
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      Ψ.toRawCentral.b w * ∫ x, u (g * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
    exact (integral_congr_ae (Filter.Eventually.of_forall fun x => by
      rw [mul_assoc, hce, mul_assoc])).trans (integral_const_mul _ _)

end Conv

end SlabWindowTransport
p2m_reactivate "P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos.SlabWindowTransport"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos.SlabWindowTransport"

end ConvOne
p2m_reactivate "P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos.SlabWindowTransport"

section ConvTwo

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.SmoothCusp AdelicDock IsDedekindDomain MeasureTheory

noncomputable section

namespace SlabWindowTransport

section OnePlace

variable {L : Type} [Field L] [NumberField L]

private def placeAt (w : HeightOneSpectrum (𝓞 L)) : GL (Fin 2) (w.adicCompletion L) →* AdelicGL2 (𝓞 L) L :=
  (finEmbed (𝓞 L) L).comp (localEmbed (𝓞 L) L w)

variable (w : HeightOneSpectrum (𝓞 L))

private theorem glArch_placeAt (m : GL (Fin 2) (w.adicCompletion L)) : glArch (𝓞 L) L (placeAt w m) = 1 :=
  glArch_finEmbed (𝓞 L) L _

private theorem finComponent_glFin_placeAt_self (m : GL (Fin 2) (w.adicCompletion L)) :
    finComponent (𝓞 L) L w (glFin (𝓞 L) L (placeAt w m)) = m := by
  show finComponent (𝓞 L) L w (glFin (𝓞 L) L (finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w m))) = m
  rw [glFin_finEmbed, finComponent_localEmbed_self]

private theorem finComponent_glFin_placeAt_of_ne (m : GL (Fin 2) (w.adicCompletion L)) {w' : HeightOneSpectrum (𝓞 L)}
    (h : w' ≠ w) : finComponent (𝓞 L) L w' (glFin (𝓞 L) L (placeAt w m)) = 1 := by
  show finComponent (𝓞 L) L w' (glFin (𝓞 L) L (finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w m))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne (𝓞 L) L w m h]

variable {w}

private theorem adelicGL2_ext {a b : AdelicGL2 (𝓞 L) L} (h₁ : glArch (𝓞 L) L a = glArch (𝓞 L) L b)
    (h₂ : ∀ w' : HeightOneSpectrum (𝓞 L),
      finComponent (𝓞 L) L w' (glFin (𝓞 L) L a) = finComponent (𝓞 L) L w' (glFin (𝓞 L) L b)) : a = b := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  refine Prod.ext ?_ ?_
  · have h := congrArg
      (fun g : GL (Fin 2) (InfiniteAdeleRing L) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j) h₁
    simpa only [glArch_apply] using h
  · refine FiniteAdeleRing.ext L fun w' => ?_
    have h := congrArg
      (fun g : GL (Fin 2) (w'.adicCompletion L) => (g : Matrix (Fin 2) (Fin 2) (w'.adicCompletion L)) i j) (h₂ w')
    simpa only [finComponent_apply, glFin_apply] using h

private theorem placeAt_mul_eq_mul_placeAt (m : GL (Fin 2) (w.adicCompletion L)) {y : AdelicGL2 (𝓞 L) L}
    (hy : finComponent (𝓞 L) L w (glFin (𝓞 L) L y) = 1) : placeAt w m * y = y * placeAt w m := by
  refine adelicGL2_ext ?_ fun w' => ?_
  · simp only [map_mul, glArch_placeAt, one_mul, mul_one]
  · simp only [map_mul]
    by_cases h : w' = w
    · subst h
      rw [finComponent_glFin_placeAt_self, hy, mul_one, one_mul]
    · rw [finComponent_glFin_placeAt_of_ne w m h, one_mul, mul_one]

private theorem finComponent_glFin_mul_inv_placeAt (x : AdelicGL2 (𝓞 L) L) :
    finComponent (𝓞 L) L w (glFin (𝓞 L) L (x * (placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L x)))⁻¹)) = 1 := by
  simp only [map_mul, map_inv, finComponent_glFin_placeAt_self, mul_inv_cancel]

private theorem heckeGen_eq_placeAt :
    heckeGen (𝓞 L) L w = placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L (heckeGen (𝓞 L) L w))) := by
  refine adelicGL2_ext ?_ fun w' => ?_
  · rw [glArch_placeAt]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [glArch_apply, Units.val_one]
    exact heckeGenAt_fst _ i j
  · by_cases h : w' = w
    · subst h
      rw [finComponent_glFin_placeAt_self]
    · rw [finComponent_glFin_placeAt_of_ne w _ h]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [finComponent_apply, glFin_apply, Units.val_one]
      exact heckeGenAt_snd_apply_of_ne _ h i j

private theorem normalise_aux {G : Type*} [Group G] {p q h y u₁ u₂ : G} (hy : y = u₁ * p⁻¹) (hq : q = p * h)
    (hcomm : q * y = y * q) : u₁ * h * u₂ = q * (y * u₂) := by
  subst hy
  calc u₁ * h * u₂ = (u₁ * p⁻¹) * (p * h) * u₂ := by group
    _ = (u₁ * p⁻¹) * q * u₂ := by rw [hq]
    _ = q * (u₁ * p⁻¹) * u₂ := by rw [← hcomm]
    _ = q * (u₁ * p⁻¹ * u₂) := by rw [mul_assoc]

private theorem mul_heckeGen_mul_eq (u₁ u₂ : AdelicGL2 (𝓞 L) L) :
    u₁ * heckeGen (𝓞 L) L w * u₂ =
      placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L u₁) *
          finComponent (𝓞 L) L w (glFin (𝓞 L) L (heckeGen (𝓞 L) L w))) *
        ((u₁ * (placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L u₁)))⁻¹) * u₂) :=
  normalise_aux rfl (by rw [map_mul, ← heckeGen_eq_placeAt])
    (placeAt_mul_eq_mul_placeAt _ (finComponent_glFin_mul_inv_placeAt u₁))

private theorem isLocalLevelOne_of_integral {N : Ideal (𝓞 L)} (hb : idealBound (𝓞 L) N w = 1)
    (M : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) (hM : ∀ i j, M i j ∈ w.adicCompletionIntegers L) :
    IsLocalLevelOne (𝓞 L) L w N M :=
  ⟨hM, by rw [hb]; exact hM 1 0, by rw [hb]; exact sub_mem (hM 1 1) (one_mem _)⟩

private theorem placeAt_mem_of_integral {N : Ideal (𝓞 L)} (hb : idealBound (𝓞 L) N w = 1)
    (m : GL (Fin 2) (w.adicCompletion L))
    (hm : ∀ i j, (m : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L)
    (hm' : ∀ i j, ((m⁻¹ : GL (Fin 2) (w.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
      w.adicCompletionIntegers L) :
    placeAt w m ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · show finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w m) ∈ levelOne (𝓞 L) L N
    rw [finEmbed_mem_levelOne_iff, localEmbed_mem_finiteLevelOne_iff, mem_localLevelOne_iff]
    exact ⟨isLocalLevelOne_of_integral hb _ hm, isLocalLevelOne_of_integral hb _ hm'⟩
  · show glArch (𝓞 L) L (placeAt w m) = 1
    exact glArch_placeAt w m

private theorem finComponent_integral_of_mem_levelOne {N : Ideal (𝓞 L)} {k : AdelicGL2 (𝓞 L) L}
    (hk : k ∈ levelOne (𝓞 L) L N) (i j : Fin 2) :
    (finComponent (𝓞 L) L w (glFin (𝓞 L) L k) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
      w.adicCompletionIntegers L := by
  rw [finComponent_apply]
  have h : (glFin (𝓞 L) L k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j ∈
      AdelicLevel.integralFiniteAdeles (𝓞 L) L :=
    (mem_finiteLevelOne_iff.mp (mem_levelOne_iff.mp hk)).1.integral i j
  exact h w

private theorem finComponent_inv_integral_of_mem_levelOne {N : Ideal (𝓞 L)} {k : AdelicGL2 (𝓞 L) L}
    (hk : k ∈ levelOne (𝓞 L) L N) (i j : Fin 2) :
    (((finComponent (𝓞 L) L w (glFin (𝓞 L) L k))⁻¹ : GL (Fin 2) (w.adicCompletion L)) :
      Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L := by
  rw [← map_inv, ← map_inv]
  exact finComponent_integral_of_mem_levelOne (inv_mem hk) i j

end OnePlace
p2m_reactivate "P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos.SlabWindowTransport"

section Hecke

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem isHeckeCosetEigenfunctionAt_rightConv {N : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)}
    (hb : idealBound (𝓞 L) N w = 1) {tys : ArchTypeFamily L} {SK : Finset (HeightOneSpectrum (𝓞 K))}
    {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (hsupp : ∀ x : AdelicGL2 (𝓞 L) L, φ x ≠ 0 →
      (∀ i j, (finComponent (𝓞 L) L w (glFin (𝓞 L) L x) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
          w.adicCompletionIntegers L) ∧
      (∀ i j, (((finComponent (𝓞 L) L w (glFin (𝓞 L) L x))⁻¹ : GL (Fin 2) (w.adicCompletion L)) :
          Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L))
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hucont : Continuous u)
    (hinv : ∀ h : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, u (h * k) = u h)
    {a : ℂ}
    (heu : IsHeckeCosetEigenfunctionAt L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (heckeGen (𝓞 L) L w) w
      u a) :
    IsHeckeCosetEigenfunctionAt L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (heckeGen (𝓞 L) L w) w
      (rightConv L u φ) a := by
  obtain ⟨reps, hsys, heig⟩ := heu
  obtain ⟨hφc, hφs⟩ :=
    continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ
      (isFactorizableTestFn_of_isUnitFactorizableAboveOfType hφ)
  letI : MeasurableSpace (AdelicGL2 (𝓞 L) L) := glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L

  have hdc : ∀ i, ∃ u₁ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
      ∃ u₂ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, u₁ * heckeGen (𝓞 L) L w * u₂ = reps i :=
    fun i => HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
  choose u₁ hu₁ u₂ hu₂ hrep using hdc

  obtain ⟨r, hr⟩ : ∃ r : Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L, ∀ i,
      r i = placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L (u₁ i)) *
        finComponent (𝓞 L) L w (glFin (𝓞 L) L (heckeGen (𝓞 L) L w))) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L, ∀ i,
      s i = (u₁ i * (placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L (u₁ i))))⁻¹) * u₂ i :=
    ⟨_, fun _ => rfl⟩
  have hreps : reps = fun i => r i * s i := funext fun i => by
    show reps i = r i * s i
    rw [← hrep i, hr, hs]
    exact mul_heckeGen_mul_eq (u₁ i) (u₂ i)
  have hsU : ∀ i, s i ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := fun i => by
    rw [hs]
    have hp : placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L (u₁ i))) ∈
        levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L :=
      placeAt_mem_of_integral hb _ (finComponent_integral_of_mem_levelOne (Subgroup.mem_inf.mp (hu₁ i)).1)
        (finComponent_inv_integral_of_mem_levelOne (Subgroup.mem_inf.mp (hu₁ i)).1)
    exact mul_mem (mul_mem (hu₁ i) (inv_mem hp)) (hu₂ i)

  have heig' : ∀ h : AdelicGL2 (𝓞 L) L, (∑ i, u (h * r i)) = a * u h := fun h => by
    have h1 := heig h
    rw [hreps, heckeCosetSum_mul_right L (fun g k hk => hinv g k hk) r s hsU h] at h1
    exact h1

  have hlevel : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
      rightConv L u φ (g * k) = rightConv L u φ g := fun g k hk =>
    rightConv_mul_eq_of_isUnitFactorizableAboveOfType hφ u g hk

  have hL1 : ∀ h : AdelicGL2 (𝓞 L) L,
      Integrable (fun x => u (h * x) * φ x) (adelicGLHaar (Fin 2) (𝓞 L) L) := fun h =>
    ((hucont.comp (continuous_const.mul continuous_id)).mul hφc).integrable_of_hasCompactSupport hφs.mul_left

  have hpt : ∀ (g x : AdelicGL2 (𝓞 L) L), (∑ i, u (g * r i * x) * φ x) = a * (u (g * x) * φ x) := by
    intro g x
    by_cases hx : φ x = 0
    · simp only [hx, mul_zero, Finset.sum_const_zero]
    obtain ⟨hx₁, hx₂⟩ := hsupp x hx
    have hxw : placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L x)) ∈
        levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L :=
      placeAt_mem_of_integral hb _ hx₁ hx₂

    obtain ⟨x', hx'⟩ : ∃ x' : AdelicGL2 (𝓞 L) L,
        x' = x * (placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L x)))⁻¹ := ⟨_, rfl⟩
    have hxx : x = x' * placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L x)) := by
      rw [hx', inv_mul_cancel_right]
    have hx'w : finComponent (𝓞 L) L w (glFin (𝓞 L) L x') = 1 := by
      rw [hx']
      exact finComponent_glFin_mul_inv_placeAt x
    have hterm : ∀ i, u (g * r i * x) = u (g * x' * r i) := fun i => by
      have hcr : r i * x' = x' * r i := by
        rw [hr]
        exact placeAt_mul_eq_mul_placeAt _ hx'w
      rw [hxx, ← mul_assoc, hinv _ _ hxw, mul_assoc, hcr, ← mul_assoc]
    rw [← Finset.sum_mul, ← mul_assoc]
    congr 1
    simp only [hterm]
    rw [heig' (g * x'), hxx, ← mul_assoc, hinv _ _ hxw]

  refine ⟨reps, hsys, fun g => ?_⟩
  have hsum : heckeCosetSum L reps (rightConv L u φ) g = heckeCosetSum L r (rightConv L u φ) g := by
    rw [hreps]
    exact heckeCosetSum_mul_right L (fun h k hk => hlevel h k hk) r s hsU g
  rw [hsum]
  show (∑ i, ∫ x, u (g * r i * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
    a * ∫ x, u (g * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
  have hswap : (∑ i, ∫ x, u (g * r i * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      ∫ x, (∑ i, u (g * r i * x) * φ x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) :=
    (integral_finsetSum Finset.univ fun i _ => hL1 (g * r i)).symm
  have hpt' : (∫ x, (∑ i, u (g * r i * x) * φ x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      ∫ x, a * (u (g * x) * φ x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => hpt g x)
  rw [hswap, hpt', integral_const_mul]

end Hecke
p2m_reactivate "P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos.SlabWindowTransport"

end SlabWindowTransport
p2m_reactivate "P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos.SlabWindowTransport"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos.SlabWindowTransport"

end ConvTwo
p2m_reactivate "P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos.SlabWindowTransport"

section ConvThree

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp
open AutomorphicForm IsDedekindDomain MeasureTheory
open scoped TensorProduct
open scoped TensorProduct.RightActions

noncomputable section

namespace SlabWindowTransport

section Dictionary

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

private theorem semiLocalHomeomorph_semiLocalEval (a : FiniteAdeleRing (𝓞 L) L) (w : v.Extension (𝓞 L)) :
    semiLocalHomeomorph K L v (semiLocalEval K L v a) w = AdelicLevel.finAdeleEval (𝓞 L) L w.1 a := by
  show HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
      ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w' : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w'.1 a)) w =
    AdelicLevel.finAdeleEval (𝓞 L) L w.1 a
  rw [AlgEquiv.apply_symm_apply]

private theorem forall_of_mem_semiLocalIntegers (t : L ⊗[K] v.adicCompletion K) (ht : t ∈ semiLocalIntegers K L v)
    (w : v.Extension (𝓞 L)) : semiLocalHomeomorph K L v t w ∈ w.1.adicCompletionIntegers L := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi] at ht
  exact ht w

end Dictionary
p2m_reactivate "P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos.SlabWindowTransport"

section Discharge

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem finComponent_integral_of_ne_zero {tys : ArchTypeFamily L} {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys U SK φ) {w : HeightOneSpectrum (𝓞 L)}
    (hw : w.under (𝓞 K) ∉ SK) (x : AdelicGL2 (𝓞 L) L) (hx : φ x ≠ 0) :
      (∀ i j, (finComponent (𝓞 L) L w (glFin (𝓞 L) L x) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
          w.adicCompletionIntegers L) ∧
      (∀ i j, (((finComponent (𝓞 L) L w (glFin (𝓞 L) L x))⁻¹ : GL (Fin 2) (w.adicCompletion L)) :
          Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L)
    := by
  obtain ⟨φa, φf, φS, -, -, -, -, h₅, h₆⟩ := hφ.1.2
  have hf : φf (glFin (𝓞 L) L x) ≠ 0 := fun h0 => hx (by rw [h₆ x, h0, mul_zero])
  have hmem : semiLocalComponent K L (w.under (𝓞 K)) (glFin (𝓞 L) L x) ∈
      semiLocalIntegralSet K L (w.under (𝓞 K)) := by
    by_contra hc
    exact hf (h₅ _ ⟨w.under (𝓞 K), hw, hc⟩)
  unfold semiLocalIntegralSet at hmem
  obtain ⟨hm, hm'⟩ := mem_integralUnitsSet.mp hmem

  let wE : {w' : HeightOneSpectrum (𝓞 L) // w'.under (𝓞 K) = w.under (𝓞 K)} := ⟨w, rfl⟩
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have h : semiLocalHomeomorph K L (w.under (𝓞 K))
        (semiLocalEval K L (w.under (𝓞 K))
          ((glFin (𝓞 L) L x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j)) wE ∈
        w.adicCompletionIntegers L :=
      forall_of_mem_semiLocalIntegers K L (w.under (𝓞 K)) _ (hm i j) wE
    rw [semiLocalHomeomorph_semiLocalEval] at h
    exact h
  · have hm'' := hm' i j
    rw [← map_inv (semiLocalComponent K L (w.under (𝓞 K))) (glFin (𝓞 L) L x)] at hm''
    have h : semiLocalHomeomorph K L (w.under (𝓞 K))
        (semiLocalEval K L (w.under (𝓞 K))
          ((((glFin (𝓞 L) L x)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j)) wE ∈
        w.adicCompletionIntegers L :=
      forall_of_mem_semiLocalIntegers K L (w.under (𝓞 K)) _ hm'' wE
    rw [semiLocalHomeomorph_semiLocalEval] at h
    rw [← map_inv (finComponent (𝓞 L) L w) (glFin (𝓞 L) L x)]
    exact h

private theorem isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAboveOfType_slab
    (c v d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (Sdom : Set (AdelicGL2 (𝓞 L) L))
    (hR : ∀ (χ : (pinsL L Sdom).Z →* ℂˣ) (ψ : AdelicGL2 (𝓞 L) L → ℂ),
      IsCuspAutomorphicFnAt L (pinsL L Sdom) χ ψ → Continuous ψ →
      ∀ f : AdelicGL2 (𝓞 L) L → ℂ, IsFactorizableTestFn L f → IsBoundedOnSiegelWindows L (rightConv L ψ f))
    (ξ : (pinsL L (window L c v d₁ d₂ T)).Z →* ℂˣ) (ξ' : (pinsL L Sdom).Z →* ℂˣ)
    (hξ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ' (toZ _ z) = ξ (toZ _ z))
    {NK : Ideal (𝓞 K)} (hN : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥)
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {SL : Finset (HeightOneSpectrum (𝓞 L))}
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∈ SK → w ∈ SL)
    (hbound : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
      idealBound (𝓞 L) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) w = 1)
    (Ψ : HeckeEigensystem L ℂ) {tys : ArchTypeFamily L} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys
      (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ)
    {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : IsIsotypicCuspFormAt L (pinsL L Sdom) ξ'
      (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ u) :
    IsIsotypicCuspFormAt L (pinsL L (window L c v d₁ d₂ T)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
      (rightConv L u φ) :=
  isIsotypicCuspFormAt_rightConv_of_hecke_slab c v d₁ d₂ T hc hd₁ Sdom hR ξ ξ' hξ hN SL Ψ hφ hu
    fun w hw =>
      isHeckeCosetEigenfunctionAt_rightConv (hbound w hw) hφ
        (fun x hx => finComponent_integral_of_ne_zero hφ (fun h => hw (hSL w h)) x hx)
        hu.continuous hu.level_invariant (hu.hecke_eigen w hw)

end Discharge
p2m_reactivate "P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos.SlabWindowTransport"

end SlabWindowTransport
p2m_reactivate "P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos.SlabWindowTransport"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos.SlabWindowTransport"

end ConvThree
p2m_reactivate "P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos.SlabWindowTransport"

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm.WindowedSiegel
open Filter Topology AutomorphicForm AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace SlabWindowInclusion

variable (F : Type) [Field F] [NumberField F]

private abbrev pinsAt (D : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
    (adelicBox F)

private abbrev win (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F) :=
  ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂

private abbrev Wcut (S D : Set (AdelicGL2 (𝓞 F) F)) (ξ : (pinsAt F S).Z →* ℂˣ) (N : Ideal (𝓞 F))
    (P : Finset (HeightOneSpectrum (𝓞 F))) (tys : ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  isotypicCuspSubmodule F (pinsAt F D) ξ N P Ψ ⊓ archCutSubmodule F tys

variable {F}

private theorem level_invariant_of_mem {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 F)}
    {P : Finset (HeightOneSpectrum (𝓞 F))} {Ψ : HeckeEigensystem F ℂ} {w : AdelicGL2 (𝓞 F) F → ℂ}
    (hw : w ∈ isotypicCuspSubmodule F pins ξ N P Ψ) :
    ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ pins.U N, w (g * k) = w g := by
  refine Submodule.span_induction (p := fun w _ => ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ pins.U N,
    w (g * k) = w g) ?_ ?_ ?_ ?_ hw
  · exact fun φ hφ => hφ.level_invariant
  · intro g k _; rfl
  · intro u v _ _ hu hv g k hk
    simp only [Pi.add_apply, hu g k hk, hv g k hk]
  · intro c u _ hu g k hk
    simp only [Pi.smul_apply, hu g k hk]

private theorem isFactorizableTestFn_of_isUnitFactorizableAboveOfType
    {tys : ArchTypeFamily F} {U : Subgroup (AdelicGL2 (𝓞 F) F)}
    {SK : Finset (HeightOneSpectrum (𝓞 F))} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsUnitFactorizableAboveOfType F F tys U SK φ) : IsFactorizableTestFn F φ := by
  obtain ⟨φa, φf, φS, h₁, h₂, -, -, -, h₆⟩ := hφ.1.2
  exact ⟨φa, φf, h₁, h₂, h₆⟩

variable (F) in
omit [NumberField F] in

private theorem under_self (w : HeightOneSpectrum (𝓞 F)) : w.under (𝓞 F) = w := by
  ext1
  simp [HeightOneSpectrum.under, Ideal.under, Ideal.comap_id]

variable (F) in

private theorem exists_primeSupport (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) :
    ∃ SK : Finset (HeightOneSpectrum (𝓞 F)), ∀ p : HeightOneSpectrum (𝓞 F), p.asIdeal ∣ N → p ∈ SK := by
  have hfin : {p : HeightOneSpectrum (𝓞 F) | p.asIdeal ∣ N}.Finite := Ideal.finite_factors hN
  exact ⟨hfin.toFinset, fun p hp => hfin.mem_toFinset.mpr hp⟩

variable (F) in

private theorem approxIdentity_self (N : Ideal (𝓞 F)) (SK : Finset (HeightOneSpectrum (𝓞 F)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 F), p.asIdeal ∣ N → p ∈ SK)
    (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f)
    (hlev : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, f (g * k) = f g)
    (harch : f ∈ archCutSubmodule F tys) :
    ∃ φ : ℕ → (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ n, IsUnitFactorizableAboveOfType F F tys (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) SK (φ n)) ∧
      ∀ g, Tendsto (fun n => rightConv F f (φ n) g) atTop (𝓝 (f g)) := by
  have hI : Ideal.map (@algebraMap (𝓞 F) (𝓞 F) _ _ (inst_ringOfIntegersAlgebra F F)) N = N := by
    have hh : @algebraMap (𝓞 F) (𝓞 F) _ _ (inst_ringOfIntegersAlgebra F F) = RingHom.id (𝓞 F) :=
      RingHom.ext fun _ => rfl
    rw [hh, Ideal.map_id]
  have h := exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
    F F N SK hNS tys f hf (by simpa only [hI] using hlev) harch
  simpa only [hI] using h

private theorem isIsotypicCuspFormAt_mono {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 F)}
    {P P' : Finset (HeightOneSpectrum (𝓞 F))} (h : P ⊆ P') {Ψ : HeckeEigensystem F ℂ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsIsotypicCuspFormAt F pins ξ N P Ψ φ) :
    IsIsotypicCuspFormAt F pins ξ N P' Ψ φ :=
  ⟨hφ.smoothCusp, hφ.continuous, hφ.level_invariant, fun v hv => hφ.hecke_eigen v fun h' => hv (h h'),
    fun v hv => hφ.central_eigen v fun h' => hv (h h')⟩

private theorem le_of_isBoundedOnSiegelWindows
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (S : Set (AdelicGL2 (𝓞 F) F))
    (hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf F S
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (P : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (hR : ∀ (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
      (χ : (productionPinsOf F S U gen (adelicBox F)).Z →* ℂˣ) (ψ : AdelicGL2 (𝓞 F) F → ℂ),
      IsCuspAutomorphicFnAt F (productionPinsOf F S U gen (adelicBox F)) χ ψ → Continuous ψ →
      ∀ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f → IsBoundedOnSiegelWindows F (rightConv F ψ f)) :
    (isotypicCuspSubmodule F
        (productionPinsOf F S
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ N P Ψ
      ⊓ archCutSubmodule F tys)
      ≤
    (isotypicCuspSubmodule F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ N P Ψ
      ⊓ archCutSubmodule F tys) := by
  classical
  have _ := hα; have _ := hαβ; have _ := hS
  obtain ⟨Ts, cs, hcs, us, hcov⟩ :=
    SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet F
  have hcov12 : CoversModCentre F (win F cs us 1 2 Ts) := hcov 1 2 two_pos one_le_two
  obtain ⟨SK, hNS⟩ := exists_primeSupport F N hN
  have hSKP : ∀ v ∈ SK, v ∈ P ∪ SK := fun v hv => Finset.mem_union_right P hv
  have hmapN : Ideal.map (algebraMap (𝓞 F) (𝓞 F)) N = N := by
    have hh : algebraMap (𝓞 F) (𝓞 F) = RingHom.id _ := RingHom.ext fun _ => rfl
    rw [hh, Ideal.map_id]
  have hM : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ,
      IsUnitFactorizableAboveOfType F F tys (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) SK φ →
      ∀ (c' u' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 F) F)), 0 < c' → 0 < d₁' →
      ∀ v, IsIsotypicCuspFormAt F (pinsAt F S) ξ N (P ∪ SK) Ψ v →
        IsIsotypicCuspFormAt F (pinsAt F (win F c' u' d₁' d₂' T')) ξ N (P ∪ SK) Ψ (rightConv F v φ) := by
    intro φ hφ c' u' d₁' d₂' T' hc' hd₁' v hv
    have hN' : Ideal.map (algebraMap (𝓞 F) (𝓞 F)) N ≠ ⊥ := by rwa [hmapN]
    have hφ' : IsUnitFactorizableAboveOfType F F tys
        (levelOne (𝓞 F) F (Ideal.map (algebraMap (𝓞 F) (𝓞 F)) N) ⊓ finiteAdelicGL2Subgroup F) SK φ := by
      rwa [hmapN]
    have hv' : IsIsotypicCuspFormAt F (pinsAt F S) ξ (Ideal.map (algebraMap (𝓞 F) (𝓞 F)) N) (P ∪ SK) Ψ v := by
      rwa [hmapN]
    have hSL : ∀ w : HeightOneSpectrum (𝓞 F), w.under (𝓞 F) ∈ SK → w ∈ P ∪ SK := fun w hw =>
      hSKP w (by rwa [under_self F w] at hw)
    have hbound : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ P ∪ SK →
        idealBound (𝓞 F) (Ideal.map (algebraMap (𝓞 F) (𝓞 F)) N) w = 1 := fun w hw =>
      idealBound_eq_one_of_not_dvd hN' fun hdvd => hw (hSKP w (hNS w (by rwa [hmapN] at hdvd)))
    have key :=
      SlabWindowTransport.isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAboveOfType_slab (K := F) (L := F)
      c' u' d₁' d₂' T' hc' hd₁' S
      (hR (fun M => levelOne (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v))
      ξ ξ (fun _ => rfl) hN' hSL hbound Ψ hφ' hv'
    have hI : Ideal.map (@algebraMap (𝓞 F) (𝓞 F) _ _ (inst_ringOfIntegersAlgebra F F)) N = N := by
      have hh : @algebraMap (𝓞 F) (𝓞 F) _ _ (inst_ringOfIntegersAlgebra F F) = RingHom.id (𝓞 F) :=
        RingHom.ext fun _ => rfl
      rw [hh, Ideal.map_id]
    simpa only [hI] using key
  haveI hfinΩs : FiniteDimensional ℂ ↥(Wcut F S (win F cs us 1 2 Ts) ξ N (P ∪ SK) tys Ψ) :=
    finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule F cs us 1 2 Ts one_lt_two hcov12 ξ N hN
      (P ∪ SK) tys Ψ
  haveI hfinE : FiniteDimensional ℂ
      ↥(Wcut F S (win F c u d₁ d₂ T) ξ N (P ∪ SK) tys Ψ ⊓ Wcut F S (win F cs us 1 2 Ts) ξ N (P ∪ SK) tys Ψ) :=
    Submodule.finiteDimensional_of_le inf_le_right
  intro w hw
  obtain ⟨hwS, hwarch⟩ := hw
  have hwS' : w ∈ isotypicCuspSubmodule F (pinsAt F S) ξ N (P ∪ SK) Ψ :=
    Submodule.span_mono (fun v hv => isIsotypicCuspFormAt_mono Finset.subset_union_left hv) hwS
  have hwcont : Continuous w := continuous_of_mem_isotypicCuspSubmodule hwS
  have hwlev : ∀ g, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, w (g * k) = w g :=
    level_invariant_of_mem hwS
  obtain ⟨φ, hφ, hlim⟩ := approxIdentity_self F N SK hNS tys w hwcont hwlev hwarch
  have hφcc : ∀ n, Continuous (φ n) ∧ HasCompactSupport (φ n) := fun n =>
    continuous_and_hasCompactSupport_of_isFactorizableTestFn F (φ n)
      (isFactorizableTestFn_of_isUnitFactorizableAboveOfType (hφ n))
  have hsmooth : ∀ (n : ℕ) (c' u' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 F) F)), 0 < c' → 0 < d₁' →
      ∀ x ∈ isotypicCuspSubmodule F (pinsAt F S) ξ N (P ∪ SK) Ψ,
        Continuous x ∧ rightConv F x (φ n) ∈
          isotypicCuspSubmodule F (pinsAt F (win F c' u' d₁' d₂' T')) ξ N (P ∪ SK) Ψ := by
    intro n c' u' d₁' d₂' T' hc' hd₁' x hx
    obtain ⟨hφc, hφcs⟩ := hφcc n
    refine Submodule.span_induction
      (p := fun x _ => Continuous x ∧ rightConv F x (φ n) ∈
        isotypicCuspSubmodule F (pinsAt F (win F c' u' d₁' d₂' T')) ξ N (P ∪ SK) Ψ) ?_ ?_ ?_ ?_ hx
    · intro v hv
      exact ⟨hv.continuous,
        (hM (φ n) (hφ n) c' u' d₁' d₂' T' hc' hd₁' v hv).mem_isotypicCuspSubmodule⟩
    · refine ⟨continuous_zero, ?_⟩
      show rightConv F (fun _ => 0) (φ n) ∈ _
      rw [rightConv_zero_left]
      exact Submodule.zero_mem _
    · intro y z _ _ hy hz
      refine ⟨hy.1.add hz.1, ?_⟩
      rw [rightConv_add_left F hy.1 hz.1 hφc hφcs]
      exact Submodule.add_mem _ hy.2 hz.2
    · intro a y _ hy
      refine ⟨hy.1.const_smul a, ?_⟩
      have h := convOp_smul F (φ n) a y
      simp only [convOp_apply] at h
      rw [h]
      exact Submodule.smul_mem _ a hy.2
  have hBi : ∀ n, rightConv F w (φ n) ∈ archCutSubmodule F tys := fun n =>
    ArchCutLanding.rightConv_mem_archCutSubmodule F (hφ n) hwcont
  have hmem : ∀ n, rightConv F w (φ n) ∈
      Wcut F S (win F c u d₁ d₂ T) ξ N (P ∪ SK) tys Ψ ⊓ Wcut F S (win F cs us 1 2 Ts) ξ N (P ∪ SK) tys Ψ :=
    fun n =>
    ⟨⟨(hsmooth n c u d₁ d₂ T hc hd₁ w hwS').2, hBi n⟩, ⟨(hsmooth n cs us 1 2 Ts hcs one_pos w hwS').2, hBi n⟩⟩
  have hwE : w ∈ Wcut F S (win F c u d₁ d₂ T) ξ N (P ∪ SK) tys Ψ ⊓
      Wcut F S (win F cs us 1 2 Ts) ξ N (P ∪ SK) tys Ψ :=
    (Submodule.closed_of_finiteDimensional _).mem_of_tendsto (tendsto_pi_nhds.2 hlim)
      (eventually_atTop.2 ⟨0, fun n _ => hmem n⟩)
  exact ⟨SpanClause.mem_isotypicCuspSubmodule_of_mem_of_mem (D := win F c u d₁ d₂ T) (D' := S) ξ N Ψ
    hwE.1.1 hwS, hwarch⟩

end SlabWindowInclusion
p2m_reactivate "P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos.SlabWindowTransport"

theorem solution
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (S : Set (AdelicGL2 (𝓞 F) F))
    (hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf F S
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (P : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hc : 0 < c) (hd₁ : 0 < d₁) :
    (isotypicCuspSubmodule F
        (productionPinsOf F S
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ N P Ψ
      ⊓ archCutSubmodule F tys)
      ≤
    (isotypicCuspSubmodule F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ξ N P Ψ
      ⊓ archCutSubmodule F tys) :=
  SlabWindowInclusion.le_of_isBoundedOnSiegelWindows F α β hα hαβ S hS ξ N hN P tys Ψ c u d₁ d₂ T hc hd₁
    (AutomorphicForm.isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_isFundamentalDomain F α β
      (hα.trans hαβ) hαβ S hS)

end
p2m_reactivate "P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos.SlabWindowTransport"

#print axioms solution

end S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos
end P2MW
export P2MW.S_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_of_isFundamentalDomain_of_pos (solution)
