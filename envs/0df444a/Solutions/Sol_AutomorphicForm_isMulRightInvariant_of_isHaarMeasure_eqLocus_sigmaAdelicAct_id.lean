-- Prove2me | solution 1 for AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/420e61c1-d2d2-58bf-89c3-e6399f1dc560

import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "sigmaAdelicAct AdelicGL2"
namespace FixedSubgroupUnimodular
p2m_open "AutomorphicForm"

open NumberField TensorProduct

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (σ : L ≃ₐ[K] L)

def Fσ : Subfield L := (IntermediateField.fixedField (Subgroup.zpowers σ)).toSubfield

theorem mem_Fσ_iff (x : L) : x ∈ Fσ K L σ ↔ σ x = x := by
  show x ∈ IntermediateField.fixedField (Subgroup.zpowers σ) ↔ _
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h; exact h σ (Subgroup.mem_zpowers σ)
  · intro h f hf
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
    have : ∀ n : ℕ, (σ ^ n) x = x := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · exact_mod_cast this n
    · rw [zpow_neg, zpow_natCast]
      have h1 := this n
      calc (σ ^ n)⁻¹ x = (σ ^ n)⁻¹ ((σ ^ n) x) := by rw [h1]
        _ = x := by rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl

scoped instance : NumberField (Fσ K L σ) := inferInstance

example : Algebra (Fσ K L σ) L := inferInstance

theorem algebraMap_Fσ (x : Fσ K L σ) : algebraMap (Fσ K L σ) L x = (x : L) := rfl

def σF : L ≃ₐ[Fσ K L σ] L :=
  AlgEquiv.ofRingEquiv (f := (σ : L ≃+* L)) (fun x => (mem_Fσ_iff K L σ x).mp x.2)

@[scoped simp] theorem σF_apply (x : L) : σF K L σ x = σ x := rfl

def resK : (L ≃ₐ[Fσ K L σ] L) →* (L ≃ₐ[K] L) where
  toFun τ := AlgEquiv.ofRingEquiv (f := (τ : L ≃+* L)) (fun k => by
    have hk : algebraMap K L k ∈ Fσ K L σ := (mem_Fσ_iff K L σ _).mpr (σ.commutes k)
    exact τ.commutes (⟨algebraMap K L k, hk⟩ : Fσ K L σ))
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

@[scoped simp] theorem resK_apply (τ : L ≃ₐ[Fσ K L σ] L) (x : L) : resK K L σ τ x = τ x := rfl

theorem resK_σF : resK K L σ (σF K L σ) = σ := by ext; rfl

variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

def DF : M4aHerbrand.IdeleGaloisDescent (𝓞 L) (Fσ K L σ) L where
  act := D.act.comp (resK K L σ)
  compat g x := D.compat (resK K L σ g) x
  continuous_act g := D.continuous_act (resK K L σ g)

theorem act_eq_genuine :
    D.act σ = (M4aHerbrand.GenuineDescent.genuineDescentDatum (Fσ K L σ) L).act (σF K L σ) := by
  have h : DF K L σ D = M4aHerbrand.GenuineDescent.genuineDescentDatum (Fσ K L σ) L :=
    Subsingleton.elim (h := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) (Fσ K L σ) L) _ _
  have := congrArg (fun E : M4aHerbrand.IdeleGaloisDescent (𝓞 L) (Fσ K L σ) L => E.act (σF K L σ)) h
  simpa [DF, resK_σF] using this

end AutomorphicForm.FixedSubgroupUnimodular
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm.FixedSubgroupUnimodular"
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "sigmaAdelicAct AdelicGL2"
namespace FixedSubgroupUnimodular
p2m_open "AutomorphicForm"

open NumberField TensorProduct

section FixedTensor

variable {F L : Type*} [Field F] [Field L] [Algebra F L] (τ : L ≃ₐ[F] L)
  (hτ : ∀ x : L, τ x = x → x ∈ Set.range (algebraMap F L))
variable (M : Type*) [AddCommGroup M] [Module F M]

include hτ in
theorem exact_algebraMap_sub_id :
    Function.Exact (Algebra.linearMap F L) (τ.toLinearMap - (LinearMap.id : L →ₗ[F] L)) := by
  intro y
  simp only [LinearMap.sub_apply, AlgEquiv.toLinearMap_apply, LinearMap.id_apply, sub_eq_zero,
    Algebra.coe_linearMap]
  constructor
  · exact hτ y
  · rintro ⟨x, rfl⟩; exact τ.commutes x

include hτ in

theorem exists_eq_tmul_one_of_lTensor_eq (z : M ⊗[F] L)
    (hz : LinearMap.lTensor M τ.toLinearMap z = z) : ∃ m : M, z = m ⊗ₜ[F] (1 : L) := by
  have hex := Module.Flat.lTensor_exact M (exact_algebraMap_sub_id τ hτ)
  have h0 : LinearMap.lTensor M (τ.toLinearMap - LinearMap.id) z = 0 := by
    rw [LinearMap.lTensor_sub, LinearMap.sub_apply, hz, LinearMap.lTensor_id, LinearMap.id_apply,
      sub_self]
  obtain ⟨w, hw⟩ := (hex z).mp h0
  rw [← hw]
  clear hw h0 hz
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul m f =>
    refine ⟨f • m, ?_⟩
    rw [LinearMap.lTensor_tmul, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    obtain ⟨m₁, h₁⟩ := hx
    obtain ⟨m₂, h₂⟩ := hy
    exact ⟨m₁ + m₂, by rw [map_add, h₁, h₂, TensorProduct.add_tmul]⟩

end FixedTensor
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm.FixedSubgroupUnimodular"

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (σ : L ≃ₐ[K] L)

abbrev AF : Type := AdeleRing (𝓞 (Fσ K L σ)) (Fσ K L σ)
abbrev AL : Type := AdeleRing (𝓞 L) L

abbrev β : AF K L σ →+* AL L := M4aHerbrand.Bridge.genuineβ (Fσ K L σ) L

def θ : AL L ≃+* AL L :=
  letI := (β K L σ).toAlgebra
  M4aHerbrand.actOf (𝓞 (Fσ K L σ)) (Fσ K L σ) (𝓞 L) L
    (M4aHerbrand.Bridge.genuineTensorEquiv (Fσ K L σ) L) (σF K L σ)

theorem genuine_act_eq_θ :
    (M4aHerbrand.GenuineDescent.genuineDescentDatum (Fσ K L σ) L).act (σF K L σ) = θ K L σ := rfl

theorem hτ_σF : ∀ x : L, σF K L σ x = x → x ∈ Set.range (algebraMap (Fσ K L σ) L) := by
  intro x hx
  exact ⟨⟨x, (mem_Fσ_iff K L σ x).mpr hx⟩, rfl⟩

theorem θ_β (a : AF K L σ) : θ K L σ (β K L σ a) = β K L σ a := by
  letI := (β K L σ).toAlgebra
  set te := M4aHerbrand.Bridge.genuineTensorEquiv (Fσ K L σ) L with hte
  have h1 : β K L σ a = te (a ⊗ₜ[Fσ K L σ] (1 : L)) :=
    (M4aHerbrand.Bridge.genuineTensorEquiv_tmul_one (Fσ K L σ) L a).symm
  show te ((Algebra.TensorProduct.congr AlgEquiv.refl (σF K L σ)) (te.symm (β K L σ a))) = _
  rw [h1, AlgEquiv.symm_apply_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul]
  simp

theorem congr_refl_eq_lTensor {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [Semiring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [Semiring B] [Algebra R B] (τ : B ≃ₐ[R] B) (z : A ⊗[R] B) :
    (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[S] A) τ) z =
      LinearMap.lTensor A τ.toLinearMap z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem exists_β_eq_of_θ_eq (y : AL L) (hy : θ K L σ y = y) : ∃ a : AF K L σ, β K L σ a = y := by
  letI := (β K L σ).toAlgebra
  set te := M4aHerbrand.Bridge.genuineTensorEquiv (Fσ K L σ) L with hte
  have hy' : (Algebra.TensorProduct.congr (AlgEquiv.refl : AF K L σ ≃ₐ[AF K L σ] AF K L σ)
      (σF K L σ)) (te.symm y) = te.symm y := by
    have := congrArg te.symm hy
    conv_lhs at this =>
      rw [show θ K L σ y = te ((Algebra.TensorProduct.congr
        (AlgEquiv.refl : AF K L σ ≃ₐ[AF K L σ] AF K L σ) (σF K L σ)) (te.symm y)) from rfl]
    rwa [AlgEquiv.symm_apply_apply] at this
  rw [congr_refl_eq_lTensor] at hy'
  obtain ⟨a, ha⟩ := exists_eq_tmul_one_of_lTensor_eq (σF K L σ) (hτ_σF K L σ) (AF K L σ)
    (te.symm y) hy'
  refine ⟨a, ?_⟩
  rw [← M4aHerbrand.Bridge.genuineTensorEquiv_tmul_one (Fσ K L σ) L a, ← hte, ← ha,
    AlgEquiv.apply_symm_apply]

theorem β_injective : Function.Injective (β K L σ) := by
  letI := (β K L σ).toAlgebra
  set te := M4aHerbrand.Bridge.genuineTensorEquiv (Fσ K L σ) L with hte
  intro a b hab
  have h : te (a ⊗ₜ[Fσ K L σ] (1 : L)) = te (b ⊗ₜ[Fσ K L σ] (1 : L)) := by
    rw [hte, M4aHerbrand.Bridge.genuineTensorEquiv_tmul_one,
      M4aHerbrand.Bridge.genuineTensorEquiv_tmul_one]
    exact hab
  have h2 := te.injective h
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeLeft : AF K L σ →ₐ[Fσ K L σ] AF K L σ ⊗[Fσ K L σ] L) :=
    Algebra.TensorProduct.includeLeft_injective (S := Fσ K L σ) (algebraMap (Fσ K L σ) L).injective
  exact hinj h2

end AutomorphicForm.FixedSubgroupUnimodular
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm.FixedSubgroupUnimodular"
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm.FixedSubgroupUnimodular"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "sigmaAdelicAct AdelicGL2"
namespace FixedSubgroupUnimodular
p2m_open "AutomorphicForm"

open NumberField TensorProduct MeasureTheory MeasureTheory.Measure

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (σ : L ≃ₐ[K] L)

section Retraction

theorem linIndep_one : LinearIndepOn (Fσ K L σ) id ({1} : Set L) :=
  LinearIndepOn.singleton one_ne_zero

abbrev ιB : Type := ((linIndep_one K L σ).extend (Set.subset_univ _) : Set L)

def bL : Module.Basis (ιB K L σ) (Fσ K L σ) L := Module.Basis.extend (linIndep_one K L σ)

def i₀ : ιB K L σ := ⟨1, (linIndep_one K L σ).subset_extend (Set.subset_univ _) rfl⟩

theorem bL_i₀ : bL K L σ (i₀ K L σ) = 1 := Module.Basis.extend_apply_self _ _

scoped instance : Finite (ιB K L σ) := Module.Finite.finite_basis (bL K L σ)

abbrev algAF : Algebra (AF K L σ) (AL L) := (β K L σ).toAlgebra

attribute [local instance] algAF

def bA : Module.Basis (ιB K L σ) (AF K L σ) (AL L) :=
  (Algebra.TensorProduct.basis (AF K L σ) (bL K L σ)).map
    (M4aHerbrand.Bridge.genuineTensorEquiv (Fσ K L σ) L).toLinearEquiv

theorem bA_i₀ : bA K L σ (i₀ K L σ) = 1 := by
  rw [bA, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply, bL_i₀]
  exact map_one (M4aHerbrand.Bridge.genuineTensorEquiv (Fσ K L σ) L)

theorem β_eq_smul_one (a : AF K L σ) : β K L σ a = a • (1 : AL L) := by
  rw [Algebra.smul_def, mul_one]; rfl

def ψ₀ : AL L →ₗ[AF K L σ] AF K L σ := (bA K L σ).coord (i₀ K L σ)

theorem ψ₀_β (a : AF K L σ) : ψ₀ K L σ (β K L σ a) = a := by
  rw [β_eq_smul_one, ← bA_i₀ K L σ, ψ₀, map_smul, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]

theorem isModuleTopology_AL : IsModuleTopology (AF K L σ) (AL L) :=
  M4aHerbrand.Bridge.isModuleTopology_adeleRing_of_free (𝓞 (Fσ K L σ)) (Fσ K L σ) (𝓞 L) L
    (M4aHerbrand.Bridge.continuous_genuineβ (Fσ K L σ) L)
    (M4aHerbrand.Bridge.genuineTensorEquiv (Fσ K L σ) L)

theorem continuous_ψ₀ : Continuous (ψ₀ K L σ) := by
  haveI := isModuleTopology_AL K L σ
  exact IsModuleTopology.continuous_of_linearMap (ψ₀ K L σ)

end Retraction
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm.FixedSubgroupUnimodular"

section GroupIso

variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

abbrev GG : Type := AutomorphicForm.AdelicGL2 (𝓞 L) L

abbrev Gs : Subgroup (GG L) :=
  MonoidHom.eqLocus (AutomorphicForm.sigmaAdelicAct K L D σ) (MonoidHom.id (GG L))

theorem mem_Gs_iff (g : GG L) :
    g ∈ Gs K L σ D ↔ ∀ i j, θ K L σ (g i j) = g i j := by
  show AutomorphicForm.sigmaAdelicAct K L D σ g = g ↔ _
  rw [AutomorphicForm.sigmaAdelicAct, act_eq_genuine K L σ D, genuine_act_eq_θ]
  constructor
  · intro h i j
    have := congrArg (fun x : GG L => x i j) h
    exact this
  · intro h
    ext i j
    exact h i j

abbrev Φ : GL (Fin 2) (AF K L σ) →* GG L := Matrix.GeneralLinearGroup.map (β K L σ)

theorem Φ_mem (g : GL (Fin 2) (AF K L σ)) : Φ K L σ g ∈ Gs K L σ D := by
  rw [mem_Gs_iff]
  intro i j
  exact θ_β K L σ (g i j)

theorem Φ_apply (g : GL (Fin 2) (AF K L σ)) (i j : Fin 2) : (Φ K L σ g) i j = β K L σ (g i j) := rfl

attribute [local instance] algAF

theorem β_ψ₀_entry (x : Gs K L σ D) (i j : Fin 2) :
    β K L σ (ψ₀ K L σ ((x : GG L) i j)) = (x : GG L) i j := by
  obtain ⟨a, ha⟩ := exists_β_eq_of_θ_eq K L σ _ ((mem_Gs_iff K L σ D _).mp x.2 i j)
  rw [← ha, ψ₀_β]

theorem β_ψ₀_entry_inv (x : Gs K L σ D) (i j : Fin 2) :
    β K L σ (ψ₀ K L σ (((x : GG L)⁻¹ : GG L) i j)) = ((x : GG L)⁻¹ : GG L) i j := by
  have hx : ((x⁻¹ : Gs K L σ D) : GG L) = (x : GG L)⁻¹ := rfl
  rw [← hx]
  exact β_ψ₀_entry K L σ D x⁻¹ i j

def ΨM (x : Gs K L σ D) : Matrix (Fin 2) (Fin 2) (AF K L σ) :=
  ((x : GG L) : Matrix (Fin 2) (Fin 2) (AL L)).map (ψ₀ K L σ)

def ΨMi (x : Gs K L σ D) : Matrix (Fin 2) (Fin 2) (AF K L σ) :=
  (((x : GG L)⁻¹ : GG L) : Matrix (Fin 2) (Fin 2) (AL L)).map (ψ₀ K L σ)

theorem ΨM_map (x : Gs K L σ D) :
    (ΨM K L σ D x).map (β K L σ) = ((x : GG L) : Matrix (Fin 2) (Fin 2) (AL L)) := by
  ext i j
  exact β_ψ₀_entry K L σ D x i j

theorem ΨMi_map (x : Gs K L σ D) :
    (ΨMi K L σ D x).map (β K L σ) = (((x : GG L)⁻¹ : GG L) : Matrix (Fin 2) (Fin 2) (AL L)) := by
  ext i j
  exact β_ψ₀_entry_inv K L σ D x i j

theorem mapMatrix_injective : Function.Injective
    ((β K L σ).mapMatrix : Matrix (Fin 2) (Fin 2) (AF K L σ) →+* Matrix (Fin 2) (Fin 2) (AL L)) :=
  fun _ _ h => Matrix.map_injective (β_injective K L σ) h

theorem ΨM_mul_ΨMi (x : Gs K L σ D) : ΨM K L σ D x * ΨMi K L σ D x = 1 := by
  apply mapMatrix_injective K L σ
  rw [map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ΨM_map, ΨMi_map]
  exact (x : GG L).mul_inv

theorem ΨMi_mul_ΨM (x : Gs K L σ D) : ΨMi K L σ D x * ΨM K L σ D x = 1 := by
  apply mapMatrix_injective K L σ
  rw [map_mul, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ΨM_map, ΨMi_map]
  exact (x : GG L).inv_mul

def Ψ (x : Gs K L σ D) : GL (Fin 2) (AF K L σ) :=
  ⟨ΨM K L σ D x, ΨMi K L σ D x, ΨM_mul_ΨMi K L σ D x, ΨMi_mul_ΨM K L σ D x⟩

theorem Φ_Ψ (x : Gs K L σ D) : Φ K L σ (Ψ K L σ D x) = (x : GG L) := by
  apply Units.ext
  exact ΨM_map K L σ D x

theorem Ψ_Φ (g : GL (Fin 2) (AF K L σ)) : Ψ K L σ D ⟨Φ K L σ g, Φ_mem K L σ D g⟩ = g := by
  apply Units.ext
  ext i j
  exact ψ₀_β K L σ (g i j)

def eGs : GL (Fin 2) (AF K L σ) ≃* Gs K L σ D where
  toFun g := ⟨Φ K L σ g, Φ_mem K L σ D g⟩
  invFun := Ψ K L σ D
  left_inv g := Ψ_Φ K L σ D g
  right_inv x := Subtype.ext (Φ_Ψ K L σ D x)
  map_mul' g h := Subtype.ext (map_mul _ g h)

theorem coe_eGs (g : GL (Fin 2) (AF K L σ)) : ((eGs K L σ D g : Gs K L σ D) : GG L) = Φ K L σ g :=
  rfl

theorem continuous_Φ : Continuous (Φ K L σ) :=
  Continuous.units_map _
    (Continuous.matrix_map continuous_id (M4aHerbrand.Bridge.continuous_genuineβ (Fσ K L σ) L))

theorem continuous_eGs : Continuous (eGs K L σ D) :=
  Continuous.subtype_mk (continuous_Φ K L σ) _

theorem continuous_eGs_symm : Continuous (eGs K L σ D).symm := by
  show Continuous (Ψ K L σ D)
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun x : Gs K L σ D => ΨM K L σ D x
    exact Continuous.matrix_map (Units.continuous_val.comp continuous_subtype_val)
      (continuous_ψ₀ K L σ)
  · show Continuous fun x : Gs K L σ D => ΨMi K L σ D x
    exact Continuous.matrix_map (Units.continuous_coe_inv.comp continuous_subtype_val)
      (continuous_ψ₀ K L σ)

def eGsₜ : GL (Fin 2) (AF K L σ) ≃ₜ* Gs K L σ D :=
  { eGs K L σ D with
    continuous_toFun := continuous_eGs K L σ D
    continuous_invFun := continuous_eGs_symm K L σ D }

end GroupIso
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm.FixedSubgroupUnimodular"

section Haar

variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
variable [MeasurableSpace (GG L)] [BorelSpace (GG L)]

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem borelSpace_GLF : BorelSpace (GL (Fin 2) (AF K L σ)) :=
  NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 (Fσ K L σ)) (Fσ K L σ)

attribute [local instance] borelSpace_GLF

theorem isMulRightInvariant_GLF (ν : Measure (GL (Fin 2) (AF K L σ))) [ν.IsHaarMeasure] :
    ν.IsMulRightInvariant := by
  haveI : SecondCountableTopology (GL (Fin 2) (AF K L σ)) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo (Fσ K L σ)
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 (Fσ K L σ)) (Fσ K L σ)
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar (Fσ K L σ)
  rw [isMulLeftInvariant_eq_smul ν
    (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 (Fσ K L σ)) (Fσ K L σ))]
  infer_instance

theorem main (μ : Measure (Gs K L σ D)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  set e := eGsₜ K L σ D with he
  set ν : Measure (GL (Fin 2) (AF K L σ)) := Measure.map e.symm μ with hν
  haveI : ν.IsHaarMeasure := e.symm.isHaarMeasure_map μ
  haveI := isMulRightInvariant_GLF K L σ ν
  have hme : Measurable (e : GL (Fin 2) (AF K L σ) → Gs K L σ D) := e.continuous.measurable
  have hmes : Measurable (e.symm : Gs K L σ D → GL (Fin 2) (AF K L σ)) :=
    e.symm.continuous.measurable
  have hμ : μ = Measure.map e ν := by
    rw [hν, Measure.map_map hme hmes]
    have : (e : GL (Fin 2) (AF K L σ) → Gs K L σ D) ∘ e.symm = id := by
      funext x; exact e.apply_symm_apply x
    rw [this, Measure.map_id]
  refine ⟨fun y => ?_⟩
  rw [hμ, Measure.map_map (measurable_mul_const y) hme]
  have hcomp : (fun h : Gs K L σ D => h * y) ∘ (e : GL (Fin 2) (AF K L σ) → Gs K L σ D) =
      (e : GL (Fin 2) (AF K L σ) → Gs K L σ D) ∘ fun g => g * e.symm y := by
    funext g
    simp only [Function.comp_apply, map_mul, ContinuousMulEquiv.apply_symm_apply]
  rw [hcomp, ← Measure.map_map hme (measurable_mul_const _), map_mul_right_eq_self]

end Haar
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm.FixedSubgroupUnimodular"

end AutomorphicForm.FixedSubgroupUnimodular
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm.FixedSubgroupUnimodular"
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm.FixedSubgroupUnimodular"

open MeasureTheory NumberField in
theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    [MeasurableSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L)]
    [BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L)]
    (μ : Measure (MonoidHom.eqLocus (AutomorphicForm.sigmaAdelicAct K L D σ)
        (MonoidHom.id (AutomorphicForm.AdelicGL2 (𝓞 L) L))))
    [μ.IsHaarMeasure] : μ.IsMulRightInvariant :=
  AutomorphicForm.FixedSubgroupUnimodular.main K L σ D μ

end
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.AutomorphicForm.FixedSubgroupUnimodular"

end S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id
end P2MW
export P2MW.S_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id (solution)
