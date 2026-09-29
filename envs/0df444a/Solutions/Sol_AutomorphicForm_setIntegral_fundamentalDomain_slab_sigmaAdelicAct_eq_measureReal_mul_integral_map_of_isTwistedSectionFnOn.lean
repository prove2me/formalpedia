-- Prove2me | solution 1 for AutomorphicForm.setIntegral_fundamentalDomain_slab_sigmaAdelicAct_eq_measureReal_mul_integral_map_of_isTwistedSectionFnOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/fd593db6-8fd4-5b9f-903c-46822fb340ba

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_AutomorphicForm_setIntegral_fundamentalDomain_slab_sigmaCentralizer_eq_measureReal_mul_integral_of_forall_exists_mem_center
import Theorems.Thm_AutomorphicForm_map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_idelesBaseChange
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_fundamentalDomain_slab_sigmaAdelicAct_eq_measureReal_mul_integral_map_of_isTwistedSectionFnOn
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal

noncomputable section

namespace P2mTwistedSlabTransport

section Scalars

theorem map_scalar {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (c : Aˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : A →* B) c) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply, Units.coe_map,
    MonoidHom.coe_coe]
  split_ifs <;> simp

theorem scalar_mul_comm {R : Type*} [CommRing R] (c : Rˣ) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : R) * (g : Matrix (Fin 2) (Fin 2) R) =
    (g : Matrix (Fin 2) (Fin 2) R) * Matrix.scalar (Fin 2) (c : R)
  exact (Matrix.scalar_commute (c : R) (fun r => Commute.all _ r) _).eq

private theorem _root_.P2mTwistedSlabTransport.det_scalar {R : Type*} [CommRing R] (c : Rˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = c ^ 2 := by
  simp [Matrix.GeneralLinearGroup.det_scalar]

p2m_export "P2mTwistedSlabTransport" "det_scalar"
end Scalars

section Transport

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

abbrev Ering : (L ⊗[K] AdeleRing (𝓞 K) K) ≃+* AdeleRing (𝓞 L) L :=
  ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
    (M4aHerbrand.Bridge.genuineRingEquiv K L))

theorem continuous_Ering : Continuous (Ering K L) ∧ Continuous (Ering K L).symm := by
  letI : Algebra (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    (M4aHerbrand.Bridge.genuineβ K L).toAlgebra
  haveI : IsModuleTopology (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 L) L) :=
    M4aHerbrand.Bridge.isModuleTopology_adeleRing_of_free (𝓞 K) K (𝓞 L) L
      (M4aHerbrand.Bridge.continuous_genuineβ K L) (M4aHerbrand.Bridge.genuineTensorEquiv K L)
  let eLin : (L ⊗[K] AdeleRing (𝓞 K) K) ≃ₗ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L :=
    (TensorProduct.RightActions.Module.TensorProduct.comm K (AdeleRing (𝓞 K) K) L).symm.trans
      (M4aHerbrand.Bridge.genuineTensorEquiv K L).toLinearEquiv
  have hfun : ∀ x, eLin x = Ering K L x := fun x => rfl
  let eC := IsModuleTopology.continuousLinearEquiv eLin
  have h1 : Continuous (Ering K L) := by
    have : Continuous eC := eC.continuous
    exact this.congr hfun
  have h2 : Continuous (Ering K L).symm := by
    have hc : Continuous eC.symm := eC.symm.continuous
    refine hc.congr fun y => ?_
    apply (Ering K L).injective
    rw [RingEquiv.apply_symm_apply]
    show Ering K L (eLin.symm y) = y
    rw [← hfun, LinearEquiv.apply_symm_apply]
  exact ⟨h1, h2⟩

theorem continuous_generalLinearGroup_map {A B : Type*} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact Continuous.matrix_map Units.continuous_val hf
  · exact Continuous.matrix_map Units.continuous_coe_inv hf

def glE : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) ≃ₜ* AdelicGL2 (𝓞 L) L where
  toFun := Matrix.GeneralLinearGroup.map (Ering K L).toRingHom
  invFun := Matrix.GeneralLinearGroup.map (Ering K L).symm.toRingHom
  left_inv g := by
    ext i j
    exact (Ering K L).symm_apply_apply (g.val i j)
  right_inv g := by
    ext i j
    exact (Ering K L).apply_symm_apply (g.val i j)
  map_mul' := map_mul _
  continuous_toFun := continuous_generalLinearGroup_map _ (continuous_Ering K L).1
  continuous_invFun := continuous_generalLinearGroup_map _ (continuous_Ering K L).2

theorem coe_glE : ⇑(glE K L) = ⇑(Matrix.GeneralLinearGroup.map (Ering K L).toRingHom) := rfl

theorem coe_glE_symm : ⇑(glE K L).symm = ⇑(Matrix.GeneralLinearGroup.map (Ering K L).symm.toRingHom) := rfl

theorem glE_apply (g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    glE K L g = Matrix.GeneralLinearGroup.map (Ering K L).toRingHom g := rfl

theorem glE_sigmaGL (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (y : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    glE K L (sigmaGL K L (AdeleRing (𝓞 K) K) σ y) = sigmaAdelicAct K L D σ (glE K L y) :=
  (AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L D).1 σ y

theorem glE_toTensorGL (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    glE K L (toTensorGL K L (AdeleRing (𝓞 K) K) g) =
      Matrix.GeneralLinearGroup.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β g :=
  (AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L D).2.1 g

theorem glE_includeLeft (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (δ₀ : GL (Fin 2) L) :
    glE K L (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀) =
      globalPoints (𝓞 L) L δ₀ :=
  (AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L D).2.2 δ₀

theorem glE_scalar (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    glE K L (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      centralScalar (𝓞 L) L (Units.map ((Ering K L).toRingHom : L ⊗[K] AdeleRing (𝓞 K) K →* _) c) := by
  rw [glE_apply, map_scalar]
  rfl

omit [NumberField L] [FiniteDimensional K L] in

theorem sigmaGL_toTensorGL (σ : L ≃ₐ[K] L) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    sigmaGL K L (AdeleRing (𝓞 K) K) σ (toTensorGL K L (AdeleRing (𝓞 K) K) g) =
      toTensorGL K L (AdeleRing (𝓞 K) K) g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show sigmaTensor K L (AdeleRing (𝓞 K) K) σ
      ((Algebra.TensorProduct.includeRight : AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] AdeleRing (𝓞 K) K)
        (g i j)) =
    (Algebra.TensorProduct.includeRight : AdeleRing (𝓞 K) K →ₐ[K] L ⊗[K] AdeleRing (𝓞 K) K) (g i j)
  simp [sigmaTensor, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem sigmaAdelicAct_map_beta (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    sigmaAdelicAct K L D σ
        (Matrix.GeneralLinearGroup.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β g) =
      Matrix.GeneralLinearGroup.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β g := by
  rw [← glE_toTensorGL K L D, ← glE_sigmaGL K L D, sigmaGL_toTensorGL]

end Transport

section CentralL

variable (L : Type) [Field L] [NumberField L]

theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L z * g = g * centralScalar (𝓞 L) L z :=
  scalar_mul_comm z g

theorem centralScalar_mem_center (z : (AdeleRing (𝓞 L) L)ˣ) :
    centralScalar (𝓞 L) L z ∈ Subgroup.center (AdelicGL2 (𝓞 L) L) := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact (centralScalar_mul_comm L z g).symm

theorem det_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z) = z ^ 2 :=
  det_scalar z

theorem mem_sigmaCentralizer_of_mem_center_of_apply_eq
    (σA : AdelicGL2 (𝓞 L) L →* AdelicGL2 (𝓞 L) L) (d z : AdelicGL2 (𝓞 L) L)
    (hz : z ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)) (hfix : σA z = z) :
    z ∈ sigmaCentralizer σA d := by
  rw [mem_sigmaCentralizer_iff, hfix, (Subgroup.mem_center_iff.mp hz d).symm, mul_inv_cancel_right]

theorem exists_mem_center_of_forall_exists_centralScalar
    (σA : AdelicGL2 (𝓞 L) L →* AdelicGL2 (𝓞 L) L) (d : AdelicGL2 (𝓞 L) L)
    (hZ : ∀ r : ℝ, 0 < r → ∃ z : (AdeleRing (𝓞 L) L)ˣ,
      σA (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L z ∧
        NumberField.TateGlobal.ideleNorm L z = r)
    (c : ℝ) (hc : 0 < c) :
    ∃ t : sigmaCentralizer σA d, t ∈ Subgroup.center _ ∧
      NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det (t : AdelicGL2 (𝓞 L) L)) = c := by
  obtain ⟨z, hfix, hz⟩ := hZ (Real.sqrt c) (Real.sqrt_pos.mpr hc)
  have hmem := mem_sigmaCentralizer_of_mem_center_of_apply_eq L σA d _ (centralScalar_mem_center L z) hfix
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (centralScalar_mul_comm L z (s : AdelicGL2 (𝓞 L) L)).symm
  · change NumberField.TateGlobal.ideleNorm L
      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) = c
    rw [det_centralScalar, pow_two, NumberField.TateGlobal.ideleNorm_mul, hz, Real.mul_self_sqrt hc.le]

end CentralL

section FixedScalars

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem exists_fixed_centralScalar_ideleNorm_eq (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L) (r : ℝ) (hr : 0 < r) :
    ∃ z : (AdeleRing (𝓞 L) L)ˣ,
      sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L z ∧
        NumberField.TateGlobal.ideleNorm L z = r := by
  set n : ℕ := Module.finrank K L with hn
  have hnpos : 0 < n := Module.finrank_pos
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hnpos.ne'
  obtain ⟨zK, -, hzK⟩ :=
    NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K (r ^ ((n : ℝ)⁻¹)) (Real.rpow_pos_of_pos hr _)
  refine ⟨AutomorphicForm.TransversalMeasure.idelesBaseChange K L zK, ?_, ?_⟩
  · have hmap : Matrix.GeneralLinearGroup.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β
        (centralScalar (𝓞 K) K zK) =
        centralScalar (𝓞 L) L (AutomorphicForm.TransversalMeasure.idelesBaseChange K L zK) := by
      show Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.scalar (Fin 2) zK) = _
      rw [map_scalar]
      rfl
    rw [← hmap, sigmaAdelicAct_map_beta]
  · rw [NumberField.TateGlobal.ideleNorm_idelesBaseChange, hzK, ← hn, ← Real.rpow_natCast,
      ← Real.rpow_mul hr.le, inv_mul_cancel₀ hn0, Real.rpow_one]

end FixedScalars

section Centralizers

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)

abbrev δA : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) :=
  Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
    Matrix.GeneralLinearGroup.scalar (Fin 2) c

abbrev cE : AdelicGL2 (𝓞 L) L :=
  Matrix.GeneralLinearGroup.map (Ering K L).toRingHom (Matrix.GeneralLinearGroup.scalar (Fin 2) c)

abbrev Tw : Subgroup (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
  twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (δA K L δ₀ c)

abbrev TA (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) : Subgroup (AdelicGL2 (𝓞 L) L) :=
  sigmaCentralizer (sigmaAdelicAct K L D σ) (globalPoints (𝓞 L) L δ₀)

theorem cE_mul_comm (g : AdelicGL2 (𝓞 L) L) : cE K L c * g = g * cE K L c := by
  show glE K L (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * g = g * glE K L _
  rw [glE_scalar]
  exact centralScalar_mul_comm L _ g

theorem glE_δA (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) :
    glE K L (δA K L δ₀ c) = globalPoints (𝓞 L) L δ₀ * cE K L c := by
  rw [map_mul, glE_includeLeft K L D]
  rfl

theorem mem_Tw_iff (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    t ∈ Tw K L σ δ₀ c ↔ glE K L t ∈ TA K L σ δ₀ D := by
  rw [mem_sigmaCentralizer_iff, mem_sigmaCentralizer_iff, ← (glE K L).injective.eq_iff, map_mul,
    map_mul, map_inv, glE_sigmaGL K L D, glE_δA K L δ₀ c D]
  set x := glE K L t
  set g := globalPoints (𝓞 L) L δ₀
  set s := sigmaAdelicAct K L D σ x
  have hkey : x * (g * cE K L c) * s⁻¹ = x * g * s⁻¹ * cE K L c := by
    rw [← mul_assoc, mul_assoc (x * g), cE_mul_comm K L c s⁻¹, ← mul_assoc]
  rw [hkey]
  constructor
  · intro h
    exact mul_right_cancel h
  · intro h
    rw [h]

end Centralizers

section Restrict

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

theorem symm_mem_Tw (s : TA K L σ δ₀ D) : (glE K L).symm s ∈ Tw K L σ δ₀ c := by
  rw [mem_Tw_iff K L σ δ₀ c D, ContinuousMulEquiv.apply_symm_apply]
  exact s.2

def eT : Tw K L σ δ₀ c ≃ₜ* TA K L σ δ₀ D where
  toFun t := ⟨glE K L t, (mem_Tw_iff K L σ δ₀ c D t).1 t.2⟩
  invFun s := ⟨(glE K L).symm s, symm_mem_Tw K L σ δ₀ c D s⟩
  left_inv _ := Subtype.ext ((glE K L).symm_apply_apply _)
  right_inv _ := Subtype.ext ((glE K L).apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul (glE K L) _ _)
  continuous_toFun := Continuous.subtype_mk ((glE K L).continuous.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk ((glE K L).symm.continuous.comp continuous_subtype_val) _

theorem coe_eT (t : Tw K L σ δ₀ c) :
    ((eT K L σ δ₀ c D t : TA K L σ δ₀ D) : AdelicGL2 (𝓞 L) L) = glE K L t := rfl

theorem coe_eT_symm (s : TA K L σ δ₀ D) :
    (((eT K L σ δ₀ c D).symm s : Tw K L σ δ₀ c) : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) =
      (glE K L).symm s := rfl

abbrev ΓL : Subgroup (GL (Fin 2) L) :=
  sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀

abbrev HT : Subgroup (Tw K L σ δ₀ c) :=
  ((ΓL K L σ δ₀).map (Matrix.GeneralLinearGroup.map
    (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
    (Tw K L σ δ₀ c)

abbrev HA : Subgroup (TA K L σ δ₀ D) :=
  ((ΓL K L σ δ₀).map (globalPoints (𝓞 L) L)).subgroupOf (TA K L σ δ₀ D)

theorem glE_symm_globalPoints (D₁ : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (γ : GL (Fin 2) L) :
    (glE K L).symm (globalPoints (𝓞 L) L γ) =
      Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) γ := by
  apply (glE K L).injective
  rw [ContinuousMulEquiv.apply_symm_apply, glE_includeLeft K L D₁]

def eH : (HA K L σ δ₀ D).op ≃ (HT K L σ δ₀ c).op where
  toFun g := ⟨MulOpposite.op ((eT K L σ δ₀ c D).symm
      (MulOpposite.unop (g : (TA K L σ δ₀ D)ᵐᵒᵖ))), by
    rw [Subgroup.mem_op, MulOpposite.unop_op, Subgroup.mem_subgroupOf, coe_eT_symm]
    have hg := g.2
    rw [Subgroup.mem_op, Subgroup.mem_subgroupOf] at hg
    obtain ⟨γ, hγ, hγeq⟩ := hg
    refine ⟨γ, hγ, ?_⟩
    rw [← glE_symm_globalPoints K L D, hγeq]⟩
  invFun h := ⟨MulOpposite.op (eT K L σ δ₀ c D
      (MulOpposite.unop (h : (Tw K L σ δ₀ c)ᵐᵒᵖ))), by
    rw [Subgroup.mem_op, MulOpposite.unop_op, Subgroup.mem_subgroupOf, coe_eT]
    have hh := h.2
    rw [Subgroup.mem_op, Subgroup.mem_subgroupOf] at hh
    obtain ⟨γ, hγ, hγeq⟩ := hh
    refine ⟨γ, hγ, ?_⟩
    rw [← hγeq, ← glE_includeLeft K L D]⟩
  left_inv g := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, ContinuousMulEquiv.apply_symm_apply]
  right_inv h := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_op, ContinuousMulEquiv.symm_apply_apply]

theorem eH_smul (g : (HA K L σ δ₀ D).op) (x : Tw K L σ δ₀ c) :
    eT K L σ δ₀ c D (eH K L σ δ₀ c D g • x) = g • eT K L σ δ₀ c D x := by
  rw [Subgroup.smul_def, Subgroup.smul_def, MulOpposite.smul_eq_mul_unop, MulOpposite.smul_eq_mul_unop,
    map_mul]
  congr 1
  exact (eT K L σ δ₀ c D).apply_symm_apply _

omit [NumberField K] [FiniteDimensional K L] in

theorem isClosed_TA :
    IsClosed ((TA K L σ δ₀ D : Subgroup (AdelicGL2 (𝓞 L) L)) : Set (AdelicGL2 (𝓞 L) L)) := by
  have hc : Continuous fun t : AdelicGL2 (𝓞 L) L =>
      t * globalPoints (𝓞 L) L δ₀ * (sigmaAdelicAct K L D σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul (continuous_sigmaAdelicAct K L D σ).inv
  have h : ((TA K L σ δ₀ D : Subgroup (AdelicGL2 (𝓞 L) L)) : Set (AdelicGL2 (𝓞 L) L)) =
      (fun t : AdelicGL2 (𝓞 L) L => t * globalPoints (𝓞 L) L δ₀ * (sigmaAdelicAct K L D σ t)⁻¹) ⁻¹'
        {globalPoints (𝓞 L) L δ₀} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [h]
  exact (isClosed_singleton).preimage hc

theorem glE_twistedConj_symm (x : AdelicGL2 (𝓞 L) L) :
    glE K L (((glE K L).symm x)⁻¹ * δA K L δ₀ c *
        sigmaGL K L (AdeleRing (𝓞 K) K) σ ((glE K L).symm x)) =
      x⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ x * cE K L c := by
  rw [map_mul, map_mul, map_inv, glE_sigmaGL K L D, ContinuousMulEquiv.apply_symm_apply,
    glE_δA K L δ₀ c D, ← mul_assoc x⁻¹, mul_assoc (x⁻¹ * globalPoints (𝓞 L) L δ₀) (cE K L c),
    cE_mul_comm, ← mul_assoc]

end Restrict

end P2mTwistedSlabTransport

end

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm P2mTwistedSlabTransport
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.twistedCentralizerBorel

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    [τ'.IsHaarMeasure] [τ'.IsMulRightInvariant]
    (D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hD' : IsFundamentalDomain
      (((AutomorphicForm.sigmaCentralizer
          (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
          (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom :
              L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
        (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom :
                L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D' τ')
    (α β : ℝ) (hα : 0 < α)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΨ : IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφm : Measurable φ)
    (w : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ)
    (hw : AutomorphicForm.IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ'
      (φ ∘ Matrix.GeneralLinearGroup.map
        (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
          (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)) w) :
    ∫ x in Ψ, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
          AutomorphicForm.sigmaAdelicAct K L D σ x *
        Matrix.GeneralLinearGroup.map
          (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
            (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
        ∂((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
          {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) =
      (τ'.real (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc α β}) : ℂ) *
        ∫ y, (φ ∘ Matrix.GeneralLinearGroup.map
            (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
              (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom))
              (y⁻¹ *
                (Matrix.GeneralLinearGroup.map
                    (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                  Matrix.GeneralLinearGroup.scalar (Fin 2) c) *
                AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ y) * (w y : ℂ)
          ∂(@Measure.map (AutomorphicForm.AdelicGL2 (𝓞 L) L) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _
            (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K))
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom))
            (adelicGLHaar (Fin 2) (𝓞 L) L)) := by
  classical

  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI : SigmaCompactSpace (AdelicGL2 (𝓞 L) L) := inferInstance
  set μ : Measure (AdelicGL2 (𝓞 L) L) := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  haveI : μ.IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L

  letI mG : MeasurableSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
    AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI : BorelSpace (Tw K L σ δ₀ c) := ⟨rfl⟩

  letI mA : MeasurableSpace (TA K L σ δ₀ D) := borel _
  haveI : BorelSpace (TA K L σ δ₀ D) := ⟨rfl⟩
  haveI : SigmaCompactSpace (TA K L σ δ₀ D) := (isClosed_TA K L σ δ₀ D).sigmaCompactSpace
  set e := eT K L σ δ₀ c D with he
  set em : Tw K L σ δ₀ c ≃ᵐ TA K L σ δ₀ D := e.toHomeomorph.toMeasurableEquiv with hem_def
  have hem : ∀ t : Tw K L σ δ₀ c, em t = e t := fun _ => rfl

  set τA : Measure (TA K L σ δ₀ D) := Measure.map em τ' with hτA
  haveI hτAH : τA.IsHaarMeasure := e.isHaarMeasure_map τ'
  haveI hτAσ : SigmaFinite τA := Measure.IsHaarMeasure.sigmaFinite (μ := τA)
  haveI : SFinite τA := @instSFiniteOfSigmaFinite _ _ τA hτAσ
  haveI : τA.IsMulRightInvariant := by
    refine ⟨fun s => ?_⟩
    rw [hτA, Measure.map_map (measurable_mul_const s) em.measurable]
    have hcomp : ((fun t : TA K L σ δ₀ D => t * s) ∘ em) =
        em ∘ fun t : Tw K L σ δ₀ c => t * e.symm s := by
      funext t
      show e t * s = e (t * e.symm s)
      rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
    rw [hcomp, ← Measure.map_map em.measurable (measurable_mul_const _), map_mul_right_eq_self]

  have hT' : ∀ r : ℝ, 0 < r → ∃ t : TA K L σ δ₀ D, t ∈ Subgroup.center _ ∧
      NumberField.TateGlobal.ideleNorm L
        (Matrix.GeneralLinearGroup.det (t : AdelicGL2 (𝓞 L) L)) = r := fun r hr =>
    exists_mem_center_of_forall_exists_centralScalar L (sigmaAdelicAct K L D σ)
      (globalPoints (𝓞 L) L δ₀)
      (fun r' hr' => exists_fixed_centralScalar_ideleNorm_eq K L D σ r' hr') r hr

  have hqmp : Measure.QuasiMeasurePreserving em.symm τA τ' := by
    refine ⟨em.symm.measurable, ?_⟩
    rw [hτA, MeasurableEquiv.map_symm_map]
  have hDA : IsFundamentalDomain (HA K L σ δ₀ D).op (em '' D') τA :=
    hD'.image_of_equiv em.toEquiv hqmp (eH K L σ δ₀ c D) (fun g x => eH_smul K L σ δ₀ c D g x)

  obtain ⟨hw0, hwm, hwc, hw1⟩ := hw
  set wA : AdelicGL2 (𝓞 L) L → ℝ := fun x => w ((glE K L).symm x) with hwA_def
  have hwA0 : ∀ x, 0 ≤ wA x := fun x => hw0 _
  have hwAm : Measurable wA := hwm.comp (glE K L).symm.continuous.measurable
  have hwAc : HasCompactSupport wA := hwc.comp_homeomorph (glE K L).symm.toHomeomorph
  set φc : AdelicGL2 (𝓞 L) L → ℂ := fun g => φ (g * cE K L c) with hφc_def
  have hφcm : Measurable φc := hφm.comp (measurable_mul_const _)
  have hw1A : ∀ x : AdelicGL2 (𝓞 L) L,
      φc (x⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ x) ≠ 0 →
        ∫ t : TA K L σ δ₀ D, wA ((t : AdelicGL2 (𝓞 L) L) * x) ∂τA = 1 := by
    intro x hx
    rw [hτA, integral_map_equiv em]
    have hrw : (fun t' : Tw K L σ δ₀ c => wA (((em t' : TA K L σ δ₀ D) : AdelicGL2 (𝓞 L) L) * x)) =
        fun t' : Tw K L σ δ₀ c =>
          w (((t' : Tw K L σ δ₀ c) : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) * (glE K L).symm x) := by
      funext t'
      show w ((glE K L).symm (glE K L (t' : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) * x)) = _
      rw [map_mul, ContinuousMulEquiv.symm_apply_apply]
    rw [hrw]
    refine hw1 ((glE K L).symm x) ?_
    show φ (glE K L (((glE K L).symm x)⁻¹ * δA K L δ₀ c *
      sigmaGL K L (AdeleRing (𝓞 K) K) σ ((glE K L).symm x))) ≠ 0
    rw [glE_twistedConj_symm K L σ δ₀ c D]
    exact hx

  have hσA : ∀ γ : GL (Fin 2) L, sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L γ) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ) := fun γ =>
    sigmaAdelicAct_globalPoints K L D σ γ
  have main :=
    AutomorphicForm.setIntegral_fundamentalDomain_slab_sigmaCentralizer_eq_measureReal_mul_integral_of_forall_exists_mem_center
      L μ (σ : L →+* L) (sigmaAdelicAct K L D σ) hσA (continuous_sigmaAdelicAct K L D σ) δ₀ τA hT'
      α β hα Ψ hΨ (em '' D') hDA φc hφcm wA hwA0 hwAm hwAc hw1A
  refine main.trans ?_
  congr 1
  ·
    have hset : em ⁻¹' (em '' D' ∩ {t : TA K L σ δ₀ D | NumberField.TateGlobal.ideleNorm L
        (Matrix.GeneralLinearGroup.det (t : AdelicGL2 (𝓞 L) L)) ∈ Set.Icc α β}) =
        D' ∩ {t : Tw K L σ δ₀ c | NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det (glE K L (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈
            Set.Icc α β} := by
      rw [Set.preimage_inter, em.injective.preimage_image]
      rfl
    rw [measureReal_def, measureReal_def, hτA, MeasurableEquiv.map_apply, hset]
    rfl
  ·
    let emG : AdelicGL2 (𝓞 L) L ≃ᵐ GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) :=
      (glE K L).symm.toHomeomorph.toMeasurableEquiv
    have hcoe : (⇑emG : AdelicGL2 (𝓞 L) L → GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) =
        ⇑(Matrix.GeneralLinearGroup.map (Ering K L).symm.toRingHom) := rfl
    symm
    rw [← hcoe, integral_map_equiv emG]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    rw [hcoe]
    dsimp only [Function.comp_apply]
    have hx := glE_twistedConj_symm K L σ δ₀ c D x
    rw [coe_glE, coe_glE_symm] at hx
    rw [hx]
    rfl

end S_AutomorphicForm_setIntegral_fundamentalDomain_slab_sigmaAdelicAct_eq_measureReal_mul_integral_map_of_isTwistedSectionFnOn
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_fundamentalDomain_slab_sigmaAdelicAct_eq_measureReal_mul_integral_map_of_isTwistedSectionFnOn (solution)
