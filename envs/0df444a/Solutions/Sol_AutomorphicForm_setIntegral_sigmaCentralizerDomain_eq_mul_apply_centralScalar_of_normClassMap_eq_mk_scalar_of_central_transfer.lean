-- Prove2me | solution 1 for AutomorphicForm.setIntegral_sigmaCentralizerDomain_eq_mul_apply_centralScalar_of_normClassMap_eq_mk_scalar_of_central_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2ac7bb16-5244-5ffa-bbe8-8afbbf962d7f

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_TwistedNormClasses
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_centralizer_forall_isFundamentalDomain_op_inter_eq_mul_log_and_isOrbitalIntegralOn_centralScalar_iff
import Theorems.Thm_AutomorphicForm_setIntegral_fundamentalDomain_slab_sigmaAdelicAct_eq_measureReal_mul_integral_map_of_isTwistedSectionFnOn
import Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_adeleRing_of_isSigmaConjugate_scalar
import Theorems.Thm_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_eq_scalar
import Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar
import Theorems.Thm_AutomorphicForm_map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft
import Theorems.Thm_M4aHerbrand_GenuineDescent_injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
import Theorems.Thm_AutomorphicForm_exists_inv_mul_mul_map_eq_scalar_of_sigmaNormPow_eq_map_scalar_of_odd
import Theorems.Thm_AutomorphicForm_setIntegral_sigmaCentralizerDomain_eq_mul_apply_centralScalar_of_normClassMap_eq_mk_scalar_of_forall_ne_scalar_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_sigmaCentralizerDomain_eq_mul_apply_centralScalar_of_normClassMap_eq_mk_scalar_of_central_transfer
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.preimage_mulLeft_smul LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"
p2m_attr_erase "simp" "Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply AutomorphicForm.cpowChar_apply_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm LT.TwistedNorm
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal

noncomputable section

namespace P2mCentralPerClass

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

theorem conj_scalar {R : Type*} [CommRing R] (c : Rˣ) (h : GL (Fin 2) R) :
    h⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) c * h = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  rw [mul_assoc, scalar_mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem eq_scalar_of_isConj {R : Type*} [CommRing R] {γ : GL (Fin 2) R} {b : Rˣ}
    (h : IsConj γ (Matrix.GeneralLinearGroup.scalar (Fin 2) b)) :
    γ = Matrix.GeneralLinearGroup.scalar (Fin 2) b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  calc γ = c⁻¹ * (c * γ * c⁻¹) * c := by group
    _ = _ := by rw [hc, conj_scalar]

theorem list_prod_map_range {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]
      simp

end Scalars

section TensorAlgebra

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (B : Type) [CommRing B] [Algebra K B]

local notation "incl" => (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] B)

theorem sigmaTensor_includeLeft (σ : L ≃ₐ[K] L) (l : L) :
    sigmaTensor K L B σ (l ⊗ₜ[K] (1 : B)) = σ l ⊗ₜ[K] (1 : B) := by
  simp [sigmaTensor, Algebra.TensorProduct.map_tmul]

theorem sigmaGL_map_includeLeft (σ : L ≃ₐ[K] L) (g : GL (Fin 2) L) :
    sigmaGL K L B σ (Matrix.GeneralLinearGroup.map incl g) =
      Matrix.GeneralLinearGroup.map incl (Matrix.GeneralLinearGroup.map (σ : L →+* L) g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show sigmaTensor K L B σ (Algebra.TensorProduct.includeLeftRingHom (g i j)) =
    Algebra.TensorProduct.includeLeftRingHom ((σ : L →+* L) (g i j))
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    sigmaTensor_includeLeft]
  rfl

theorem conj_eq_scalar (σ : L ≃ₐ[K] L) (δ₀ h : GL (Fin 2) L) (d : Lˣ)
    (hd : h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h =
      Matrix.GeneralLinearGroup.scalar (Fin 2) d)
    (c : (L ⊗[K] B)ˣ) :
    (Matrix.GeneralLinearGroup.map incl h)⁻¹ *
        (Matrix.GeneralLinearGroup.map incl δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c) *
        sigmaGL K L B σ (Matrix.GeneralLinearGroup.map incl h) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (incl : L →* L ⊗[K] B) d * c) := by
  rw [sigmaGL_map_includeLeft, map_mul, ← map_scalar (incl) d, ← hd, map_mul, map_mul, map_inv]
  simp only [mul_assoc]
  rw [scalar_mul_comm]

theorem toTensorGL_map_algebraMap (s₀ : GL (Fin 2) K) :
    toTensorGL K L B (Matrix.GeneralLinearGroup.map (algebraMap K B) s₀) =
      Matrix.GeneralLinearGroup.map incl (Matrix.GeneralLinearGroup.map (algebraMap K L) s₀) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show (Algebra.TensorProduct.includeRight : B →ₐ[K] L ⊗[K] B) (algebraMap K B (s₀ i j)) =
    Algebra.TensorProduct.includeLeftRingHom (algebraMap K L (s₀ i j))
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.commutes,
    Algebra.TensorProduct.algebraMap_apply]

theorem map_sigma_map_algebraMap (σ : L ≃ₐ[K] L) (s₀ : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.map (σ : L →+* L) (Matrix.GeneralLinearGroup.map (algebraMap K L) s₀) =
      Matrix.GeneralLinearGroup.map (algebraMap K L) s₀ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show (σ : L →+* L) (algebraMap K L (s₀ i j)) = algebraMap K L (s₀ i j)
  exact σ.commutes _

theorem conj_mem_sigmaCentralizer (σ : L ≃ₐ[K] L) (δ₀ h : GL (Fin 2) L) (d : Lˣ)
    (hd : h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h =
      Matrix.GeneralLinearGroup.scalar (Fin 2) d)
    (s₀ : GL (Fin 2) K) :
    h * Matrix.GeneralLinearGroup.map (algebraMap K L) s₀ * h⁻¹ ∈
      sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀ := by
  rw [mem_sigmaCentralizer_iff]
  set sL := Matrix.GeneralLinearGroup.map (algebraMap K L) s₀ with hsL
  set θ := Matrix.GeneralLinearGroup.map (n := Fin 2) (σ : L →+* L) with hθ
  have hδ₀ : δ₀ = h * Matrix.GeneralLinearGroup.scalar (Fin 2) d * (θ h)⁻¹ := by
    rw [← hd]; group
  have hσs : θ sL = sL := map_sigma_map_algebraMap K L σ s₀
  have hcomm : Matrix.GeneralLinearGroup.scalar (Fin 2) d * sL =
      sL * Matrix.GeneralLinearGroup.scalar (Fin 2) d := scalar_mul_comm d sL
  rw [hδ₀, map_mul, map_mul, map_inv, hσs]
  calc h * sL * h⁻¹ * (h * Matrix.GeneralLinearGroup.scalar (Fin 2) d * (θ h)⁻¹) * (θ h * sL * (θ h)⁻¹)⁻¹
      = h * (sL * Matrix.GeneralLinearGroup.scalar (Fin 2) d) * sL⁻¹ * (θ h)⁻¹ := by group
    _ = h * (Matrix.GeneralLinearGroup.scalar (Fin 2) d * sL) * sL⁻¹ * (θ h)⁻¹ := by rw [hcomm]
    _ = h * Matrix.GeneralLinearGroup.scalar (Fin 2) d * (θ h)⁻¹ := by group

end TensorAlgebra

section Descent

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [CharZero K]
  (B : Type) [CommRing B] [Algebra K B]

theorem exists_eq_algebraMap_of_tmul_eq (l : L) (a : B)
    (h : l ⊗ₜ[K] (1 : B) = (1 : L) ⊗ₜ[K] a) : ∃ k : K, a = algebraMap K B k := by
  have h1 := congrArg (fun z => TensorProduct.lid K B
    (LinearMap.rTensor B (Algebra.trace K L) z)) h
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h1
  have htr1 : Algebra.trace K L (1 : L) = (Module.finrank K L : K) := by
    rw [← map_one (algebraMap K L), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
  rw [htr1] at h1
  have hn : (Module.finrank K L : K) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  refine ⟨(Module.finrank K L : K)⁻¹ * Algebra.trace K L l, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one, mul_smul, h1, smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem exists_eq_map_algebraMap_of_toTensorGL_eq (hinj : Function.Injective (algebraMap K B))
    (s : GL (Fin 2) B) (g : GL (Fin 2) L)
    (h : toTensorGL K L B s =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] B) g) :
    ∃ s₀ : GL (Fin 2) K, s = Matrix.GeneralLinearGroup.map (algebraMap K B) s₀ := by
  haveI : Nontrivial B := hinj.nontrivial
  have hent : ∀ i j : Fin 2, ∃ k : K, (s : Matrix (Fin 2) (Fin 2) B) i j = algebraMap K B k := by
    intro i j
    have hij := congrArg (fun x : GL (Fin 2) (L ⊗[K] B) => (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] B)) i j) h
    refine exists_eq_algebraMap_of_tmul_eq K L B (g i j) (s i j) ?_
    change (Algebra.TensorProduct.includeRight : B →ₐ[K] L ⊗[K] B) (s i j) =
      Algebra.TensorProduct.includeLeftRingHom (g i j) at hij
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.includeRight_apply] at hij
    exact hij.symm
  choose k hk using hent
  set M : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => k i j with hM
  have hMs : (algebraMap K B).mapMatrix M = (s : Matrix (Fin 2) (Fin 2) B) := by
    ext i j
    simp [hM, hk]
  have hdet : M.det ≠ 0 := by
    intro h0
    have h1 : (s : Matrix (Fin 2) (Fin 2) B).det = 0 := by
      rw [← hMs, ← RingHom.map_det, h0, map_zero]
    exact (Matrix.isUnits_det_units s).ne_zero h1
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, Units.ext ?_⟩
  rw [← hMs]
  rfl

end Descent

section TwistedNorm

variable {F L : Type} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {σ : L ≃ₐ[F] L}

theorem sigmaNormPow_eq_scalar_of_normClassMap_eq (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} {b : Fˣ}
    (h : normClassMap hgen (SigmaConjClasses.mk σ δ) =
      ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) b)) :
    sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ =
      Matrix.GeneralLinearGroup.map (algebraMap F L) (Matrix.GeneralLinearGroup.scalar (Fin 2) b) := by
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj] at h
  have hrep : normRep hgen δ = Matrix.GeneralLinearGroup.scalar (Fin 2) b := eq_scalar_of_isConj h
  obtain ⟨P, hP⟩ := isNormRep_normRep hgen δ
  rw [hrep, map_scalar] at hP
  rw [map_scalar]
  calc sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ
      = P * (P⁻¹ * sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank F L) δ
          * P) * P⁻¹ := by group
    _ = _ := by
        rw [hP]
        have := conj_scalar (Units.map ((algebraMap F L : F →+* L) : F →* L) b) P⁻¹
        rwa [inv_inv] at this

end TwistedNorm

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

theorem glE_iterate_sigmaGL (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (i : ℕ) (y : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
    glE K L ((⇑(sigmaGL K L (AdeleRing (𝓞 K) K) σ))^[i] y) =
      (⇑(sigmaAdelicAct K L D σ))^[i] (glE K L y) :=
  Function.Semiconj.iterate_right (fun x => glE_sigmaGL K L D σ x) i y

theorem glE_scalar (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    glE K L (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      centralScalar (𝓞 L) L (Units.map ((Ering K L).toRingHom : L ⊗[K] AdeleRing (𝓞 K) K →* _) c) := by
  rw [glE_apply, map_scalar]
  rfl

omit [NumberField K] [FiniteDimensional K L] in

theorem sigmaAdelicAct_centralScalar (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (v : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L v) = centralScalar (𝓞 L) L (D.unitsAct σ v) := by
  show Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.scalar (Fin 2) v) =
    Matrix.GeneralLinearGroup.scalar (Fin 2) _
  rw [map_scalar]
  rfl

omit [NumberField K] [FiniteDimensional K L] in
theorem iterate_sigmaAdelicAct_centralScalar (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L) (i : ℕ) (v : (AdeleRing (𝓞 L) L)ˣ) :
    (⇑(sigmaAdelicAct K L D σ))^[i] (centralScalar (𝓞 L) L v) =
      centralScalar (𝓞 L) L ((⇑(D.unitsAct σ))^[i] v) :=
  (Function.Semiconj.iterate_right (f := centralScalar (𝓞 L) L)
    (fun x => (sigmaAdelicAct_centralScalar K L D σ x).symm) i v).symm

omit [NumberField K] [FiniteDimensional K L] in

theorem iterate_unitsAct (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (i : ℕ) (v : (AdeleRing (𝓞 L) L)ˣ) :
    (⇑(D.unitsAct σ))^[i] v = D.unitsAct (σ ^ i) v := by
  induction i generalizing v with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ', map_mul, MulAut.mul_apply]

end Transport

section NormString

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L]

omit [NumberField L] [FiniteDimensional K L] in

theorem iterate_sigmaGL_scalar (σ : L ≃ₐ[K] L) (i : ℕ) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    ∃ c' : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ, (⇑(sigmaGL K L (AdeleRing (𝓞 K) K) σ))^[i]
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = Matrix.GeneralLinearGroup.scalar (Fin 2) c' := by
  induction i with
  | zero => exact ⟨c, rfl⟩
  | succ i ih =>
    obtain ⟨c', hc'⟩ := ih
    refine ⟨Units.map (sigmaTensor K L (AdeleRing (𝓞 K) K) σ :
      L ⊗[K] AdeleRing (𝓞 K) K →* L ⊗[K] AdeleRing (𝓞 K) K) c', ?_⟩
    rw [Function.iterate_succ_apply', hc']
    exact map_scalar _ _

theorem list_prod_map_mul_of_comm {ι G : Type*} [Monoid G] (l : List ι) (f g : ι → G)
    (hg : ∀ i ∈ l, ∀ x : G, g i * x = x * g i) :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih (fun i hi => hg i (List.mem_cons_of_mem a hi))]
    have hc : (t.map f).prod * g a = g a * (t.map f).prod := (hg a List.mem_cons_self _).symm
    rw [mul_assoc (f a) (g a), ← mul_assoc (g a), ← hc]
    simp only [mul_assoc]

omit [NumberField L] [FiniteDimensional K L] in

theorem normString_mul_scalar (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    normString K L (AdeleRing (𝓞 K) K) σ (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      normString K L (AdeleRing (𝓞 K) K) σ δ *
        normString K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  unfold AutomorphicForm.normString
  have hmul : ∀ i : ℕ, (⇑(sigmaGL K L (AdeleRing (𝓞 K) K) σ))^[i]
      (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      (⇑(sigmaGL K L (AdeleRing (𝓞 K) K) σ))^[i] δ *
        (⇑(sigmaGL K L (AdeleRing (𝓞 K) K) σ))^[i] (Matrix.GeneralLinearGroup.scalar (Fin 2) c) :=
    fun i => iterate_map_mul (sigmaGL K L (AdeleRing (𝓞 K) K) σ) i δ _
  simp_rw [hmul]
  refine list_prod_map_mul_of_comm _ _ _ (fun i _ x => ?_)
  obtain ⟨c', hc'⟩ := iterate_sigmaGL_scalar K L σ i c
  rw [hc']
  exact scalar_mul_comm c' x

omit [NumberField L] [FiniteDimensional K L] in

theorem normString_map_includeLeft (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) :
    normString K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀) =
      Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K)
        (sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L) δ₀) := by
  unfold AutomorphicForm.normString
  rw [← sigmaPartialNorm_eq_prod_map_range, ← sigmaNormPow_def,
    hom_sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (sigmaGL K L (AdeleRing (𝓞 K) K) σ)
      (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))
      (fun x => (sigmaGL_map_includeLeft K L (AdeleRing (𝓞 K) K) σ x).symm)]

theorem normString_scalar_transport [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (z : (AdeleRing (𝓞 L) L)ˣ) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (hc : glE K L (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      centralScalar (𝓞 L) L (D.unitsAct σ z)) :
    normString K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      toTensorGL K L (AdeleRing (𝓞 K) K)
        (centralScalar (𝓞 K) K ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) := by
  apply (glE K L).injective
  unfold AutomorphicForm.normString
  rw [map_list_prod, List.map_map]
  have hfun : (⇑(glE K L) ∘ fun i => (⇑(sigmaGL K L (AdeleRing (𝓞 K) K) σ))^[i]
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) =
      fun i => centralScalar (𝓞 L) L (D.unitsAct (σ ^ (i + 1)) z) := by
    funext i
    simp only [Function.comp_apply]
    rw [glE_iterate_sigmaGL K L D, hc, iterate_sigmaAdelicAct_centralScalar, iterate_unitsAct,
      pow_succ, map_mul, MulAut.mul_apply]
  rw [hfun, ← Function.comp_def (centralScalar (𝓞 L) L), ← List.map_map, ← map_list_prod,
    list_prod_map_range]

  have horder : σ ^ Module.finrank K L = 1 := by
    have h : orderOf σ = Module.finrank K L := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]
    rw [← h, pow_orderOf_eq_one]
  have hshift : ∏ i ∈ Finset.range (Module.finrank K L), D.unitsAct (σ ^ (i + 1)) z =
      ∏ i ∈ Finset.range (Module.finrank K L), D.unitsAct (σ ^ i) z := by
    have h1 := Finset.prod_range_succ (fun i => D.unitsAct (σ ^ i) z) (Module.finrank K L)
    have h2 := Finset.prod_range_succ' (fun i => D.unitsAct (σ ^ i) z) (Module.finrank K L)
    rw [horder, pow_zero] at *
    rw [h1] at h2
    exact (mul_right_cancel h2).symm
  rw [hshift, ← prod_algEquiv_eq_prod_range_of_generator hgen (fun τ => D.unitsAct τ z),
    (M4aHerbrand.GenuineDescent.injective_beta_and_fixed_iff_and_h90_and_prod_unitsAct_eq_idelicNorm
      K L D).2.2.2 z, glE_toTensorGL K L D]
  show _ = Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.scalar (Fin 2) _)
  rw [map_scalar]
  rfl

theorem normString_delta [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (b₀ : Kˣ)
    (hδ₀ : normClassMap hgen (SigmaConjClasses.mk σ δ₀) =
      ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) b₀))
    (z : (AdeleRing (𝓞 L) L)ˣ) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (hc : glE K L (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      centralScalar (𝓞 L) L (D.unitsAct σ z)) :
    normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      toTensorGL K L (AdeleRing (𝓞 K) K) (centralScalar (𝓞 K) K
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) b₀ *
          (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) := by
  rw [normString_mul_scalar, normString_map_includeLeft, sigmaNormPow_eq_scalar_of_normClassMap_eq hgen hδ₀,
    ← toTensorGL_map_algebraMap, normString_scalar_transport K L D σ hgen z c hc, ← map_mul,
    map_mul (centralScalar (𝓞 K) K), map_scalar]
  rfl

end NormString

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

abbrev inclA : L →+* L ⊗[K] AdeleRing (𝓞 K) K := Algebra.TensorProduct.includeLeftRingHom

abbrev δA (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) :=
  Matrix.GeneralLinearGroup.map (inclA K L) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c

abbrev Tw (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    Subgroup (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :=
  AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (δA K L δ₀ c)

abbrev ΓTw (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) :
    Subgroup (Tw K L σ δ₀ c) :=
  ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
    (Matrix.GeneralLinearGroup.map (inclA K L))).subgroupOf (Tw K L σ δ₀ c)

abbrev Zu (u : (AdeleRing (𝓞 K) K)ˣ) : Subgroup (AdelicGL2 (𝓞 K) K) :=
  Subgroup.centralizer ({centralScalar (𝓞 K) K u} : Set (AdelicGL2 (𝓞 K) K))

abbrev ΓKu (u : (AdeleRing (𝓞 K) K)ˣ) : Subgroup (Zu K u) := ((globalPoints (𝓞 K) K).range).subgroupOf (Zu K u)

set_option maxHeartbeats 8000000 in

theorem main_first_kind
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (c₀ : NNReal)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hcent : ∀ (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ),
      AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
        AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u) →
      ∀ (τ : Measure (Subgroup.centralizer
          ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AdelicGL2 (𝓞 K) K))))
        (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
        τ.IsHaarMeasure → τ'.IsHaarMeasure →
      ∀ C : ENNReal, C ≠ 0 → C ≠ ⊤ →
        (∀ D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
          IsFundamentalDomain
            (((AutomorphicForm.sigmaCentralizer
                (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
                (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom :
                    L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
              (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
                (Matrix.GeneralLinearGroup.map
                    (Algebra.TensorProduct.includeLeftRingHom :
                      L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                  Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D' τ' →
          ∀ a b : ℝ, 0 < a → a ≤ b →
            τ' (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
              (Matrix.GeneralLinearGroup.det
                (Matrix.GeneralLinearGroup.map
                  (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                    (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
                  (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
              C * ENNReal.ofReal (Real.log (b / a))) →
        (∀ D : Set (Subgroup.centralizer
            ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AdelicGL2 (𝓞 K) K))),
          IsFundamentalDomain
            (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf
              (Subgroup.centralizer
                ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AdelicGL2 (𝓞 K) K)))).op D τ →
          ∀ a b : ℝ, 0 < a → a ≤ b →
            τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (t : AdelicGL2 (𝓞 K) K)) ∈ Set.Icc a b}) =
              (Module.finrank K L : ENNReal) * C * ENNReal.ofReal (Real.log (b / a))) →
      ∀ I I' : ℂ,
        AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ
          (@Measure.map (AdelicGL2 (𝓞 L) L) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _
            (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K))
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom))
            (adelicGLHaar (Fin 2) (𝓞 L) L))
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ'
          (φ ∘ Matrix.GeneralLinearGroup.map
            (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
              (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)) I' →
        AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I → I' = I)
    (C_H : ℝ≥0∞) (hC0 : C_H ≠ 0) (hCt : C_H ≠ ⊤)
    (hC_H : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K),
      Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} →
      IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}) →
      adelicGLHaar (Fin 2) (𝓞 K) K Φ = C_H * ENNReal.ofReal (Real.log (b / a)))
    (δ₀ : GL (Fin 2) L) (b₀ : Kˣ)
    (hδ₀ : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ₀) =
      ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) b₀))
    (h : GL (Fin 2) L) (d : Lˣ)
    (hd : h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h =
      Matrix.GeneralLinearGroup.scalar (Fin 2) d)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΨs : Ψ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨ : IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    ∫ x in Ψ, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      (((c₀ : ℝ) / (Module.finrank K L : ℝ) * (C_H * ENNReal.ofReal (Real.log (β / α))).toReal : ℝ) : ℂ) *
        f (AutomorphicForm.centralScalar (𝓞 K) K
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) b₀ *
            (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) := by
  classical

  haveI := isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  haveI := isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI := t2Space_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  have hnpos : 0 < Module.finrank K L := Module.finrank_pos

  obtain ⟨c, hc_def⟩ : ∃ c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ, c =
      Units.map (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom : AdeleRing (𝓞 L) L →* L ⊗[K] AdeleRing (𝓞 K) K)
        (D.unitsAct σ z) := ⟨_, rfl⟩
  have hcE : Matrix.GeneralLinearGroup.map ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      centralScalar (𝓞 L) L (D.unitsAct σ z) := by
    rw [map_scalar]
    show Matrix.GeneralLinearGroup.scalar (Fin 2) _ = Matrix.GeneralLinearGroup.scalar (Fin 2) (D.unitsAct σ z)
    congr 1
    refine Units.ext ?_
    simp [hc_def]
  have hσz : sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (D.unitsAct σ z) :=
    sigmaAdelicAct_centralScalar K L D σ z

  have hnorm := normString_delta K L D σ hgen δ₀ b₀ hδ₀ z c hcE
  generalize hu : (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) b₀ *
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) = u at hnorm ⊢
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c)) := ⟨rfl⟩
  haveI : BorelSpace (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) := ⟨rfl⟩

  have hζ : (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) h)⁻¹ * (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c) *
      sigmaGL K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) h) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map ((Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) : L →* L ⊗[K] AdeleRing (𝓞 K) K) d * c) :=
    conj_eq_scalar K L (AdeleRing (𝓞 K) K) σ δ₀ h d hd c
  obtain ⟨e, he⟩ :=
    AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar
      K L σ hgen (AdeleRing (𝓞 K) K) (centralScalar (𝓞 K) K u) ⟨u, rfl⟩ ((Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c))
      (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) h) _ hζ

  obtain ⟨τ₁, hτ₁H, hτ₁R, ⟨D₁, hD₁⟩, -, -⟩ :=
    AutomorphicForm.exists_isHaarMeasure_centralizer_forall_isFundamentalDomain_op_inter_eq_mul_log_and_isOrbitalIntegralOn_centralScalar_iff
      K C_H hC0 hCt hC_H u 1 one_ne_zero ENNReal.one_ne_top

  let em : (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) ≃ᵐ (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c)) := e.toHomeomorph.toMeasurableEquiv
  have hem : ∀ s : (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))), em s = e s := fun _ => rfl
  obtain ⟨τ', hτ'⟩ : ∃ τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c)), τ' = Measure.map em τ₁ := ⟨_, rfl⟩
  haveI hτ'H : τ'.IsHaarMeasure := by rw [hτ']; exact e.isHaarMeasure_map τ₁
  haveI hτ'R : τ'.IsMulRightInvariant := by
    refine ⟨fun s => ?_⟩
    rw [hτ', Measure.map_map (measurable_mul_const s) em.measurable]
    have hcomp : ((fun t : (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => t * s) ∘ em) = em ∘ fun t : (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))) => t * e.symm s := by
      funext t
      show e t * s = e (t * e.symm s)
      rw [map_mul e t (e.symm s), ContinuousMulEquiv.apply_symm_apply]
    rw [hcomp, ← Measure.map_map em.measurable (measurable_mul_const _), map_mul_right_eq_self]

  have hinj : Function.Injective (algebraMap K (AdeleRing (𝓞 K) K)) :=
    NumberField.AdeleRing.algebraMap_injective (𝓞 K) K
  have hmemK : ∀ t : (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c)), t ∈ (((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c))) → e.symm t ∈ (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))) := by
    intro t ht
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at ht
    obtain ⟨g₁, -, hg₁⟩ := ht
    have hts : ((e (e.symm t) : (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c))) : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) =
        Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) h *
          toTensorGL K L (AdeleRing (𝓞 K) K) ((e.symm t : (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))) : GL (Fin 2) (AdeleRing (𝓞 K) K)) *
          (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) h)⁻¹ := he _
    rw [ContinuousMulEquiv.apply_symm_apply] at hts
    have htens : toTensorGL K L (AdeleRing (𝓞 K) K)
        ((e.symm t : (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))) : GL (Fin 2) (AdeleRing (𝓞 K) K)) =
        Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) (h⁻¹ * g₁ * h) := by
      rw [map_mul (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K)),
        map_mul (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K)), map_inv, hg₁, hts]
      group
    obtain ⟨s₀, hs₀⟩ := exists_eq_map_algebraMap_of_toTensorGL_eq K L (AdeleRing (𝓞 K) K) hinj
      ((e.symm t : (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))) : GL (Fin 2) (AdeleRing (𝓞 K) K)) (h⁻¹ * g₁ * h) htens
    rw [Subgroup.mem_subgroupOf]
    exact ⟨s₀, hs₀.symm⟩
  have hmemL : ∀ s : (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))), s ∈ (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))) → e s ∈ (((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c))) := by
    intro s hs
    rw [Subgroup.mem_subgroupOf] at hs
    obtain ⟨s₀, hs₀⟩ := hs
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    refine ⟨h * Matrix.GeneralLinearGroup.map (algebraMap K L) s₀ * h⁻¹,
      conj_mem_sigmaCentralizer K L σ δ₀ h d hd s₀, ?_⟩
    rw [he s, ← hs₀]
    show _ = Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) h * toTensorGL K L (AdeleRing (𝓞 K) K)
      (Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) s₀) *
        (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) h)⁻¹
    rw [toTensorGL_map_algebraMap, map_mul (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K)),
      map_mul (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K)), map_inv]
  let eΓ : (((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op → (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))).op := fun g =>
    ⟨MulOpposite.op (e.symm (MulOpposite.unop (g : (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c))ᵐᵒᵖ))),
      Subgroup.mem_op.2 (hmemK _ (Subgroup.mem_op.1 g.2))⟩
  have heΓ : ∀ g : (((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op, ((eΓ g : (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))).op) : (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))ᵐᵒᵖ) =
      MulOpposite.op (e.symm (MulOpposite.unop (g : (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c))ᵐᵒᵖ))) := fun _ => rfl
  have hbij : Function.Bijective eΓ := by
    constructor
    · intro g₁ g₂ hg
      have hg' := congrArg (fun x : (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))).op => MulOpposite.unop (x : (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))ᵐᵒᵖ)) hg
      simp only [heΓ, MulOpposite.unop_op] at hg'
      exact Subtype.ext (MulOpposite.unop_injective (e.symm.injective hg'))
    · intro q
      refine ⟨⟨MulOpposite.op (e (MulOpposite.unop (q : (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))ᵐᵒᵖ))),
        Subgroup.mem_op.2 (hmemL _ (Subgroup.mem_op.1 q.2))⟩, ?_⟩
      apply Subtype.ext
      rw [heΓ]
      simp only [MulOpposite.unop_op, ContinuousMulEquiv.symm_apply_apply, MulOpposite.op_unop]
  have hsemi : ∀ (g : (((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op) (x : (Subgroup.centralizer ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))), em ((Equiv.ofBijective eΓ hbij) g • x) = g • em x := by
    intro g x
    rw [Equiv.ofBijective_apply, hem, hem, Subgroup.smul_def, Subgroup.smul_def,
      MulOpposite.smul_eq_mul_unop, MulOpposite.smul_eq_mul_unop, heΓ, MulOpposite.unop_op,
      map_mul e x _, ContinuousMulEquiv.apply_symm_apply]
  have hqmp : Measure.QuasiMeasurePreserving em.symm τ' τ₁ := by
    refine ⟨em.symm.measurable, ?_⟩
    rw [hτ', MeasurableEquiv.map_symm_map]
  have hD' : IsFundamentalDomain (((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op (em '' D₁) τ' :=
    hD₁.image_of_equiv em.toEquiv hqmp (Equiv.ofBijective eΓ hbij) (fun g x => hsemi g x)

  obtain ⟨C_B, hB0, hBt, hB⟩ :=
    AutomorphicForm.exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_eq_scalar
      K L σ hgen δ₀ h d hd c τ'

  have hnC0 : (Module.finrank K L : ℝ≥0∞) * C_B ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 hnpos.ne') hB0
  have hnCt : (Module.finrank K L : ℝ≥0∞) * C_B ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hBt
  obtain ⟨τ, hτH, -, -, hτFD, hτOI⟩ :=
    AutomorphicForm.exists_isHaarMeasure_centralizer_forall_isFundamentalDomain_op_inter_eq_mul_log_and_isOrbitalIntegralOn_centralScalar_iff
      K C_H hC0 hCt hC_H u ((Module.finrank K L : ℝ≥0∞) * C_B) hnC0 hnCt
  have hOI := (hτOI c₀ f _).2 rfl

  have hφEc : HasCompactSupport (φ ∘ Matrix.GeneralLinearGroup.map ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom) := by
    have h1 : HasCompactSupport (φ ∘ (glE K L).toHomeomorph) := hφc.comp_homeomorph _
    exact h1
  obtain ⟨w, hw⟩ :=
    AutomorphicForm.exists_isTwistedSectionFnOn_adeleRing_of_isSigmaConjugate_scalar
      K L σ hgen ((Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c)) ⟨_, Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) h, hζ.symm⟩ τ' hτ'H
      (φ ∘ Matrix.GeneralLinearGroup.map ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom) hφEc

  have hJI := hcent δ₀ c u hnorm τ τ' hτH hτ'H C_B hB0 hBt hB hτFD _ _ ⟨w, hw, rfl⟩ hOI

  have key :=
    AutomorphicForm.setIntegral_fundamentalDomain_slab_sigmaAdelicAct_eq_measureReal_mul_integral_map_of_isTwistedSectionFnOn
      K L D σ δ₀ c τ' (em '' D₁) hD' α β hα Ψ hΨ φ hφ.measurable w hw

  have hLHS : ∫ x in Ψ, φ (x⁻¹ * globalPoints (𝓞 L) L δ₀ *
        sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      ∫ x in Ψ, φ (x⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ x *
        Matrix.GeneralLinearGroup.map ((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
        ∂((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
          {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) := by
    rw [Measure.restrict_restrict_of_subset hΨs]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [map_mul (sigmaAdelicAct K L D σ), hσz, hcE]
    congr 1
    rw [mul_assoc (x⁻¹ * globalPoints (𝓞 L) L δ₀) (sigmaAdelicAct K L D σ x)]
    congr 1
    exact scalar_mul_comm (D.unitsAct σ z) (sigmaAdelicAct K L D σ x)
  rw [hLHS, key, hJI, measureReal_def, hB (em '' D₁) hD' α β hα hαβ.le]

  have hcB : 0 < C_B.toReal := ENNReal.toReal_pos hB0 hBt
  have hnR : (0 : ℝ) < Module.finrank K L := Nat.cast_pos.2 hnpos
  have hreal : (C_B * ENNReal.ofReal (Real.log (β / α))).toReal *
      ((c₀ : ℝ) * (C_H / ((Module.finrank K L : ℝ≥0∞) * C_B)).toReal) =
      (c₀ : ℝ) / (Module.finrank K L : ℝ) * (C_H * ENNReal.ofReal (Real.log (β / α))).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_mul]
    field_simp
  rw [← mul_assoc, ← Complex.ofReal_mul, hreal]

end Main

end P2mCentralPerClass

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

set_option maxHeartbeats 4000000 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hprime : (Module.finrank K L).Prime)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (c₀ : NNReal)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hcent : ∀ (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ),
      AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ.symm
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
        AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u) →
      ∀ (τ : Measure (Subgroup.centralizer
          ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AdelicGL2 (𝓞 K) K))))
        (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
        τ.IsHaarMeasure → τ'.IsHaarMeasure →
      ∀ C : ENNReal, C ≠ 0 → C ≠ ⊤ →
        (∀ D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
          IsFundamentalDomain
            (((AutomorphicForm.sigmaCentralizer
                (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map
                (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom :
                    L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
              (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ.symm
                (Matrix.GeneralLinearGroup.map
                    (Algebra.TensorProduct.includeLeftRingHom :
                      L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                  Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D' τ' →
          ∀ a b : ℝ, 0 < a → a ≤ b →
            τ' (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
              (Matrix.GeneralLinearGroup.det
                (Matrix.GeneralLinearGroup.map
                  (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                    (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
                  (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
              C * ENNReal.ofReal (Real.log (b / a))) →
        (∀ D : Set (Subgroup.centralizer
            ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AdelicGL2 (𝓞 K) K))),
          IsFundamentalDomain
            (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf
              (Subgroup.centralizer
                ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AdelicGL2 (𝓞 K) K)))).op D τ →
          ∀ a b : ℝ, 0 < a → a ≤ b →
            τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
              (Matrix.GeneralLinearGroup.det (t : AdelicGL2 (𝓞 K) K)) ∈ Set.Icc a b}) =
              (Module.finrank K L : ENNReal) * C * ENNReal.ofReal (Real.log (b / a))) →
      ∀ I I' : ℂ,
        AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ.symm
          (@Measure.map (AdelicGL2 (𝓞 L) L) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _
            (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K))
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom))
            (adelicGLHaar (Fin 2) (𝓞 L) L))
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ'
          (φ ∘ Matrix.GeneralLinearGroup.map
            (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
              (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)) I' →
        AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
          (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I → I' = I)
    (C_H : ℝ≥0∞) (hC0 : C_H ≠ 0) (hCt : C_H ≠ ⊤)
    (hC_H : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K),
      Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} →
      IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}) →
      adelicGLHaar (Fin 2) (𝓞 K) K Φ = C_H * ENNReal.ofReal (Real.log (b / a)))
    (δ₀ : GL (Fin 2) L) (b₀ : Kˣ)
    (hδ₀ : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ.symm δ₀) =
      ConjClasses.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) b₀))
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΨs : Ψ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨ : IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ.symm : L →+* L)) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (z : (AdeleRing (𝓞 L) L)ˣ) :
    ∫ x in Ψ, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        AutomorphicForm.sigmaAdelicAct K L D σ.symm (AutomorphicForm.centralScalar (𝓞 L) L z * x))
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      (((c₀ : ℝ) / (Module.finrank K L : ℝ) * (C_H * ENNReal.ofReal (Real.log (β / α))).toReal : ℝ) : ℂ) *
        f (AutomorphicForm.centralScalar (𝓞 K) K
          (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) b₀ *
            (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z)) := by
  by_cases hfirst : ∃ (h : GL (Fin 2) L) (d : Lˣ),
      h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ.symm : L →+* L) h =
        Matrix.GeneralLinearGroup.scalar (Fin 2) d
  ·
    obtain ⟨h, d, hd⟩ := hfirst
    exact P2mCentralPerClass.main_first_kind K L α β hα hαβ D σ.symm hgen c₀ φ hφ hφc f hf hfc hcent
      C_H hC0 hCt hC_H δ₀ b₀ hδ₀ h d hd Ψ hΨs hΨ z
  ·
    have h2 : Module.finrank K L = 2 := by
      rcases hprime.eq_two_or_odd' with h2 | hodd
      · exact h2
      · exact absurd
          (AutomorphicForm.exists_inv_mul_mul_map_eq_scalar_of_sigmaNormPow_eq_map_scalar_of_odd K L σ.symm
            hgen hodd δ₀ b₀ (P2mCentralPerClass.sigmaNormPow_eq_scalar_of_normClassMap_eq hgen hδ₀)) hfirst
    exact AutomorphicForm.setIntegral_sigmaCentralizerDomain_eq_mul_apply_centralScalar_of_normClassMap_eq_mk_scalar_of_forall_ne_scalar_of_finrank_eq_two
      K L h2 α β hα hαβ D σ hσ hgen c₀ φ hφ hφc f hf hfc hcent C_H hC0 hCt hC_H δ₀ b₀ hδ₀
      (fun x e hx => hfirst ⟨x, e, hx⟩) Ψ hΨs hΨ z

end S_AutomorphicForm_setIntegral_sigmaCentralizerDomain_eq_mul_apply_centralScalar_of_normClassMap_eq_mk_scalar_of_central_transfer
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_sigmaCentralizerDomain_eq_mul_apply_centralScalar_of_normClassMap_eq_mk_scalar_of_central_transfer (solution)
