-- Prove2me | solution 1 for AutomorphicForm.exists_twistedTorusFamily_lift_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0d6af00e-27c9-58d6-b2a4-be2d99feabf6

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_AutomorphicForm_twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub
import Theorems.Thm_AutomorphicForm_exists_tensorArch_eq_and_forall_tensorPlace_eq_of_forall_not_mem_mem_semiLocalIntegralSet_and_ext
import Theorems.Thm_AutomorphicForm_exists_diagUnits2_mem_semiLocalIntegralSet_and_normString_eq_toTensorGL_of_ramificationIdx_eq_one
import Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_tensorPlace_preimage_semiLocalIntegralSet_eq_one
import Theorems.Thm_AutomorphicForm_exists_isNormOf_diagUnits2_iff_mem_range_norm_of_isUnit_sub
import Theorems.Thm_AutomorphicForm_normString_apply_eq_one_tmul_norm_apply_of_diagonal
import Theorems.Thm_AutomorphicForm_toTensorGL_mem_semiLocalIntegralSet_iff_mem_localIntegralSet
import Theorems.Thm_NumberField_exists_finset_forall_ramificationIdx_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_twistedTorusFamily_lift_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace K58TFL

section Algebra

variable {A B : Type*} [CommRing A] [CommRing B]

theorem glMap_apply (f : A →+* B) (g : GL (Fin 2) A) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) i j =
      f ((g : Matrix (Fin 2) (Fin 2) A) i j) := rfl

theorem diagUnits2_apply (x y : Aˣ) (i j : Fin 2) :
    ((diagUnits2 x y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j =
      if i = j then (if i = 0 then (x : A) else (y : A)) else 0 := by
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
  fin_cases i <;> fin_cases j <;> simp

theorem inv_diagUnits2 (x y : Aˣ) : (diagUnits2 x y)⁻¹ = diagUnits2 x⁻¹ y⁻¹ := rfl

theorem map_diagUnits2 (f : A →+* B) (x y : Aˣ) :
    Matrix.GeneralLinearGroup.map f (diagUnits2 x y) =
      diagUnits2 (Units.map (f : A →* B) x) (Units.map (f : A →* B) y) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glMap_apply, diagUnits2_apply, diagUnits2_apply]
  split_ifs <;> simp

theorem scalar_mul_diagUnits2 (z a b : Aˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 a b = diagUnits2 (z * a) (z * b) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, diagUnits2_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.scalar, LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.mul_apply,
      Fin.sum_univ_two]

end Algebra

section NormString

open scoped TensorProduct.RightActions

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

omit [FiniteDimensional K L] [IsGalois K L] in
theorem toTensorGL_apply (A : Type) [CommRing A] [Algebra K A] (g : GL (Fin 2) A) (i j : Fin 2) :
    ((AutomorphicForm.toTensorGL K L A g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (1 : L) ⊗ₜ[K] ((g : Matrix (Fin 2) (Fin 2) A) i j) := rfl

include hgen in

theorem normString_diagUnits2_eq_toTensorGL (A : Type) [CommRing A] [Algebra K A]
    (d₁ d₂ : (L ⊗[K] A)ˣ) (x y : Aˣ)
    (h₁ : Algebra.norm A (d₁ : L ⊗[K] A) = x) (h₂ : Algebra.norm A (d₂ : L ⊗[K] A) = y) :
    AutomorphicForm.normString K L A σ (diagUnits2 d₁ d₂) = AutomorphicForm.toTensorGL K L A (diagUnits2 x y) := by
  obtain ⟨h10, h01, h00, h11⟩ :=
    AutomorphicForm.normString_apply_eq_one_tmul_norm_apply_of_diagonal K L σ hgen A (diagUnits2 d₁ d₂)
      (by rw [diagUnits2_apply]; simp) (by rw [diagUnits2_apply]; simp)
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [toTensorGL_apply]
  fin_cases i <;> fin_cases j <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one]
  · rw [h00, diagUnits2_apply, diagUnits2_apply]; simp [h₁]
  · rw [h01, diagUnits2_apply]; simp
  · rw [h10, diagUnits2_apply]; simp
  · rw [h11, diagUnits2_apply, diagUnits2_apply]; simp [h₂]

include hgen in

theorem exists_diagUnits2_normString_eq (A : Type) [CommRing A] [Algebra K A] (x y : Aˣ)
    (hxy : IsUnit ((x : A) - (y : A)))
    (h : ∃ δ₀ : GL (Fin 2) (L ⊗[K] A), AutomorphicForm.IsNormOf K L A σ (diagUnits2 x y) δ₀) :
    ∃ d₁ d₂ : (L ⊗[K] A)ˣ,
      AutomorphicForm.normString K L A σ (diagUnits2 d₁ d₂) = AutomorphicForm.toTensorGL K L A (diagUnits2 x y) := by
  obtain ⟨⟨d₁, hd₁⟩, ⟨d₂, hd₂⟩⟩ :=
    (AutomorphicForm.exists_isNormOf_diagUnits2_iff_mem_range_norm_of_isUnit_sub K L σ hgen A x y hxy).1 h
  exact ⟨d₁, d₂, normString_diagUnits2_eq_toTensorGL K L σ hgen A d₁ d₂ x y hd₁ hd₂⟩

omit [FiniteDimensional K L] [IsGalois K L] in

theorem map_normString {A B : Type} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (f : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] B))
    (hf : ∀ x, f (AutomorphicForm.sigmaGL K L A σ x) = AutomorphicForm.sigmaGL K L B σ (f x))
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    f (AutomorphicForm.normString K L A σ δ) = AutomorphicForm.normString K L B σ (f δ) := by
  have hsc : Function.Semiconj f (AutomorphicForm.sigmaGL K L A σ) (AutomorphicForm.sigmaGL K L B σ) := hf
  simp only [AutomorphicForm.normString, map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact hsc.iterate_right i δ

omit [FiniteDimensional K L] [IsGalois K L] in

theorem isNormOf_map {A B : Type} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (f : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] B)) (g : GL (Fin 2) A →* GL (Fin 2) B)
    (hf : ∀ x, f (AutomorphicForm.sigmaGL K L A σ x) = AutomorphicForm.sigmaGL K L B σ (f x))
    (hfg : ∀ t, f (AutomorphicForm.toTensorGL K L A t) = AutomorphicForm.toTensorGL K L B (g t))
    {γ : GL (Fin 2) A} {δ₀ : GL (Fin 2) (L ⊗[K] A)} (h : AutomorphicForm.IsNormOf K L A σ γ δ₀) :
    AutomorphicForm.IsNormOf K L B σ (g γ) (f δ₀) := by
  obtain ⟨y, hy⟩ := h
  refine ⟨f y, ?_⟩
  unfold AutomorphicForm.IsNormConjugator at hy ⊢
  rw [← hfg, hy, map_mul, map_mul, map_inv, map_normString K L σ f hf]

end NormString

section Transport

open scoped TensorProduct.RightActions
open Topology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  (σ : L ≃ₐ[K] L)

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] in

theorem exists_retraction : ∃ ψ : L →ₗ[K] K, ψ 1 = 1 := by
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K L)
    (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)
  exact ⟨ψ, by simpa using LinearMap.congr_fun hψ (1 : K)⟩

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] in

def retr (ψ : L →ₗ[K] K) : (L ⊗[K] A) →ₗ[A] A where
  toFun z := TensorProduct.lid K A (LinearMap.rTensor A ψ z)
  map_add' x y := by simp only [map_add]
  map_smul' a z := by
    simp only [RingHom.id_apply]
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul l b =>
        rw [AutomorphicForm.rightActions_smul_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, TensorProduct.lid_tmul,
          smul_eq_mul, mul_smul_comm]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, map_add, map_add, smul_add]

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] in
theorem retr_tmul (ψ : L →ₗ[K] K) (l : L) (a : A) : retr K L A ψ (l ⊗ₜ[K] a) = ψ l • a := by
  show TensorProduct.lid K A (LinearMap.rTensor A ψ (l ⊗ₜ[K] a)) = _
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

theorem isClosedEmbedding_tmul_one :
    IsClosedEmbedding (fun a : A => ((1 : L) ⊗ₜ[K] a : L ⊗[K] A)) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.t2Space_tensor K L A
  obtain ⟨ψ, hψ1⟩ := exists_retraction K L
  have hfc : Continuous (fun a : A => ((1 : L) ⊗ₜ[K] a : L ⊗[K] A)) := by
    have h : Continuous fun a : A => a • ((1 : L) ⊗ₜ[K] (1 : A)) := continuous_id.fun_smul continuous_const
    refine h.congr fun a => ?_
    show a • ((1 : L) ⊗ₜ[K] (1 : A)) = (1 : L) ⊗ₜ[K] a
    rw [AutomorphicForm.rightActions_smul_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have hrc : Continuous (retr K L A ψ) := IsModuleTopology.continuous_of_linearMap _
  have hrf : ∀ a : A, retr K L A ψ ((1 : L) ⊗ₜ[K] a) = a := fun a => by
    rw [retr_tmul, hψ1, one_smul]
  have hinj : Function.Injective (fun a : A => ((1 : L) ⊗ₜ[K] a : L ⊗[K] A)) := fun a b h => by
    have := congrArg (retr K L A ψ) h
    rwa [hrf, hrf] at this
  have hrange : IsClosed (Set.range (fun a : A => ((1 : L) ⊗ₜ[K] a : L ⊗[K] A))) := by
    have : Set.range (fun a : A => ((1 : L) ⊗ₜ[K] a : L ⊗[K] A)) =
        {e | (1 : L) ⊗ₜ[K] (retr K L A ψ e) = e} := by
      ext e
      constructor
      · rintro ⟨a, rfl⟩
        show (1 : L) ⊗ₜ[K] (retr K L A ψ ((1 : L) ⊗ₜ[K] a)) = (1 : L) ⊗ₜ[K] a
        rw [hrf]
      · intro he
        exact ⟨_, he⟩
    rw [this]
    exact isClosed_eq (hfc.comp hrc) continuous_id
  refine Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hfc hinj fun C hC => ?_
  have : (fun a : A => ((1 : L) ⊗ₜ[K] a : L ⊗[K] A)) '' C =
      retr K L A ψ ⁻¹' C ∩ Set.range (fun a : A => ((1 : L) ⊗ₜ[K] a : L ⊗[K] A)) := by
    ext e
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨?_, ⟨a, rfl⟩⟩
      show retr K L A ψ ((1 : L) ⊗ₜ[K] a) ∈ C
      rw [hrf]; exact ha
    · rintro ⟨he, ⟨a, rfl⟩⟩
      refine ⟨a, ?_, rfl⟩
      have h' : retr K L A ψ ((1 : L) ⊗ₜ[K] a) ∈ C := he
      rwa [hrf] at h'
  rw [this]
  exact (hC.preimage hrc).inter hrange

theorem isClosedEmbedding_toTensorGL : IsClosedEmbedding (AutomorphicForm.toTensorGL K L A) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have h1 := isClosedEmbedding_tmul_one K L A
  have h2 : IsClosedEmbedding
      (((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom.mapMatrix :
        Matrix (Fin 2) (Fin 2) A →+* Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).toMonoidHom :
        Matrix (Fin 2) (Fin 2) A → Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    have : (((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom.mapMatrix :
        Matrix (Fin 2) (Fin 2) A →+* Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).toMonoidHom :
        Matrix (Fin 2) (Fin 2) A → Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
        Pi.map (fun _ : Fin 2 => Pi.map (fun _ : Fin 2 => fun a : A => ((1 : L) ⊗ₜ[K] a : L ⊗[K] A))) := by
      funext M i j; rfl
    rw [this]
    exact Topology.IsClosedEmbedding.piMap fun _ => Topology.IsClosedEmbedding.piMap fun _ => h1
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  exact h2.units_map

theorem continuous_toTensorGL : Continuous (AutomorphicForm.toTensorGL K L A) :=
  (isClosedEmbedding_toTensorGL K L A).continuous

theorem toTensorGL_injective : Function.Injective (AutomorphicForm.toTensorGL K L A) :=
  (isClosedEmbedding_toTensorGL K L A).injective

omit [T2Space A] in

theorem continuous_sigmaGL : Continuous (AutomorphicForm.sigmaGL K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  refine AutomorphicForm.continuous_glMap _ ?_
  exact IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap

theorem isClosed_twistedCentralizer (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed (AutomorphicForm.twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  have : (AutomorphicForm.twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) =
      {t | t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹ = δ} := by
    ext t; exact AutomorphicForm.mem_sigmaCentralizer_iff
  rw [this]
  exact isClosed_eq ((continuous_id.mul continuous_const).mul ((continuous_sigmaGL K L A σ).inv)) continuous_const

theorem exists_isHaarMeasure_twistedCentralizer [LocallyCompactSpace A] (δ : GL (Fin 2) (L ⊗[K] A)) :
    ∃ τ : Measure (AutomorphicForm.twistedCentralizer K L A σ δ), τ.IsHaarMeasure := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L A
  haveI : LocallyCompactSpace (AutomorphicForm.twistedCentralizer K L A σ δ) :=
    (isClosed_twistedCentralizer K L A σ δ).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L A σ δ) := ⟨rfl⟩
  obtain ⟨K₀⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts
    (AutomorphicForm.twistedCentralizer K L A σ δ)))
  exact ⟨Measure.haarMeasure K₀, Measure.isHaarMeasure_haarMeasure K₀⟩

variable {A σ}

def ceqv (γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A))
    (hEq : AutomorphicForm.twistedCentralizer K L A σ δ =
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))).map (AutomorphicForm.toTensorGL K L A)) :
    Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) ≃ₜ* AutomorphicForm.twistedCentralizer K L A σ δ :=
  let e : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) ≃* AutomorphicForm.twistedCentralizer K L A σ δ :=
    (Subgroup.equivMapOfInjective _ (AutomorphicForm.toTensorGL K L A) (toTensorGL_injective K L A)).trans
      (MulEquiv.subgroupCongr hEq.symm)
  have he : ∀ t, ((e t : AutomorphicForm.twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) =
      AutomorphicForm.toTensorGL K L A (t : GL (Fin 2) A) := fun _ => rfl
  { e with
    continuous_toFun := by
      refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
      have : Subtype.val ∘ (fun t => e t) =
          fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => AutomorphicForm.toTensorGL K L A (t : GL (Fin 2) A) :=
        funext he
      show Continuous (Subtype.val ∘ fun t => e t)
      rw [this]
      exact (continuous_toTensorGL K L A).comp continuous_subtype_val
    continuous_invFun := by
      refine Topology.IsInducing.subtypeVal.continuous_iff.2
        ((isClosedEmbedding_toTensorGL K L A).isInducing.continuous_iff.2 ?_)
      have : AutomorphicForm.toTensorGL K L A ∘ Subtype.val ∘ (fun s => e.symm s) = Subtype.val := by
        funext s
        show AutomorphicForm.toTensorGL K L A ((e.symm s : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) :
          GL (Fin 2) A) = s
        rw [← he, MulEquiv.apply_symm_apply]
      show Continuous (AutomorphicForm.toTensorGL K L A ∘ Subtype.val ∘ fun s => e.symm s)
      rw [this]
      exact continuous_subtype_val }

theorem coe_ceqv_apply (γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A))
    (hEq : AutomorphicForm.twistedCentralizer K L A σ δ =
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))).map (AutomorphicForm.toTensorGL K L A))
    (t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) :
    ((ceqv K L γ δ hEq t : AutomorphicForm.twistedCentralizer K L A σ δ) : GL (Fin 2) (L ⊗[K] A)) =
      AutomorphicForm.toTensorGL K L A (t : GL (Fin 2) A) := rfl

variable (γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A))
    (hEq : AutomorphicForm.twistedCentralizer K L A σ δ =
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))).map (AutomorphicForm.toTensorGL K L A))

theorem isHaarMeasure_map_ceqv (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))))
    [τ.IsHaarMeasure] : (Measure.map (ceqv K L γ δ hEq) τ).IsHaarMeasure := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L A σ δ) := ⟨rfl⟩
  exact ContinuousMulEquiv.isHaarMeasure_map τ (ceqv K L γ δ hEq)

theorem integral_map_ceqv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))) (g : GL (Fin 2) (L ⊗[K] A) → E) :
    ∫ s, g (s : GL (Fin 2) (L ⊗[K] A)) ∂(Measure.map (ceqv K L γ δ hEq) τ) =
      ∫ t, g (AutomorphicForm.toTensorGL K L A (t : GL (Fin 2) A)) ∂τ := by
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L A σ δ) := ⟨rfl⟩
  have h := integral_map_equiv (μ := τ) (ceqv K L γ δ hEq).toHomeomorph.toMeasurableEquiv
    (fun s : AutomorphicForm.twistedCentralizer K L A σ δ => g (s : GL (Fin 2) (L ⊗[K] A)))
  rw [Homeomorph.toMeasurableEquiv_coe] at h
  exact h

theorem aestronglyMeasurable_comp_ceqv {E : Type*} [TopologicalSpace E]
    (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))) (g : GL (Fin 2) (L ⊗[K] A) → E)
    (h : AEStronglyMeasurable (fun s : AutomorphicForm.twistedCentralizer K L A σ δ => g (s : GL (Fin 2) (L ⊗[K] A)))
      (Measure.map (ceqv K L γ δ hEq) τ)) :
    AEStronglyMeasurable
      (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => g (AutomorphicForm.toTensorGL K L A (t : GL (Fin 2) A))) τ := by
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L A σ δ) := ⟨rfl⟩
  have hm : Measurable (ceqv K L γ δ hEq) := (ceqv K L γ δ hEq).continuous.measurable
  exact h.comp_measurable hm

theorem coupled_map_ceqv (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))) :
    AutomorphicForm.Coupled K L A σ γ δ 1 τ (Measure.map (ceqv K L γ δ hEq) τ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  letI := AutomorphicForm.glBorelOf (L ⊗[K] A)
  haveI := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L A σ δ) := ⟨rfl⟩
  unfold AutomorphicForm.Coupled
  have hm1 : Measurable (fun t : AutomorphicForm.twistedCentralizer K L A σ δ =>
      (1 : GL (Fin 2) (L ⊗[K] A))⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * 1) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hm2 : Measurable (ceqv K L γ δ hEq) := (ceqv K L γ δ hEq).continuous.measurable
  rw [Measure.map_map hm1 hm2]
  congr 1
  funext t
  simp only [Function.comp_apply, inv_one, one_mul, mul_one, coe_ceqv_apply]

theorem map_ceqv_apply_preimage (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))))
    (S : Set (GL (Fin 2) A)) (S' : Set (GL (Fin 2) (L ⊗[K] A))) (hS' : IsOpen S')
    (h : ∀ t : GL (Fin 2) A, AutomorphicForm.toTensorGL K L A t ∈ S' ↔ t ∈ S) :
    (Measure.map (ceqv K L γ δ hEq) τ) (Subtype.val ⁻¹' S') = τ (Subtype.val ⁻¹' S) := by
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L A σ δ) := ⟨rfl⟩
  have hm : Measurable (ceqv K L γ δ hEq) := (ceqv K L γ δ hEq).continuous.measurable
  rw [Measure.map_apply hm (hS'.preimage continuous_subtype_val).measurableSet]
  congr 1
  ext t
  simp only [Set.mem_preimage, coe_ceqv_apply, h]

end Transport

section TransportEq

open scoped TensorProduct.RightActions

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  {A : Type} [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
  {σ : L ≃ₐ[K] L}
  (γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A))
  (hEq : AutomorphicForm.twistedCentralizer K L A σ δ =
    (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))).map (AutomorphicForm.toTensorGL K L A))
  (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))))
  (τ' : Measure (AutomorphicForm.twistedCentralizer K L A σ δ))
  (hτ' : τ' = Measure.map (ceqv K L γ δ hEq) τ)

include hτ' in
theorem isHaarMeasure_of_eq_map [τ.IsHaarMeasure] : τ'.IsHaarMeasure := by
  subst hτ'; exact isHaarMeasure_map_ceqv K L γ δ hEq τ

include hτ' in
theorem integral_of_eq_map {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : GL (Fin 2) (L ⊗[K] A) → E) :
    ∫ s, g (s : GL (Fin 2) (L ⊗[K] A)) ∂τ' = ∫ t, g (AutomorphicForm.toTensorGL K L A (t : GL (Fin 2) A)) ∂τ := by
  subst hτ'; exact integral_map_ceqv K L γ δ hEq τ g

include hτ' in
theorem coupled_of_eq_map : AutomorphicForm.Coupled K L A σ γ δ 1 τ τ' := by
  subst hτ'; exact coupled_map_ceqv K L γ δ hEq τ

include hτ' in
theorem apply_preimage_of_eq_map (S : Set (GL (Fin 2) A)) (S' : Set (GL (Fin 2) (L ⊗[K] A))) (hS' : IsOpen S')
    (h : ∀ t : GL (Fin 2) A, AutomorphicForm.toTensorGL K L A t ∈ S' ↔ t ∈ S) :
    τ' (Subtype.val ⁻¹' S') = τ (Subtype.val ⁻¹' S) := by
  subst hτ'; exact map_ceqv_apply_preimage K L γ δ hEq τ S S' hS' h

end TransportEq

section Assemble

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem semiLocalEval_apply (v : HeightOneSpectrum (𝓞 K)) (a : FiniteAdeleRing (𝓞 L) L) :
    AutomorphicForm.semiLocalEval K L v a =
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w : v.Extension (𝓞 L) => a w.1) :=
  rfl

theorem eq_of_forall_semiLocalEval_eq {a b : FiniteAdeleRing (𝓞 L) L}
    (h : ∀ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.semiLocalEval K L v a = AutomorphicForm.semiLocalEval K L v b) :
    a = b := by
  refine RestrictedProduct.ext _ _ fun w' => ?_
  have hw := h (HeightOneSpectrum.under (𝓞 K) w')
  rw [semiLocalEval_apply, semiLocalEval_apply] at hw
  have hinj := (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L)
    (HeightOneSpectrum.under (𝓞 K) w')).symm.injective hw
  exact congrFun hinj (⟨w', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w').Extension (𝓞 L))

theorem mem_semiLocalIntegers_iff_forall (v : HeightOneSpectrum (𝓞 K)) (x : L ⊗[K] v.adicCompletion K) :
    x ∈ AutomorphicForm.semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L),
        HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x w ∈ w.1.adicCompletionIntegers L := by
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage, AutomorphicForm.piIntegers,
    Set.mem_univ_pi]
  rfl

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def assemble (y : ∀ v : HeightOneSpectrum (𝓞 K), L ⊗[K] v.adicCompletion K)
    (hy : ∀ v ∉ S, y v ∈ AutomorphicForm.semiLocalIntegers K L v) : FiniteAdeleRing (𝓞 L) L :=
  ⟨fun w => (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) (HeightOneSpectrum.under (𝓞 K) w)
      (y (HeightOneSpectrum.under (𝓞 K) w)) ⟨w, rfl⟩ : w.adicCompletion L),
    by
      refine Filter.eventually_cofinite.mpr ?_
      refine ((S.finite_toSet.preimage' (f := fun w : HeightOneSpectrum (𝓞 L) => HeightOneSpectrum.under (𝓞 K) w)
        fun v _ => ?_).subset ?_)
      · haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
        refine (Set.finite_range fun w : v.Extension (𝓞 L) => (w.1 : HeightOneSpectrum (𝓞 L))).subset ?_
        intro w hw
        exact ⟨⟨w, hw⟩, rfl⟩
      · intro w hw
        by_contra hS
        exact hw ((mem_semiLocalIntegers_iff_forall K L _ _).1 (hy _ hS) ⟨w, rfl⟩)⟩

theorem semiLocalEval_assemble (y : ∀ v : HeightOneSpectrum (𝓞 K), L ⊗[K] v.adicCompletion K)
    (hy : ∀ v ∉ S, y v ∈ AutomorphicForm.semiLocalIntegers K L v) (v : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.semiLocalEval K L v (assemble K L S y hy) = y v := by
  rw [semiLocalEval_apply, AlgEquiv.symm_apply_eq]
  funext w
  obtain ⟨w, hw⟩ := w
  subst hw
  rfl

def assembleUnit (d : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ)
    (hd : ∀ v ∉ S, ((d v : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
        AutomorphicForm.semiLocalIntegers K L v ∧
      (((d v)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
        AutomorphicForm.semiLocalIntegers K L v) :
    (FiniteAdeleRing (𝓞 L) L)ˣ where
  val := assemble K L S (fun v => ((d v : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K))
    (fun v hv => (hd v hv).1)
  inv := assemble K L S (fun v => (((d v)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K))
    (fun v hv => (hd v hv).2)
  val_inv := eq_of_forall_semiLocalEval_eq K L fun v => by
    rw [map_mul, semiLocalEval_assemble, semiLocalEval_assemble, map_one, Units.mul_inv]
  inv_val := eq_of_forall_semiLocalEval_eq K L fun v => by
    rw [map_mul, semiLocalEval_assemble, semiLocalEval_assemble, map_one, Units.inv_mul]

def assembleAll (da : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    (d : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ)
    (hd : ∀ v ∉ S, ((d v : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
        AutomorphicForm.semiLocalIntegers K L v ∧
      (((d v)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
        AutomorphicForm.semiLocalIntegers K L v) :
    (L ⊗[K] AdeleRing (𝓞 K) K)ˣ :=
  let a : (InfiniteAdeleRing L)ˣ := Units.map ((AutomorphicForm.archIdentEquiv K L).toRingHom : _ →* _) da
  let f : (FiniteAdeleRing (𝓞 L) L)ˣ := assembleUnit K L S d hd
  let y : (AdeleRing (𝓞 L) L)ˣ :=
    ⟨((a : InfiniteAdeleRing L), (f : FiniteAdeleRing (𝓞 L) L)),
      (((a⁻¹ : (InfiniteAdeleRing L)ˣ) : InfiniteAdeleRing L), ((f⁻¹ : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L)),
      Prod.ext a.mul_inv f.mul_inv, Prod.ext a.inv_mul f.inv_mul⟩
  Units.map ((AutomorphicForm.baseChangeEquiv K L).symm.toRingHom : _ →* _) y

theorem coe_assembleAll (da : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    (d : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ)
    (hd : ∀ v ∉ S, ((d v : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
        AutomorphicForm.semiLocalIntegers K L v ∧
      (((d v)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
        AutomorphicForm.semiLocalIntegers K L v) :
    ((assembleAll K L S da d hd : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) : L ⊗[K] AdeleRing (𝓞 K) K) =
      (AutomorphicForm.baseChangeEquiv K L).symm
        ((AutomorphicForm.archIdentEquiv K L (da : L ⊗[K] InfiniteAdeleRing K),
          (assembleUnit K L S d hd : FiniteAdeleRing (𝓞 L) L)) : AdeleRing (𝓞 L) L) := rfl

theorem tensorArchHom_assembleAll (da : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    (d : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ)
    (hd : ∀ v ∉ S, ((d v : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
        AutomorphicForm.semiLocalIntegers K L v ∧
      (((d v)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
        AutomorphicForm.semiLocalIntegers K L v) :
    AutomorphicForm.tensorArchHom K L (assembleAll K L S da d hd : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) = da := by
  apply (AutomorphicForm.archIdentEquiv K L).injective
  rw [AutomorphicForm.archIdentEquiv_apply K L (AutomorphicForm.tensorArchHom K L _),
    ← AutomorphicForm.fst_baseChangeEquiv, coe_assembleAll, RingEquiv.apply_symm_apply]

theorem tensorPlaceHom_assembleAll (da : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    (d : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ)
    (hd : ∀ v ∉ S, ((d v : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
        AutomorphicForm.semiLocalIntegers K L v ∧
      (((d v)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
        AutomorphicForm.semiLocalIntegers K L v) (v : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.tensorPlaceHom K L v (assembleAll K L S da d hd : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) = d v := by
  rw [← AutomorphicForm.semiLocalEval_snd_baseChangeEquiv, coe_assembleAll, RingEquiv.apply_symm_apply]
  exact semiLocalEval_assemble K L S (fun v => ((d v : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K))
    (fun v hv => (hd v hv).1) v

theorem tensorArch_diagUnits2_assembleAll (da₁ da₂ : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    (d₁ d₂ : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ) (hd₁ hd₂) :
    AutomorphicForm.tensorArch K L (diagUnits2 (assembleAll K L S da₁ d₁ hd₁) (assembleAll K L S da₂ d₂ hd₂)) =
      diagUnits2 da₁ da₂ := by
  unfold AutomorphicForm.tensorArch
  rw [map_diagUnits2]
  congr 1 <;> exact Units.ext (tensorArchHom_assembleAll K L S _ _ _)

theorem tensorPlace_diagUnits2_assembleAll (da₁ da₂ : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    (d₁ d₂ : ∀ v : HeightOneSpectrum (𝓞 K), (L ⊗[K] v.adicCompletion K)ˣ) (hd₁ hd₂) (v : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.tensorPlace K L v (diagUnits2 (assembleAll K L S da₁ d₁ hd₁) (assembleAll K L S da₂ d₂ hd₂)) =
      diagUnits2 (d₁ v) (d₂ v) := by
  unfold AutomorphicForm.tensorPlace
  rw [map_diagUnits2]
  congr 1 <;> exact Units.ext (tensorPlaceHom_assembleAll K L S _ _ _ v)

end Assemble

section Lift

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
theorem gamma_eq (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) = diagUnits2 (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) z := by
  show Matrix.GeneralLinearGroup.scalar (Fin 2) z * _ = _
  rw [scalar_mul_diagUnits2, mul_one]

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
theorem glArch_gamma_eq (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) = diagUnits2 (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)))
      (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) z) := by
  rw [gamma_eq]
  unfold AdelicLevel.glArch
  rw [map_diagUnits2]

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
theorem finComponent_gamma_eq (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) = diagUnits2
      (Units.map (AdelicLevel.finAdeleEval (𝓞 K) K v : FiniteAdeleRing (𝓞 K) K →* v.adicCompletion K)
        (Units.map (AdelicLevel.adeleFin (𝓞 K) K : AdeleRing (𝓞 K) K →* FiniteAdeleRing (𝓞 K) K) (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))))
      (Units.map (AdelicLevel.finAdeleEval (𝓞 K) K v : FiniteAdeleRing (𝓞 K) K →* v.adicCompletion K)
        (Units.map (AdelicLevel.adeleFin (𝓞 K) K : AdeleRing (𝓞 K) K →* FiniteAdeleRing (𝓞 K) K) z)) := by
  rw [gamma_eq]
  unfold AdelicLevel.glFin AdelicLevel.finComponent
  rw [map_diagUnits2, map_diagUnits2]

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in

theorem isUnit_sub_gamma (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (hu : (u : K) ≠ 1) :
    IsUnit (((z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) - ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) := by
  have h1 : IsUnit (algebraMap K (AdeleRing (𝓞 K) K) ((u : K) - 1)) :=
    (Ne.isUnit (sub_ne_zero.2 hu)).map _
  have : ((z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) - ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) =
      ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) ((u : K) - 1) := by
    rw [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, map_sub, map_one]; ring
  rw [this]
  exact z.isUnit.mul h1

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
theorem isUnit_sub_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x y : Aˣ)
    (h : IsUnit ((x : A) - (y : A))) :
    IsUnit ((Units.map (f : A →* B) x : B) - (Units.map (f : A →* B) y : B)) := by
  simpa [← map_sub] using h.map f

def intUnit (v : HeightOneSpectrum (𝓞 K)) (a : (AdeleRing (𝓞 K) K)ˣ)
    (ha : (((a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K)
    (ha' : ((((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
      v.adicCompletionIntegers K) :
    (v.adicCompletionIntegers K)ˣ where
  val := ⟨_, ha⟩
  inv := ⟨_, ha'⟩
  val_inv := Subtype.ext (by
    have h := congrArg (fun t : AdeleRing (𝓞 K) K => (t.2 : FiniteAdeleRing (𝓞 K) K) v) a.mul_inv
    exact h)
  inv_val := Subtype.ext (by
    have h := congrArg (fun t : AdeleRing (𝓞 K) K => (t.2 : FiniteAdeleRing (𝓞 K) K) v) a.inv_mul
    exact h)

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
theorem map_intUnit (v : HeightOneSpectrum (𝓞 K)) (a : (AdeleRing (𝓞 K) K)ˣ) (ha ha') :
    Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) :
        v.adicCompletionIntegers K →* v.adicCompletion K) (intUnit K v a ha ha') =
      Units.map (AdelicLevel.finAdeleEval (𝓞 K) K v : FiniteAdeleRing (𝓞 K) K →* v.adicCompletion K)
        (Units.map (AdelicLevel.adeleFin (𝓞 K) K : AdeleRing (𝓞 K) K →* FiniteAdeleRing (𝓞 K) K) a) :=
  Units.ext rfl

def IsGood (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  (∀ w' : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w' = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal = 1) ∧
  ((((z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
    ((((z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
      v.adicCompletionIntegers K) ∧
  ((((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
    ((((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K)

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
theorem finite_setOf_not_mem (a : (AdeleRing (𝓞 K) K)ˣ) :
    {v : HeightOneSpectrum (𝓞 K) |
      ¬ ((((a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v ∈
        v.adicCompletionIntegers K)}.Finite := by
  have h := Filter.eventually_cofinite.1 (((a : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2).2
  exact h

omit [FiniteDimensional K L] [IsGalois K L] in

theorem finite_not_isGood (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    {v : HeightOneSpectrum (𝓞 K) | ¬ IsGood K L u z v}.Finite := by
  obtain ⟨S₀, hS₀⟩ := NumberField.exists_finset_forall_ramificationIdx_eq_one K L
  refine ((((S₀.finite_toSet.union (finite_setOf_not_mem K (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)))).union
    (finite_setOf_not_mem K (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u))⁻¹)).union (finite_setOf_not_mem K z)).union
    (finite_setOf_not_mem K z⁻¹)).subset fun v hv => ?_
  by_contra hmem
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hmem
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := hmem
  exact hv ⟨fun w' hw' => hS₀ w' (by rw [hw']; exact h0), ⟨h1, h2⟩, ⟨h3, h4⟩⟩

include hgen in

theorem exists_arch (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ p : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
      ((u : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ₀) →
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 p.1 p.2) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) := by
  classical
  by_cases h : (u : K) ≠ 1 ∧ ∃ δ₀, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ₀
  · obtain ⟨hu, hguard⟩ := h
    rw [glArch_gamma_eq] at hguard
    obtain ⟨d₁, d₂, hN⟩ := exists_diagUnits2_normString_eq K L σ hgen (InfiniteAdeleRing K) _ _
      (isUnit_sub_map _ _ _ (isUnit_sub_gamma K u z hu)) hguard
    exact ⟨(d₁, d₂), fun _ _ => by rw [glArch_gamma_eq]; exact hN⟩
  · exact ⟨(1, 1), fun hu hguard => absurd ⟨hu, hguard⟩ h⟩

include hgen in

theorem exists_local (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ∃ p : (L ⊗[K] v.adicCompletion K)ˣ × (L ⊗[K] v.adicCompletion K)ˣ,
      (IsGood K L u z v → diagUnits2 p.1 p.2 ∈ AutomorphicForm.semiLocalIntegralSet K L v) ∧
      ((u : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ₀) →
        AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 p.1 p.2) =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) := by
  classical
  by_cases hg : IsGood K L u z v
  · obtain ⟨hram, ⟨hx, hx'⟩, ⟨hy, hy'⟩⟩ := hg
    obtain ⟨d₁, d₂, hint, hN⟩ :=
      AutomorphicForm.exists_diagUnits2_mem_semiLocalIntegralSet_and_normString_eq_toTensorGL_of_ramificationIdx_eq_one
        K L σ hgen v hram (intUnit K v (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u)) hx hx') (intUnit K v z hy hy')
    refine ⟨(d₁, d₂), fun _ => hint, fun _ _ => ?_⟩
    rw [hN, map_intUnit, map_intUnit, finComponent_gamma_eq]
  · by_cases h2 : (u : K) ≠ 1 ∧ ∃ δ₀, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ₀
    · obtain ⟨hu, hguard⟩ := h2
      rw [finComponent_gamma_eq] at hguard
      obtain ⟨d₁, d₂, hN⟩ := exists_diagUnits2_normString_eq K L σ hgen (v.adicCompletion K) _ _
        (isUnit_sub_map _ _ _ (isUnit_sub_map _ _ _ (isUnit_sub_gamma K u z hu))) hguard
      refine ⟨(d₁, d₂), fun h => absurd h hg, fun _ _ => ?_⟩
      rw [finComponent_gamma_eq]; exact hN
    · exact ⟨(1, 1), fun h => absurd h hg, fun hu hguard => absurd ⟨hu, hguard⟩ h2⟩

include hgen in

theorem exists_lift (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ D : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ × (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
      ((u : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ₀) →
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ
            (AutomorphicForm.tensorArch K L (diagUnits2 D.1 D.2)) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), (u : K) ≠ 1 →
        (∃ δ₀, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ₀) →
        AutomorphicForm.normString K L (v.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L v (diagUnits2 D.1 D.2)) =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) := by
  classical
  obtain ⟨pa, hpa⟩ := exists_arch K L σ hgen u z
  choose p hp using exists_local K L σ hgen u z
  have hfin := finite_not_isGood K L u z
  have hS : ∀ v ∉ hfin.toFinset, IsGood K L u z v := fun v hv => by
    by_contra h
    exact hv (hfin.mem_toFinset.2 h)
  have hd₁ : ∀ v ∉ hfin.toFinset,
      (((p v).1 : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈ AutomorphicForm.semiLocalIntegers K L v ∧
        ((((p v).1)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
          AutomorphicForm.semiLocalIntegers K L v := by
    intro v hv
    have h := AutomorphicForm.mem_integralUnitsSet.1 ((hp v).1 (hS v hv))
    rw [inv_diagUnits2] at h
    exact ⟨by simpa [diagUnits2_apply] using h.1 0 0, by simpa [diagUnits2_apply] using h.2 0 0⟩
  have hd₂ : ∀ v ∉ hfin.toFinset,
      (((p v).2 : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈ AutomorphicForm.semiLocalIntegers K L v ∧
        ((((p v).2)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
          AutomorphicForm.semiLocalIntegers K L v := by
    intro v hv
    have h := AutomorphicForm.mem_integralUnitsSet.1 ((hp v).1 (hS v hv))
    rw [inv_diagUnits2] at h
    exact ⟨by simpa [diagUnits2_apply] using h.1 1 1, by simpa [diagUnits2_apply] using h.2 1 1⟩
  refine ⟨(assembleAll K L hfin.toFinset pa.1 (fun v => (p v).1) hd₁,
    assembleAll K L hfin.toFinset pa.2 (fun v => (p v).2) hd₂), fun hu hg => ?_, fun v hu hg => ?_⟩
  · rw [tensorArch_diagUnits2_assembleAll]
    exact hpa hu hg
  · rw [tensorPlace_diagUnits2_assembleAll]
    exact (hp v).2 hu hg

end Lift

section Main

open scoped TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

omit [FiniteDimensional K L] [IsGalois K L] in
theorem archGuard_of_global (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ)
    (hg : ∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀) :
    ∃ δ₀, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ₀ := by
  obtain ⟨δ₀, h⟩ := hg
  exact ⟨_, isNormOf_map K L σ (AutomorphicForm.tensorArch K L) (AdelicLevel.glArch (𝓞 K) K)
    (AutomorphicForm.tensorArch_sigmaGL K L σ) (AutomorphicForm.tensorArch_toTensorGL K L) h⟩

omit [FiniteDimensional K L] [IsGalois K L] in
theorem localGuard_of_global (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K))
    (hg : ∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀) :
    ∃ δ₀, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ₀ := by
  obtain ⟨δ₀, h⟩ := hg
  exact ⟨_, isNormOf_map K L σ (AutomorphicForm.tensorPlace K L v)
    ((AdelicLevel.finComponent (𝓞 K) K v).comp (AdelicLevel.glFin (𝓞 K) K))
    (AutomorphicForm.tensorPlace_sigmaGL K L σ v) (AutomorphicForm.tensorPlace_toTensorGL K L v) h⟩

omit [FiniteDimensional K L] [IsGalois K L] in

theorem normString_eq_of_components (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hA : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ) =
      AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
    (hF : ∀ v : HeightOneSpectrum (𝓞 K),
      AutomorphicForm.normString K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v δ) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) :
    AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ = AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) := by
  refine (AutomorphicForm.exists_tensorArch_eq_and_forall_tensorPlace_eq_of_forall_not_mem_mem_semiLocalIntegralSet_and_ext
    K L).2 _ _ ?_ ?_
  · rw [map_normString K L σ (AutomorphicForm.tensorArch K L) (AutomorphicForm.tensorArch_sigmaGL K L σ),
      AutomorphicForm.tensorArch_toTensorGL]
    exact hA
  · intro v
    rw [map_normString K L σ (AutomorphicForm.tensorPlace K L v) (AutomorphicForm.tensorPlace_sigmaGL K L σ v),
      AutomorphicForm.tensorPlace_toTensorGL]
    exact hF v

include hgen in
theorem twistedCentralizer_eq_global (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (hu : (u : K) ≠ 1)
    (D₁ D₂ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ (diagUnits2 D₁ D₂) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) :
    AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (diagUnits2 D₁ D₂) =
      (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))).map
        (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)) := by
  rw [gamma_eq] at hN ⊢
  exact AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub
    K L σ hgen (AdeleRing (𝓞 K) K) _ _ (isUnit_sub_gamma K u z hu) _ _ hN

include hgen in
theorem twistedCentralizer_eq_arch (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (hu : (u : K) ≠ 1)
    (D₁ D₂ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L (diagUnits2 D₁ D₂)) =
      AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) :
    AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L (diagUnits2 D₁ D₂)) =
      (Subgroup.centralizer ({(AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))} : Set (GL (Fin 2) (InfiniteAdeleRing K)))).map
        (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)) := by
  rw [glArch_gamma_eq] at hN ⊢
  unfold AutomorphicForm.tensorArch at hN ⊢
  rw [map_diagUnits2] at hN ⊢
  exact AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub
    K L σ hgen (InfiniteAdeleRing K) _ _ (isUnit_sub_map _ _ _ (isUnit_sub_gamma K u z hu)) _ _ hN

include hgen in
theorem twistedCentralizer_eq_local (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) (hu : (u : K) ≠ 1)
    (D₁ D₂ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v (diagUnits2 D₁ D₂)) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) :
    AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v (diagUnits2 D₁ D₂)) =
      (Subgroup.centralizer ({(AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))} : Set (GL (Fin 2) (v.adicCompletion K)))).map
        (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) := by
  rw [finComponent_gamma_eq] at hN ⊢
  unfold AutomorphicForm.tensorPlace at hN ⊢
  rw [map_diagUnits2] at hN ⊢
  exact AutomorphicForm.twistedCentralizer_diagUnits2_eq_map_toTensorGL_centralizer_of_normString_eq_of_isUnit_sub
    K L σ hgen (v.adicCompletion K) _ _
    (isUnit_sub_map _ _ _ (isUnit_sub_map _ _ _ (isUnit_sub_gamma K u z hu))) _ _ hN

omit [IsGalois K L] in

theorem restrictedProduct_transport
    (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (eG : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ =
      (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))).map
        (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)))
    (eA : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ) =
      (Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))).map
        (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)))
    (τG : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (τA : Measure (Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))))
    (τF : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))
        (AutomorphicForm.localCentralizerBorel K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))))
    (τG' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ))
    (τA' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ)))
    (τF' : ∀ v : HeightOneSpectrum (𝓞 K),
      Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v δ)))
    (hG : τG' = Measure.map (ceqv K L γ δ eG) τG)
    (hA : τA' = Measure.map (ceqv K L _ _ eA) τA)
    (cT : ℝ)
    (hT : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ)]
          (fun t => Wa t) τA →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))] (fun t => WS v t) (τF v)) →
        (∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τG = cT * (∫ t, Wa t ∂τA) * ∏ v ∈ S, ∫ t, WS v t ∂(τF v))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hF : ∀ v ∈ S, ∃ eF : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v δ) =
        (Subgroup.centralizer ({AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)} :
          Set (GL (Fin 2) (v.adicCompletion K)))).map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)),
      τF' v = Measure.map (ceqv K L _ _ eF) (τF v))
    (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
    (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
    (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hWa : AEStronglyMeasurable
      (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ) =>
        Wa (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τA')
    (hWS : ∀ v ∈ S, AEStronglyMeasurable
      (fun t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v δ) =>
        WS v (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K))) (τF' v))
    (hfac : ∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
      (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
        W t = Wa (AutomorphicForm.tensorArch K L t) * ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t))
    (hvan : ∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
      (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) → W t = 0) :
    ∫ t, W t ∂τG' = cT * (∫ t, Wa t ∂τA') * ∏ v ∈ S, ∫ t, WS v t ∂(τF' v) := by
  classical
  subst hG hA
  have hWS' : ∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))]
        (fun t => WS v (AutomorphicForm.toTensorGL K L (v.adicCompletion K) t)) (τF v) := by
    intro v hv
    obtain ⟨eF, hF'⟩ := hF v hv
    have h := hWS v hv
    rw [hF'] at h
    exact aestronglyMeasurable_comp_ceqv K L _ _ _ (τF v) (fun x => WS v x) h
  have key := hT S (fun x => W (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) x))
    (fun a => Wa (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) a))
    (fun v x => WS v (AutomorphicForm.toTensorGL K L (v.adicCompletion K) x))
    (aestronglyMeasurable_comp_ceqv K L _ _ _ τA (fun x => Wa x) hWa) hWS' ?_ ?_
  · have hprod : (∏ v ∈ S, ∫ t, WS v (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∂(τF' v)) =
        ∏ v ∈ S, ∫ t, WS v (AutomorphicForm.toTensorGL K L (v.adicCompletion K) (t : GL (Fin 2) (v.adicCompletion K)))
          ∂(τF v) := by
      refine Finset.prod_congr rfl fun v hv => ?_
      obtain ⟨eF, hF'⟩ := hF v hv
      rw [hF', integral_map_ceqv]
    rw [integral_map_ceqv, integral_map_ceqv, hprod]
    exact key
  · intro t ht
    have h := hfac (ceqv K L γ δ eG t) (fun v hv => by
      rw [coe_ceqv_apply, AutomorphicForm.tensorPlace_toTensorGL,
        AutomorphicForm.toTensorGL_mem_semiLocalIntegralSet_iff_mem_localIntegralSet]
      exact ht v hv)
    simp only [coe_ceqv_apply, AutomorphicForm.tensorArch_toTensorGL, AutomorphicForm.tensorPlace_toTensorGL] at h
    exact h
  · intro t ht
    obtain ⟨v, hv, hnot⟩ := ht
    have hmem : AutomorphicForm.tensorPlace K L v
        ((ceqv K L γ δ eG t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ) :
          GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∉ AutomorphicForm.semiLocalIntegralSet K L v := by
      rw [coe_ceqv_apply, AutomorphicForm.tensorPlace_toTensorGL,
        AutomorphicForm.toTensorGL_mem_semiLocalIntegralSet_iff_mem_localIntegralSet]
      exact hnot
    have h := hvan _ ⟨v, hv, hmem⟩
    simp only [coe_ceqv_apply] at h
    exact h

end Main

section LiftFull

open scoped TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

include hgen in

theorem exists_lift_full (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ D : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ × (L ⊗[K] AdeleRing (𝓞 K) K)ˣ,
      ((u : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ₀) →
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ
            (AutomorphicForm.tensorArch K L (diagUnits2 D.1 D.2)) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), (u : K) ≠ 1 →
        (∃ δ₀, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ₀) →
        AutomorphicForm.normString K L (v.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L v (diagUnits2 D.1 D.2)) =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) ∧
      ((u : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀) →
        AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ (diagUnits2 D.1 D.2) =
          AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) ∧
      ((u : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀) →
        AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (diagUnits2 D.1 D.2) =
          (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))).map
            (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K))) ∧
      ((u : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ₀) →
        AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
            (AutomorphicForm.tensorArch K L (diagUnits2 D.1 D.2)) =
          (Subgroup.centralizer ({(AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))} : Set (GL (Fin 2) (InfiniteAdeleRing K)))).map
            (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K))) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), (u : K) ≠ 1 →
        (∃ δ₀, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ₀) →
        AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
            (AutomorphicForm.tensorPlace K L v (diagUnits2 D.1 D.2)) =
          (Subgroup.centralizer ({(AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))} : Set (GL (Fin 2) (v.adicCompletion K)))).map
            (AutomorphicForm.toTensorGL K L (v.adicCompletion K))) := by
  obtain ⟨D, hA, hF⟩ := exists_lift K L σ hgen u z
  have hN : (u : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀) →
      AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ (diagUnits2 D.1 D.2) =
        AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) :=
    fun hu hg => normString_eq_of_components K L σ u z _ (hA hu (archGuard_of_global K L σ u z hg))
      (fun v => hF v hu (localGuard_of_global K L σ u z v hg))
  exact ⟨D, hA, hF, hN, fun hu hg => twistedCentralizer_eq_global K L σ hgen u z hu _ _ (hN hu hg),
    fun hu hg => twistedCentralizer_eq_arch K L σ hgen u z hu _ _ (hA hu hg),
    fun v hu hg => twistedCentralizer_eq_local K L σ hgen u z v hu _ _ (hF v hu hg)⟩

end LiftFull

section Families

open scoped TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] (σ : L ≃ₐ[K] L)

omit [NumberField K] [NumberField L] in
theorem exists_transportFamily {ι κ : Type*} (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A] [LocallyCompactSpace A]
    (P : ι → κ → Prop) (γ : ι → κ → GL (Fin 2) A) (δ : ι → κ → GL (Fin 2) (L ⊗[K] A))
    (hEq : ∀ i j, P i j → AutomorphicForm.twistedCentralizer K L A σ (δ i j) =
      (Subgroup.centralizer ({γ i j} : Set (GL (Fin 2) A))).map (AutomorphicForm.toTensorGL K L A))
    (τ : ∀ i j, Measure (Subgroup.centralizer ({γ i j} : Set (GL (Fin 2) A)))) :
    ∃ τ' : ∀ i j, Measure (AutomorphicForm.twistedCentralizer K L A σ (δ i j)),
      (∀ i j (h : P i j), τ' i j = Measure.map (ceqv K L (γ i j) (δ i j) (hEq i j h)) (τ i j)) ∧
      (∀ i j, ¬ P i j → (τ' i j).IsHaarMeasure) := by
  classical
  refine ⟨fun i j => if h : P i j then Measure.map (ceqv K L (γ i j) (δ i j) (hEq i j h)) (τ i j)
      else (exists_isHaarMeasure_twistedCentralizer K L A σ (δ i j)).choose,
    fun i j h => dif_pos h, fun i j h => ?_⟩
  simp only [dif_neg h]
  exact (exists_isHaarMeasure_twistedCentralizer K L A σ (δ i j)).choose_spec

theorem exists_localFamily {ι κ : Type*} (P : ι → κ → HeightOneSpectrum (𝓞 K) → Prop)
    (γ : ι → κ → ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (δ : ι → κ → GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hEq : ∀ i j v, P i j v →
      AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v (δ i j)) =
        (Subgroup.centralizer ({γ i j v} : Set (GL (Fin 2) (v.adicCompletion K)))).map
          (AutomorphicForm.toTensorGL K L (v.adicCompletion K)))
    (τ : ∀ i j v, Measure (Subgroup.centralizer ({γ i j v} : Set (GL (Fin 2) (v.adicCompletion K))))) :
    ∃ τ' : ∀ i j v, Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
        (AutomorphicForm.tensorPlace K L v (δ i j))),
      (∀ i j v (h : P i j v), τ' i j v = Measure.map (ceqv K L (γ i j v) _ (hEq i j v h)) (τ i j v)) ∧
      (∀ i j v, ¬ P i j v → (τ' i j v).IsHaarMeasure ∧
        τ' i j v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1) := by
  classical
  refine ⟨fun i j v => if h : P i j v then Measure.map (ceqv K L (γ i j v) _ (hEq i j v h)) (τ i j v)
      else (AutomorphicForm.exists_isHaarMeasure_twistedCentralizer_tensorPlace_preimage_semiLocalIntegralSet_eq_one
        K L σ (δ i j)).choose v,
    fun i j v h => dif_pos h, fun i j v h => ?_⟩
  simp only [dif_neg h]
  exact ⟨(AutomorphicForm.exists_isHaarMeasure_twistedCentralizer_tensorPlace_preimage_semiLocalIntegralSet_eq_one
      K L σ (δ i j)).choose_spec.1 v,
    (AutomorphicForm.exists_isHaarMeasure_twistedCentralizer_tensorPlace_preimage_semiLocalIntegralSet_eq_one
      K L σ (δ i j)).choose_spec.2 v⟩

end Families

section FamiliesNF

open scoped TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
  (D : Kˣ → (AdeleRing (𝓞 K) K)ˣ → (L ⊗[K] AdeleRing (𝓞 K) K)ˣ × (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)

theorem exists_tauG
    (hEq : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 →
      (∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀) →
        AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (diagUnits2 (D u z).1 (D u z).2) =
          (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))).map
            (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K)))
    (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))) :
    ∃ τG' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
        Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (diagUnits2 (D u z).1 (D u z).2)),
      ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ)
        (h : (u : K) ≠ 1 ∧ ∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀),
        τG' u z = Measure.map (ceqv K L (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) (diagUnits2 (D u z).1 (D u z).2) (hEq u z h.1 h.2)) (τG u z) := by
  obtain ⟨τ', h, -⟩ := exists_transportFamily K L σ (AdeleRing (𝓞 K) K)
    (fun (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) =>
      (u : K) ≠ 1 ∧ ∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀)
    (fun (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) => (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))
    (fun (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) => (diagUnits2 (D u z).1 (D u z).2))
    (fun u z h => hEq u z h.1 h.2) τG
  exact ⟨τ', h⟩

theorem exists_tauA
    (hEq : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 →
      (∃ δ₀, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ₀) →
        AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L (diagUnits2 (D u z).1 (D u z).2)) =
          (Subgroup.centralizer ({(AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))} : Set (GL (Fin 2) (InfiniteAdeleRing K)))).map
            (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)))
    (τA : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      @Measure (Subgroup.centralizer ({(AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) :
    ∃ τA' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
        Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L (diagUnits2 (D u z).1 (D u z).2))),
      (∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ)
        (h : (u : K) ≠ 1 ∧ ∃ δ₀, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ₀),
        τA' u z = Measure.map (ceqv K L (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (AutomorphicForm.tensorArch K L (diagUnits2 (D u z).1 (D u z).2)) (hEq u z h.1 h.2)) (τA u z)) ∧
      (∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
        ¬ ((u : K) ≠ 1 ∧ ∃ δ₀, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ₀) →
        (τA' u z).IsHaarMeasure) :=
  exists_transportFamily K L σ (InfiniteAdeleRing K)
    (fun (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) =>
      (u : K) ≠ 1 ∧ ∃ δ₀, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ₀)
    (fun (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) => (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
    (fun (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) => AutomorphicForm.tensorArch K L (diagUnits2 (D u z).1 (D u z).2))
    (fun u z h => hEq u z h.1 h.2) τA

theorem exists_tauF
    (hEq : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)), (u : K) ≠ 1 →
      (∃ δ₀, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ₀) →
        AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v (diagUnits2 (D u z).1 (D u z).2)) =
          (Subgroup.centralizer ({(AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))} : Set (GL (Fin 2) (v.adicCompletion K)))).map
            (AutomorphicForm.toTensorGL K L (v.adicCompletion K)))
    (τF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (AutomorphicForm.localCentralizerBorel K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))) :
    ∃ τF' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
        Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v (diagUnits2 (D u z).1 (D u z).2))),
      (∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K))
        (h : (u : K) ≠ 1 ∧ ∃ δ₀, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ₀),
        τF' u z v = Measure.map (ceqv K L (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (AutomorphicForm.tensorPlace K L v (diagUnits2 (D u z).1 (D u z).2)) (hEq u z v h.1 h.2)) (τF u z v)) ∧
      (∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
        ¬ ((u : K) ≠ 1 ∧ ∃ δ₀, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ₀) →
        (τF' u z v).IsHaarMeasure ∧ τF' u z v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1) :=
  exists_localFamily K L σ
    (fun (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) =>
      (u : K) ≠ 1 ∧ ∃ δ₀, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ₀)
    (fun (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) => (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (fun (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) => (diagUnits2 (D u z).1 (D u z).2))
    (fun u z v h => hEq u z v h.1 h.2) τF

end FamiliesNF

end K58TFL

end

open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hσ : σ ^ Module.finrank K L = 1)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (cτK : ℝ) (hcτK : 0 < cτK)
    (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))) (τA : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))) (cT : ℝ)
    (hτG : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τG u z).IsHaarMeasure)
    (hτGc : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG u z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (hτA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA u z))
    (hτF : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF u z v))
    (hτF1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF u z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (hcT : 0 < cT)
    (hT : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA u z) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF u z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG u z) = cT * (∫ t, Wa t ∂(τA u z)) * ∏ v ∈ S, ∫ t, WS v t ∂(τF u z v)) :
    ∃ (δ : Kˣ → (AdeleRing (𝓞 K) K)ˣ → GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
      (τG' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (δ u z)) (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ (δ u z)))
      (τA' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L (δ u z))) (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L (δ u z))))
      (τF' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)), @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v (δ u z))) (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v (δ u z)))),

      (∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀) →
        AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ (δ u z) =
          AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) ∧
      (∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ₀) →
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L (δ u z)) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) ∧
      (∀ u z v, ((u : Kˣ) : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ₀) →
        AutomorphicForm.normString K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v (δ u z)) =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K)
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) ∧

      (∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀) → @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ (δ u z)) (τG' u z)) ∧
      (∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀) → ∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ,
        ∫ s : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (δ u z), g (s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∂(τG' u z) =
          cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
            g (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2)) ∂(νZK.prod νZK)) ∧
      (∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀) →
        AutomorphicForm.Coupled K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) (δ u z) 1 (τG u z) (τG' u z)) ∧

      (∀ u z, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L (δ u z))) (τA' u z)) ∧
      (∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ₀) →
        AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))
          (AutomorphicForm.tensorArch K L (δ u z)) 1 (τA u z) (τA' u z)) ∧

      (∀ u z v, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v (δ u z))) (τF' u z v)) ∧
      (∀ u z v, ((u : Kˣ) : K) ≠ 1 →
        τF' u z v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1) ∧
      (∀ u z v, ((u : Kˣ) : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ₀) →
        AutomorphicForm.Coupled K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
          (AutomorphicForm.tensorPlace K L v (δ u z)) 1 (τF u z v) (τF' u z v)) ∧

      (∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀) → ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L (δ u z))] (fun t => Wa t) (τA' u z) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (δ u z))] (fun t => WS v t) (τF' u z v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (δ u z),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (δ u z),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂(τG' u z) = cT * (∫ t, Wa t ∂(τA' u z)) * ∏ v ∈ S, ∫ t, WS v t ∂(τF' u z v)) := by

  classical

  choose D hD using K58TFL.exists_lift_full K L σ hgen

  obtain ⟨τG', hτG'⟩ := K58TFL.exists_tauG K L σ D (fun u z => (hD u z).2.2.2.1) τG
  obtain ⟨τA', hτA', hτA'n⟩ := K58TFL.exists_tauA K L σ D (fun u z => (hD u z).2.2.2.2.1) τA
  obtain ⟨τF', hτF', hτF'n⟩ := K58TFL.exists_tauF K L σ D (fun u z => (hD u z).2.2.2.2.2) τF

  refine ⟨fun u z => (diagUnits2 (D u z).1 (D u z).2), τG', τA', τF', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro u z hu hg
    exact (hD u z).2.2.1 hu hg

  · intro u z hu hg
    exact (hD u z).1 hu hg

  · intro u z v hu hg
    exact (hD u z).2.1 v hu hg

  · intro u z hu hg
    haveI := hτG u z hu
    exact K58TFL.isHaarMeasure_of_eq_map K L _ _ _ (τG u z) _ (hτG' u z ⟨hu, hg⟩)

  · intro u z hu hg g
    rw [K58TFL.integral_of_eq_map K L _ _ _ (τG u z) _ (hτG' u z ⟨hu, hg⟩)]
    exact hτGc u z hu (fun x => g (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) x))

  · intro u z hu hg
    exact K58TFL.coupled_of_eq_map K L _ _ _ (τG u z) _ (hτG' u z ⟨hu, hg⟩)

  · intro u z hu
    by_cases hg : ∃ δ₀, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ₀
    · haveI := hτA u z hu
      exact K58TFL.isHaarMeasure_of_eq_map K L _ _ _ (τA u z) _ (hτA' u z ⟨hu, hg⟩)
    · exact hτA'n u z (fun h => hg h.2)

  · intro u z hu hg
    exact K58TFL.coupled_of_eq_map K L _ _ _ (τA u z) _ (hτA' u z ⟨hu, hg⟩)

  · intro u z v hu
    by_cases hg : ∃ δ₀, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ₀
    · haveI := hτF u z v hu
      exact K58TFL.isHaarMeasure_of_eq_map K L _ _ _ (τF u z v) _ (hτF' u z v ⟨hu, hg⟩)
    · exact (hτF'n u z v (fun h => hg h.2)).1

  · intro u z v hu
    by_cases hg : ∃ δ₀, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ₀
    · rw [K58TFL.apply_preimage_of_eq_map K L _ _ _ (τF u z v) _ (hτF' u z v ⟨hu, hg⟩) (AutomorphicForm.localIntegralSet K v)
        (AutomorphicForm.semiLocalIntegralSet K L v) (AutomorphicForm.isOpen_semiLocalIntegralSet K L v)
        (fun t => AutomorphicForm.toTensorGL_mem_semiLocalIntegralSet_iff_mem_localIntegralSet K L v t)]
      exact hτF1 u z v hu
    · exact (hτF'n u z v (fun h => hg h.2)).2

  · intro u z v hu hg
    exact K58TFL.coupled_of_eq_map K L _ _ _ (τF u z v) _ (hτF' u z v ⟨hu, hg⟩)

  · intro u z hu hg S W Wa WS hWa hWS hfac hvan
    exact K58TFL.restrictedProduct_transport K L σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) (diagUnits2 (D u z).1 (D u z).2) ((hD u z).2.2.2.1 hu hg)
      ((hD u z).2.2.2.2.1 hu (K58TFL.archGuard_of_global K L σ u z hg)) (τG u z) (τA u z) (τF u z)
      (τG' u z) (τA' u z) (τF' u z) (hτG' u z ⟨hu, hg⟩) (hτA' u z ⟨hu, K58TFL.archGuard_of_global K L σ u z hg⟩)
      cT (hT u z hu) S
      (fun v _ => ⟨(hD u z).2.2.2.2.2 v hu (K58TFL.localGuard_of_global K L σ u z v hg),
        hτF' u z v ⟨hu, K58TFL.localGuard_of_global K L σ u z v hg⟩⟩)
      W Wa WS hWa hWS hfac hvan

end S_AutomorphicForm_exists_twistedTorusFamily_lift_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct
end P2MW
export P2MW.S_AutomorphicForm_exists_twistedTorusFamily_lift_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct (solution)
