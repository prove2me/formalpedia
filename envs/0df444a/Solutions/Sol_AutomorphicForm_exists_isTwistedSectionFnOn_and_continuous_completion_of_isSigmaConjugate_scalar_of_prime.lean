-- Prove2me | solution 1 for AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/1cec85b0-51dc-5ab1-9e11-166b2ab17ff5

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_TwistedNormClasses
import Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_of_normString_eq_toTensorGL_scalar_of_algHom
import Theorems.Thm_NumberField_InfinitePlace_nonempty_algHom_completion_of_isUnramified
import Theorems.Thm_AutomorphicForm_exists_ringEquiv_tensor_completion_complex_of_isRamified
import Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_conjAe_toTensorGL_scalar_and_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime
p2m_attr_erase "simp" "AutomorphicForm.SplitPlace.string_castSucc AutomorphicForm.SplitPlace.reindex_symm_apply AutomorphicForm.SplitPlace.psiLeft_apply AutomorphicForm.SplitPlace.psiHomeomorph_apply AutomorphicForm.SplitPlace.psiLinearEquiv_apply AutomorphicForm.SplitPlace.psiEquiv_apply AutomorphicForm.SplitPlace.psi_tmul AutomorphicForm.SplitPlace.psiLinear_apply AutomorphicForm.SplitPlace.coords_apply_val AutomorphicForm.SplitPlace.string_last AutomorphicForm.SplitPlace.psiGL_apply_val AutomorphicForm.SplitPlace.dedekindMatrix_apply AutomorphicForm.SplitPlace.reindex_apply"

set_option autoImplicit false

open MeasureTheory AutomorphicForm Topology
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace P2mTsCent

section General

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  {A : Type} [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
  (σ : L ≃ₐ[K] L)

local notation "G" => GL (Fin 2) (L ⊗[K] A)

scoped instance instTopRing : IsTopologicalRing (L ⊗[K] A) := isTopologicalRing_tensor K L A
scoped instance instTopGroup : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] A)) := isTopologicalGroup_tensorGL K L A

omit [TopologicalSpace A] [IsTopologicalRing A] in
theorem isTwistedSectionFnOn_of_ne_zero_imp [TopologicalSpace A] (δ : G)
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (φ ψ : G → ℂ) (hφψ : ∀ y, φ y ≠ 0 → ψ y ≠ 0) (w : G → ℝ)
    (hw : IsTwistedSectionFnOn K L A σ δ τ' ψ w) : IsTwistedSectionFnOn K L A σ δ τ' φ w :=
  ⟨hw.1, hw.2.1, hw.2.2.1, fun x hx => hw.2.2.2 x (hφψ _ hx)⟩

theorem exists_continuous_bump [T2Space A] [LocallyCompactSpace A] (φ : G → ℂ) (hφ : HasCompactSupport φ) :
    ∃ ψ : G → ℂ, Continuous ψ ∧ HasCompactSupport ψ ∧ ∀ y, φ y ≠ 0 → ψ y ≠ 0 := by
  haveI : T2Space (GL (Fin 2) (L ⊗[K] A)) := t2Space_tensorGL K L A
  haveI : LocallyCompactSpace (GL (Fin 2) (L ⊗[K] A)) := locallyCompactSpace_tensorGL K L A
  obtain ⟨f, hf1, -, hfc, -⟩ :=
    exists_continuous_one_zero_of_isCompact hφ.isCompact isClosed_empty (Set.disjoint_empty _)
  refine ⟨fun y => ((f y : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous, ?_, fun y hy => ?_⟩
  · exact hfc.comp_left Complex.ofReal_zero
  · have : f y = 1 := hf1 (subset_tsupport _ hy)
    simp [this]

omit [TopologicalSpace A] [IsTopologicalRing A] in
theorem mem_twistedCentralizer_conj {δ y t : G} (ht : t ∈ twistedCentralizer K L A σ δ) :
    y⁻¹ * t * y ∈ twistedCentralizer K L A σ (y⁻¹ * δ * sigmaGL K L A σ y) := by
  rw [mem_sigmaCentralizer_iff] at ht ⊢
  rw [map_mul, map_mul, map_inv]
  calc y⁻¹ * t * y * (y⁻¹ * δ * sigmaGL K L A σ y) * ((sigmaGL K L A σ y)⁻¹ * sigmaGL K L A σ t * sigmaGL K L A σ y)⁻¹
      = y⁻¹ * (t * δ * (sigmaGL K L A σ t)⁻¹) * sigmaGL K L A σ y := by group
    _ = y⁻¹ * δ * sigmaGL K L A σ y := by rw [ht]

omit [TopologicalSpace A] [IsTopologicalRing A] in
theorem mem_twistedCentralizer_conj_iff (δ y t : G) :
    t ∈ twistedCentralizer K L A σ δ ↔
      y⁻¹ * t * y ∈ twistedCentralizer K L A σ (y⁻¹ * δ * sigmaGL K L A σ y) := by
  refine ⟨mem_twistedCentralizer_conj σ, fun h => ?_⟩
  have h' := mem_twistedCentralizer_conj σ (y := y⁻¹) h
  have e1 : y⁻¹⁻¹ * (y⁻¹ * t * y) * y⁻¹ = t := by group
  have e2 : y⁻¹⁻¹ * (y⁻¹ * δ * sigmaGL K L A σ y) * sigmaGL K L A σ y⁻¹ = δ := by
    rw [map_inv]; group
  rwa [e1, e2] at h'

theorem exists_transport_conj [T2Space A] [LocallyCompactSpace A] (δ y : G)
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ') :
    ∃ τ'' : @Measure (twistedCentralizer K L A σ (y⁻¹ * δ * sigmaGL K L A σ y))
        (twistedCentralizerBorel K L A σ (y⁻¹ * δ * sigmaGL K L A σ y)),
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ (y⁻¹ * δ * sigmaGL K L A σ y)) τ'' ∧
      ∀ (φ : G → ℂ) (w : G → ℝ),
        IsTwistedSectionFnOn K L A σ (y⁻¹ * δ * sigmaGL K L A σ y) τ'' φ w →
        IsTwistedSectionFnOn K L A σ δ τ' φ (fun x => w (y⁻¹ * x)) ∧
          (Continuous w → Continuous (fun x => w (y⁻¹ * x))) := by
  set δ' : G := y⁻¹ * δ * sigmaGL K L A σ y with hδ'
  letI : MeasurableSpace (twistedCentralizer K L A σ δ) := twistedCentralizerBorel K L A σ δ
  letI : MeasurableSpace (twistedCentralizer K L A σ δ') := twistedCentralizerBorel K L A σ δ'
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K L A σ δ') := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf _
  haveI : Measure.IsHaarMeasure τ' := hτ'

  let cFun : twistedCentralizer K L A σ δ → twistedCentralizer K L A σ δ' :=
    fun t => ⟨y⁻¹ * t * y, mem_twistedCentralizer_conj σ t.2⟩
  let cInv : twistedCentralizer K L A σ δ' → twistedCentralizer K L A σ δ :=
    fun s => ⟨y * s * y⁻¹, by
      have h := s.2
      rw [(mem_twistedCentralizer_conj_iff σ δ y (y * (s : G) * y⁻¹))]
      have : y⁻¹ * (y * (s : G) * y⁻¹) * y = s := by group
      rw [this]; exact h⟩
  let c : twistedCentralizer K L A σ δ ≃ₜ* twistedCentralizer K L A σ δ' :=
    { toFun := cFun
      invFun := cInv
      left_inv := fun t => Subtype.ext (by show y * (y⁻¹ * (t : G) * y) * y⁻¹ = t; group)
      right_inv := fun s => Subtype.ext (by show y⁻¹ * (y * (s : G) * y⁻¹) * y = s; group)
      map_mul' := fun s t => Subtype.ext (by
        show y⁻¹ * ((s : G) * t) * y = (y⁻¹ * s * y) * (y⁻¹ * t * y); group)
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact (continuous_const.mul continuous_subtype_val).mul continuous_const
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ _
        exact (continuous_const.mul continuous_subtype_val).mul continuous_const }
  have hc_meas : Measurable c := c.continuous.measurable
  refine ⟨Measure.map c τ', ContinuousMulEquiv.isHaarMeasure_map τ' c, fun φ w hw => ⟨?_, fun hwc => ?_⟩⟩
  · refine ⟨fun x => hw.1 _, hw.2.1.comp (measurable_const_mul _), ?_, fun x hx => ?_⟩
    · exact hw.2.2.1.comp_homeomorph (Homeomorph.mulLeft y⁻¹)
    · have hx' : φ ((y⁻¹ * x)⁻¹ * δ' * sigmaGL K L A σ (y⁻¹ * x)) ≠ 0 := by
        have : (y⁻¹ * x)⁻¹ * δ' * sigmaGL K L A σ (y⁻¹ * x) = x⁻¹ * δ * sigmaGL K L A σ x := by
          rw [hδ', map_mul, map_inv]; group
        rwa [this]
      have key := hw.2.2.2 (y⁻¹ * x) hx'
      rw [MeasureTheory.integral_map hc_meas.aemeasurable] at key
      · convert key using 2
        funext t
        show w (y⁻¹ * ((t : G) * x)) = w (y⁻¹ * (t : G) * y * (y⁻¹ * x))
        congr 1; group
      · exact (hw.2.1.comp ((continuous_subtype_val.mul continuous_const).measurable)).aestronglyMeasurable
  · exact hwc.comp (continuous_const.mul continuous_id)

end General

section Iso

variable {K L A : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)
  {K' L' A' : Type} [Field K'] [Field L'] [Algebra K' L'] [FiniteDimensional K' L']
  [CommRing A'] [Algebra K' A'] [TopologicalSpace A'] [IsTopologicalRing A'] (σ' : L' ≃ₐ[K'] L')
  (E : L ⊗[K] A ≃+* L' ⊗[K'] A') (hE : Continuous E) (hE' : Continuous E.symm)
  (hEσ : ∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K' L' A' σ' (E z))

abbrev Ehat (E : L ⊗[K] A ≃+* L' ⊗[K'] A') : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L' ⊗[K'] A') :=
  Matrix.GeneralLinearGroup.map E.toRingHom

abbrev EhatInv (E : L ⊗[K] A ≃+* L' ⊗[K'] A') : GL (Fin 2) (L' ⊗[K'] A') →* GL (Fin 2) (L ⊗[K] A) :=
  Matrix.GeneralLinearGroup.map E.symm.toRingHom

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] [FiniteDimensional K' L']
  [TopologicalSpace A'] [IsTopologicalRing A'] in
theorem EhatInv_Ehat (x : GL (Fin 2) (L ⊗[K] A)) : EhatInv E (Ehat E x) = x := by
  apply Units.ext; ext i j
  show E.symm (E ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j)) = _
  exact E.symm_apply_apply _

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] [FiniteDimensional K' L']
  [TopologicalSpace A'] [IsTopologicalRing A'] in
theorem Ehat_EhatInv (x : GL (Fin 2) (L' ⊗[K'] A')) : Ehat E (EhatInv E x) = x := by
  apply Units.ext; ext i j
  show E (E.symm ((x : Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A')) i j)) = _
  exact E.apply_symm_apply _

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] [FiniteDimensional K' L']
  [TopologicalSpace A'] [IsTopologicalRing A'] in
include hEσ in
theorem Ehat_sigmaGL (x : GL (Fin 2) (L ⊗[K] A)) :
    Ehat E (sigmaGL K L A σ x) = sigmaGL K' L' A' σ' (Ehat E x) := by
  apply Units.ext; ext i j
  exact hEσ _

include hE in
theorem continuous_Ehat : Continuous (Ehat E : GL (Fin 2) (L ⊗[K] A) → GL (Fin 2) (L' ⊗[K'] A')) := by
  refine Continuous.units_map _ ?_
  change Continuous fun M : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) => M.map E
  exact continuous_id.matrix_map hE

include hE' in
theorem continuous_EhatInv : Continuous (EhatInv E : GL (Fin 2) (L' ⊗[K'] A') → GL (Fin 2) (L ⊗[K] A)) := by
  refine Continuous.units_map _ ?_
  change Continuous fun M : Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A') => M.map E.symm
  exact continuous_id.matrix_map hE'

def EhatHomeo (hE : Continuous E) (hE' : Continuous E.symm) :
    GL (Fin 2) (L ⊗[K] A) ≃ₜ GL (Fin 2) (L' ⊗[K'] A') where
  toFun := Ehat E
  invFun := EhatInv E
  left_inv := EhatInv_Ehat E
  right_inv := Ehat_EhatInv E
  continuous_toFun := continuous_Ehat E hE
  continuous_invFun := continuous_EhatInv E hE'

include hE hE' hEσ in

theorem exists_transport_iso (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ') :
    ∃ τ'' : @Measure (twistedCentralizer K' L' A' σ' (Ehat E δ)) (twistedCentralizerBorel K' L' A' σ' (Ehat E δ)),
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K' L' A' σ' (Ehat E δ)) τ'' ∧
      ∀ (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (w : GL (Fin 2) (L' ⊗[K'] A') → ℝ),
        IsTwistedSectionFnOn K' L' A' σ' (Ehat E δ) τ'' (φ ∘ EhatInv E) w →
        IsTwistedSectionFnOn K L A σ δ τ' φ (w ∘ Ehat E) ∧
          (Continuous w → Continuous (w ∘ Ehat E)) := by
  haveI : IsTopologicalRing (L ⊗[K] A) := isTopologicalRing_tensor K L A
  haveI : IsTopologicalRing (L' ⊗[K'] A') := isTopologicalRing_tensor K' L' A'
  haveI : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] A)) := isTopologicalGroup_tensorGL K L A
  haveI : IsTopologicalGroup (GL (Fin 2) (L' ⊗[K'] A')) := isTopologicalGroup_tensorGL K' L' A'
  set δ' := Ehat E δ with hδ'
  letI : MeasurableSpace (twistedCentralizer K L A σ δ) := twistedCentralizerBorel K L A σ δ
  letI : MeasurableSpace (twistedCentralizer K' L' A' σ' δ') := twistedCentralizerBorel K' L' A' σ' δ'
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  haveI : BorelSpace (twistedCentralizer K' L' A' σ' δ') := ⟨rfl⟩
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf _
  letI : MeasurableSpace (GL (Fin 2) (L' ⊗[K'] A')) := glBorelOf (L' ⊗[K'] A')
  haveI : BorelSpace (GL (Fin 2) (L' ⊗[K'] A')) := borelSpace_glBorelOf _
  haveI : Measure.IsHaarMeasure τ' := hτ'
  have hmem : ∀ t : GL (Fin 2) (L ⊗[K] A), t ∈ twistedCentralizer K L A σ δ →
      Ehat E t ∈ twistedCentralizer K' L' A' σ' δ' := by
    intro t ht
    rw [mem_sigmaCentralizer_iff] at ht ⊢
    rw [hδ', ← Ehat_sigmaGL σ σ' E hEσ, ← map_inv, ← map_mul, ← map_mul, ht]
  have hmem' : ∀ s : GL (Fin 2) (L' ⊗[K'] A'), s ∈ twistedCentralizer K' L' A' σ' δ' →
      EhatInv E s ∈ twistedCentralizer K L A σ δ := by
    intro s hs
    rw [mem_sigmaCentralizer_iff] at hs ⊢
    have h1 : Ehat E (EhatInv E s * δ * (sigmaGL K L A σ (EhatInv E s))⁻¹) = δ' := by
      rw [map_mul, map_mul, map_inv, Ehat_sigmaGL σ σ' E hEσ, Ehat_EhatInv, ← hδ', hs]
    have h2 := congrArg (EhatInv E) h1
    rwa [EhatInv_Ehat, hδ', EhatInv_Ehat] at h2
  let c : twistedCentralizer K L A σ δ ≃ₜ* twistedCentralizer K' L' A' σ' δ' :=
    { toFun := fun t => ⟨Ehat E t, hmem t t.2⟩
      invFun := fun s => ⟨EhatInv E s, hmem' s s.2⟩
      left_inv := fun t => Subtype.ext (EhatInv_Ehat E t)
      right_inv := fun s => Subtype.ext (Ehat_EhatInv E s)
      map_mul' := fun s t => Subtype.ext
        (map_mul (Ehat E) (s : GL (Fin 2) (L ⊗[K] A)) (t : GL (Fin 2) (L ⊗[K] A)))
      continuous_toFun := Continuous.subtype_mk ((continuous_Ehat E hE).comp continuous_subtype_val) _
      continuous_invFun := Continuous.subtype_mk ((continuous_EhatInv E hE').comp continuous_subtype_val) _ }
  have hc_meas : Measurable c := c.continuous.measurable
  refine ⟨Measure.map c τ', ContinuousMulEquiv.isHaarMeasure_map τ' c, fun φ w hw => ⟨?_, fun hwc => ?_⟩⟩
  · refine ⟨fun x => hw.1 _, hw.2.1.comp (continuous_Ehat E hE).measurable, ?_, fun x hx => ?_⟩
    · exact hw.2.2.1.comp_homeomorph (EhatHomeo E hE hE')
    · have hx' : (φ ∘ EhatInv E) ((Ehat E x)⁻¹ * δ' * sigmaGL K' L' A' σ' (Ehat E x)) ≠ 0 := by
        have : (Ehat E x)⁻¹ * δ' * sigmaGL K' L' A' σ' (Ehat E x) = Ehat E (x⁻¹ * δ * sigmaGL K L A σ x) := by
          rw [map_mul, map_mul, map_inv, Ehat_sigmaGL σ σ' E hEσ]
        rw [this, Function.comp_apply, EhatInv_Ehat]
        exact hx
      have key := hw.2.2.2 (Ehat E x) hx'
      rw [MeasureTheory.integral_map hc_meas.aemeasurable] at key
      · convert key using 2
        funext t
        show w (Ehat E ((t : GL (Fin 2) (L ⊗[K] A)) * x)) = w (Ehat E t * Ehat E x)
        rw [map_mul]
      · exact (hw.2.1.comp ((continuous_subtype_val.mul continuous_const).measurable)).aestronglyMeasurable
  · exact hwc.comp (continuous_Ehat E hE)

end Iso

section NormString

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  {A : Type} [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

omit [FiniteDimensional K L] in
theorem sigmaTensor_tmul' (l : L) (a : A) : sigmaTensor K L A σ (l ⊗ₜ a) = σ l ⊗ₜ a := by
  simp [sigmaTensor]

omit [FiniteDimensional K L] in

theorem exists_eq_tmul_of_fixed (hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L))
    (u : L ⊗[K] A) (hu : sigmaTensor K L A σ u = u) : ∃ a : A, u = (1 : L) ⊗ₜ[K] a := by
  have hex : Function.Exact (Algebra.linearMap K L) (σ.toLinearMap - LinearMap.id : L →ₗ[K] L) := by
    intro l
    constructor
    · intro hl
      have : σ l - l = 0 := hl
      exact hfix l (sub_eq_zero.1 this)
    · rintro ⟨k, rfl⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, Algebra.linearMap_apply,
        AlgEquiv.toLinearMap_apply, AlgEquiv.commutes, sub_self]
  have hexA := Module.Flat.rTensor_exact A hex
  have hrT : ∀ w : L ⊗[K] A, ((σ.toLinearMap - LinearMap.id).rTensor A) w = sigmaTensor K L A σ w - w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
        rw [LinearMap.rTensor_tmul, LinearMap.sub_apply, LinearMap.id_apply, TensorProduct.sub_tmul,
          sigmaTensor_tmul']
        rfl
    | add x y hx hy => rw [map_add, hx, hy, map_add]; abel
  have hu0 : ((σ.toLinearMap - LinearMap.id).rTensor A) u = 0 := by rw [hrT, hu, sub_self]
  obtain ⟨w, hw⟩ := (hexA u).1 hu0
  rw [← hw]
  clear hw hu0 hu
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul k a =>
      refine ⟨k • a, ?_⟩
      rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, TensorProduct.tmul_add]⟩

omit [FiniteDimensional K L] in
private theorem _root_.P2mTsCent.includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

p2m_export "P2mTsCent" "includeRight_injective"

theorem iterate_sigmaTensor_finrank [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (x : L ⊗[K] A) : (⇑(sigmaTensor K L A σ))^[Module.finrank K L] x = x := by
  rw [← RingHom.coe_pow]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l a =>
      have : ∀ n : ℕ, ((sigmaTensor K L A σ) ^ n) (l ⊗ₜ a) = ((⇑σ)^[n] l) ⊗ₜ a := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            rw [pow_succ', RingHom.coe_mul, Function.comp_apply, ih, sigmaTensor_tmul',
              Function.iterate_succ_apply']
      rw [this, LT.TwistedNorm.iterate_finrank_apply_of_generator hgen]
  | add x y hx hy => rw [map_add, hx, hy]

theorem iterate_sigmaGL_finrank [IsGalois K L] (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (g : GL (Fin 2) (L ⊗[K] A)) : (⇑(sigmaGL K L A σ))^[Module.finrank K L] g = g := by
  apply Units.ext; ext i j
  rw [show sigmaGL K L A σ = Matrix.GeneralLinearGroup.map (sigmaTensor K L A σ) from rfl,
    LT.TwistedNorm.iterate_generalLinearGroup_map_apply]
  exact iterate_sigmaTensor_finrank σ hgen _

omit [FiniteDimensional K L] in
theorem normString_eq_sigmaNormPow (δ : GL (Fin 2) (L ⊗[K] A)) :
    normString K L A σ δ = LT.TwistedNorm.sigmaNormPow (sigmaGL K L A σ) (Module.finrank K L) δ := by
  rw [LT.TwistedNorm.sigmaNormPow_def, LT.TwistedNorm.sigmaPartialNorm_eq_prod_map_range]
  rfl

omit [FiniteDimensional K L] in
theorem sigmaGL_scalar (u : (L ⊗[K] A)ˣ) :
    sigmaGL K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (sigmaTensor K L A σ).toMonoidHom u) := by
  apply Units.ext; ext i j
  show sigmaTensor K L A σ ((Matrix.scalar (Fin 2) (u : L ⊗[K] A)) i j) = (Matrix.scalar (Fin 2) _) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero _

omit [FiniteDimensional K L] in
theorem scalar_mul_comm' (c : (L ⊗[K] A)ˣ) (g : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : L ⊗[K] A) * (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
    (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * Matrix.scalar (Fin 2) (c : L ⊗[K] A)
  exact (Matrix.scalar_commute (c : L ⊗[K] A) (fun r => Commute.all _ r) _).eq

omit [FiniteDimensional K L] in
theorem scalar_includeRight (z : Aˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom.toMonoidHom z) =
      toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
  apply Units.ext; ext i j
  show (Matrix.scalar (Fin 2) _) i j =
    (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) ((Matrix.scalar (Fin 2) (z : A)) i j)
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact (map_zero _).symm

theorem exists_normString_eq_toTensorGL_scalar [IsGalois K L]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : ∃ d : (L ⊗[K] A)ˣ, IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) :
    ∃ z : Aˣ, normString K L A σ δ = toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by
  obtain ⟨d, y, hy⟩ := hδ
  set n := Module.finrank K L with hn
  set σG := sigmaGL K L A σ with hσG
  set σU : (L ⊗[K] A)ˣ →* (L ⊗[K] A)ˣ := Units.map (sigmaTensor K L A σ).toMonoidHom with hσU

  have hfixG : ∀ g : GL (Fin 2) (L ⊗[K] A), (⇑σG)^[n] g = g := iterate_sigmaGL_finrank σ hgen
  have h1 : LT.TwistedNorm.sigmaNormPow σG n (Matrix.GeneralLinearGroup.scalar (Fin 2) d) =
      y⁻¹ * LT.TwistedNorm.sigmaNormPow σG n δ * y := by
    rw [hy, LT.TwistedNorm.sigmaNormPow_sigmaConjElt σG n (hfixG y)]
  have h2 : LT.TwistedNorm.sigmaNormPow σG n (Matrix.GeneralLinearGroup.scalar (Fin 2) d) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (LT.TwistedNorm.sigmaNormPow σU n d) := by
    have := LT.TwistedNorm.hom_sigmaNormPow σU σG (Matrix.GeneralLinearGroup.scalar (Fin 2))
      (fun x => (sigmaGL_scalar σ x).symm) n d
    exact this.symm
  set Nd := LT.TwistedNorm.sigmaNormPow σU n d with hNd

  have hfixU : ∀ u : (L ⊗[K] A)ˣ, (⇑σU)^[n] u = u := by
    intro u; apply Units.ext
    have : ∀ m : ℕ, (((⇑σU)^[m] u : (L ⊗[K] A)ˣ) : L ⊗[K] A) = (⇑(sigmaTensor K L A σ))^[m] (u : L ⊗[K] A) := by
      intro m; induction m with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]; rfl
    rw [this]; exact iterate_sigmaTensor_finrank σ hgen _
  have hNdfix : sigmaTensor K L A σ (Nd : L ⊗[K] A) = Nd := by
    have h := congrArg Units.val (LT.TwistedNorm.map_sigmaNormPow σU n (hfixU d))
    rw [Units.val_mul, Units.val_mul] at h
    have e : ((d⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * (Nd : L ⊗[K] A) * (d : L ⊗[K] A) = Nd := by
      rw [show ((d⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * (Nd : L ⊗[K] A) * (d : L ⊗[K] A) =
        (Nd : L ⊗[K] A) * (((d⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) * d) by ring, Units.inv_mul, mul_one]
    rw [← hNd, e] at h
    exact h
  have hσUNd : σU Nd = Nd := Units.ext hNdfix
  have hNdfix' : sigmaTensor K L A σ ((Nd⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) = (Nd⁻¹ : (L ⊗[K] A)ˣ) := by
    show ((σU Nd⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) = _
    rw [map_inv, hσUNd]
  have hfix : ∀ l : L, σ l = l → l ∈ Set.range (algebraMap K L) := fun l hl =>
    LT.TwistedNorm.mem_range_algebraMap_of_generator_apply_eq hgen hl
  obtain ⟨a, ha⟩ := exists_eq_tmul_of_fixed σ hfix _ hNdfix
  obtain ⟨b, hb⟩ := exists_eq_tmul_of_fixed σ hfix _ hNdfix'
  have hab : a * b = 1 := by
    apply includeRight_injective (K := K) (L := L) (A := A)
    rw [map_mul, map_one]
    show ((1 : L) ⊗ₜ[K] a) * ((1 : L) ⊗ₜ[K] b) = 1
    rw [← ha, ← hb, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  let z : Aˣ := ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
  refine ⟨z, ?_⟩
  have hNdz : Nd = Units.map (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom.toMonoidHom z :=
    Units.ext ha
  calc normString K L A σ δ = LT.TwistedNorm.sigmaNormPow σG n δ := normString_eq_sigmaNormPow σ δ
    _ = y * (y⁻¹ * LT.TwistedNorm.sigmaNormPow σG n δ * y) * y⁻¹ := by group
    _ = y * Matrix.GeneralLinearGroup.scalar (Fin 2) Nd * y⁻¹ := by rw [← h1, h2]
    _ = Matrix.GeneralLinearGroup.scalar (Fin 2) Nd := by rw [← scalar_mul_comm', mul_inv_cancel_right]
    _ = toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) z) := by rw [hNdz, scalar_includeRight]

end NormString

section Model

def eRing : (ℂ ⊗[ℝ] ℝ) ≃+* ℂ :=
  @AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)

theorem eRing_tmul (z : ℂ) (a : ℝ) : eRing (z ⊗ₜ[ℝ] a) = (a : ℂ) * z := by
  show (Algebra.TensorProduct.rid ℝ ℝ ℂ) (z ⊗ₜ[ℝ] a) = (a : ℂ) * z
  rw [Algebra.TensorProduct.rid_tmul, Complex.real_smul]

theorem eRing_sigmaTensor (x : ℂ ⊗[ℝ] ℝ) :
    eRing (sigmaTensor ℝ ℂ ℝ Complex.conjAe x) = (starRingEnd ℂ) (eRing x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z a =>
      rw [sigmaTensor_tmul', eRing_tmul, eRing_tmul, map_mul, Complex.conj_ofReal]
      rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add eRing x y, map_add]

theorem exists_conj_eq_mul_of_norm_eq_one (ω : ℂ) (hω : ‖ω‖ = 1) :
    ∃ c : ℂ, c ≠ 0 ∧ (starRingEnd ℂ) c = ω * c := by
  by_cases h : ω = -1
  · refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
    rw [h, Complex.conj_I, neg_one_mul]
  · refine ⟨1 + (starRingEnd ℂ) ω, ?_, ?_⟩
    · intro h0
      apply h
      have : (starRingEnd ℂ) ω = -1 := by linear_combination h0
      have := congrArg (starRingEnd ℂ) this
      rwa [Complex.conj_conj, map_neg, map_one] at this
    · have hωω : ω * (starRingEnd ℂ) ω = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hω]; norm_num
      rw [map_add, map_one, Complex.conj_conj, mul_add, mul_one, hωω, add_comm]

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map f.toMonoidHom u) := by
  apply Units.ext; ext i j
  show f ((Matrix.scalar (Fin 2) (u : R)) i j) = (Matrix.scalar (Fin 2) _) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero _

theorem exists_toTensorGL_real_scalar_eq (d' : (ℂ ⊗[ℝ] ℝ)ˣ) :
    ∃ (d₀ : ℝˣ) (c : (ℂ ⊗[ℝ] ℝ)ˣ),
      toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d₀) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) d' *
          sigmaGL ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  set u : ℂ := eRing (d' : ℂ ⊗[ℝ] ℝ) with hu
  have hu0 : u ≠ 0 := by
    rw [hu]
    exact (d'.isUnit.map eRing.toRingHom.toMonoidHom).ne_zero
  set r : ℝ := ‖u‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 hu0
  set ω : ℂ := (r : ℂ) / u with hω
  have hω1 : ‖ω‖ = 1 := by
    rw [hω, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, hr, div_self (norm_ne_zero_iff.2 hu0)]
  obtain ⟨cC, hc0, hc⟩ := exists_conj_eq_mul_of_norm_eq_one ω hω1

  have key : cC⁻¹ * u * (starRingEnd ℂ) cC = r := by
    rw [hc, hω]; field_simp
  let d₀ : ℝˣ := Units.mk0 r hr0.ne'
  let c : (ℂ ⊗[ℝ] ℝ)ˣ := Units.map eRing.symm.toRingHom.toMonoidHom (Units.mk0 cC hc0)
  refine ⟨d₀, c, ?_⟩
  rw [← scalar_includeRight, sigmaGL_scalar, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  apply eRing.injective
  rw [Units.val_mul, Units.val_mul, map_mul, map_mul]
  show eRing ((1 : ℂ) ⊗ₜ[ℝ] (r : ℝ)) =
    eRing (eRing.symm (cC⁻¹)) * u * eRing (sigmaTensor ℝ ℂ ℝ Complex.conjAe (eRing.symm cC))
  rw [eRing_tmul, mul_one, eRing_sigmaTensor, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, key]

end Model

section Assembly

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  {A : Type} [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
  (σ : L ≃ₐ[K] L)

theorem exists_transport_conj' [T2Space A] [LocallyCompactSpace A] (δ y δ' : GL (Fin 2) (L ⊗[K] A))
    (hδ' : δ' = y⁻¹ * δ * sigmaGL K L A σ y)
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ') :
    ∃ τ'' : @Measure (twistedCentralizer K L A σ δ') (twistedCentralizerBorel K L A σ δ'),
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ') τ'' ∧
      ∀ (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (w : GL (Fin 2) (L ⊗[K] A) → ℝ),
        IsTwistedSectionFnOn K L A σ δ' τ'' φ w →
        IsTwistedSectionFnOn K L A σ δ τ' φ (fun x => w (y⁻¹ * x)) ∧
          (Continuous w → Continuous (fun x => w (y⁻¹ * x))) := by
  subst hδ'
  exact exists_transport_conj σ δ y τ' hτ'

end Assembly

section Main

open NumberField

theorem sigma_ne_one {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) : σ ≠ 1 := by
  intro h
  have hcard : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have hsub : ∀ τ : L ≃ₐ[K] L, τ = 1 := fun τ => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgen τ)
    rw [← hk, h, one_zpow]
  have h1 : Nat.card (L ≃ₐ[K] L) = 1 :=
    Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (hsub a).trans (hsub b).symm⟩, ⟨1⟩⟩
  rw [h1] at hcard
  exact hprime.one_lt.ne hcard

set_option maxHeartbeats 32000000 in
theorem main
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (hprime : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : InfinitePlace K)
    (δ : GL (Fin 2) (L ⊗[K] v.Completion))
    (hδ : ∃ d : (L ⊗[K] v.Completion)ˣ,
      IsSigmaConjugate K L v.Completion σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))
    (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] v.Completion) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ W : GL (Fin 2) (L ⊗[K] v.Completion) → ℝ,
      IsTwistedSectionFnOn K L v.Completion σ δ τ' φ W ∧ Continuous W := by
  have hσ1 : σ ≠ 1 := sigma_ne_one hprime σ hgen

  obtain ⟨w, rfl⟩ := NumberField.InfinitePlace.comap_surjective (k := K) (K := L) v

  haveI hsc : SecondCountableTopology (w.comap (algebraMap K L)).Completion :=
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding
      (w.comap (algebraMap K L))).isEmbedding.secondCountableTopology

  obtain ⟨ψ, hψc, hψs, hφψ⟩ := exists_continuous_bump (K := K) (L := L) φ hφ
  suffices h : ∃ W : GL (Fin 2) (L ⊗[K] (w.comap (algebraMap K L)).Completion) → ℝ,
      IsTwistedSectionFnOn K L _ σ δ τ' ψ W ∧ Continuous W by
    obtain ⟨W, hW, hWc⟩ := h
    exact ⟨W, isTwistedSectionFnOn_of_ne_zero_imp σ δ τ' φ ψ hφψ W hW, hWc⟩
  by_cases hun : w.IsUnramified K
  ·
    obtain ⟨ι⟩ := NumberField.InfinitePlace.nonempty_algHom_completion_of_isUnramified K L
      (w.comap (algebraMap K L)) w rfl hun
    obtain ⟨z, hz⟩ := exists_normString_eq_toTensorGL_scalar σ hgen δ hδ
    exact AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_of_normString_eq_toTensorGL_scalar_of_algHom
      K L hprime σ hσ1 (w.comap (algebraMap K L)).Completion ι δ z hz ψ hψc hψs τ' hτ'
  ·
    have h2 : Module.finrank K L = 2 :=
      (Nat.Prime.even_iff hprime).1 (NumberField.InfinitePlace.even_finrank_of_not_isUnramified hun)
    obtain ⟨e, E, he, he', hE, hE', hEσ, hEι, hErid, heK⟩ :=
      AutomorphicForm.exists_ringEquiv_tensor_completion_complex_of_isRamified K L h2 σ hσ1 w hun

    obtain ⟨τ₂, hτ₂, htr₂⟩ := exists_transport_iso σ Complex.conjAe E hE hE' hEσ δ τ' hτ'

    obtain ⟨d, y, hy⟩ := hδ
    obtain ⟨d₀, c, hc⟩ := exists_toTensorGL_real_scalar_eq (Units.map E.toRingHom.toMonoidHom d)
    set y₁ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) := Ehat E y * Matrix.GeneralLinearGroup.scalar (Fin 2) c with hy₁
    have hconj : toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d₀) =
        y₁⁻¹ * Ehat E δ * sigmaGL ℝ ℂ ℝ Complex.conjAe y₁ := by
      have h1 : Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map E.toRingHom.toMonoidHom d) =
          (Ehat E y)⁻¹ * Ehat E δ * sigmaGL ℝ ℂ ℝ Complex.conjAe (Ehat E y) := by
        rw [← map_scalar, hy, map_mul, map_mul, map_inv, Ehat_sigmaGL σ Complex.conjAe E hEσ]
      rw [hc, h1, hy₁, map_mul, mul_inv_rev]
      group
    obtain ⟨τ₃, hτ₃, htr₃⟩ := exists_transport_conj' Complex.conjAe (Ehat E δ) y₁ _ hconj τ₂ hτ₂

    have hψ' : Continuous (ψ ∘ EhatInv E) := hψc.comp (continuous_EhatInv E hE')
    have hψ's : HasCompactSupport (ψ ∘ EhatInv E) := hψs.comp_homeomorph (EhatHomeo E hE hE').symm
    obtain ⟨w₀, hw₀, hw₀c⟩ :=
      AutomorphicForm.exists_isTwistedSectionFnOn_conjAe_toTensorGL_scalar_and_continuous d₀ (ψ ∘ EhatInv E)
        hψ' hψ's τ₃ hτ₃

    obtain ⟨hw₁, hw₁c⟩ := htr₃ (ψ ∘ EhatInv E) w₀ hw₀
    obtain ⟨hw₂, hw₂c⟩ := htr₂ ψ (fun x => w₀ (y₁⁻¹ * x)) hw₁
    exact ⟨_, hw₂, hw₂c (hw₁c hw₀c)⟩

end Main

end P2mTsCent
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime.P2mTsCent"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime.P2mTsCent"

open NumberField

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (hprime : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : InfinitePlace K)
    (δ : GL (Fin 2) (L ⊗[K] v.Completion))
    (hδ : ∃ d : (L ⊗[K] v.Completion)ˣ,
      IsSigmaConjugate K L v.Completion σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))
    (τ' : @Measure (twistedCentralizer K L v.Completion σ δ) (twistedCentralizerBorel K L v.Completion σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L v.Completion σ δ) τ')
    (hτ'i : @Measure.IsInvInvariant _ (twistedCentralizerBorel K L v.Completion σ δ) _ τ')
    (φ : GL (Fin 2) (L ⊗[K] v.Completion) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ W : GL (Fin 2) (L ⊗[K] v.Completion) → ℝ,
      IsTwistedSectionFnOn K L v.Completion σ δ τ' φ W ∧ Continuous W := by
  exact P2mTsCent.main K L hprime σ hgen v δ hδ τ' hτ' φ hφ

end S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime
end P2MW
export P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime (solution)
