-- Prove2me | solution 1 for AutomorphicForm.exists_isTwistedSectionFnOn_conjAe_toTensorGL_scalar_and_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/1ba9289b-c12d-5f22-b3be-6eb030552f46

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_isClosedEmbedding_toTensorGL_and_exists_nhds_one_twistedCentralizer_iff_and_forall_isCompact_conjAe
import Theorems.Thm_MeasureTheory_exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_conjAe_toTensorGL_scalar_and_continuous

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace P2mRamModel

open Topology

abbrev GLCR := GL (Fin 2) (ℂ ⊗[ℝ] ℝ)

scoped instance instTopRingCR : IsTopologicalRing (ℂ ⊗[ℝ] ℝ) := isTopologicalRing_tensor ℝ ℂ ℝ
scoped instance instT2CR : T2Space (ℂ ⊗[ℝ] ℝ) := t2Space_tensor ℝ ℂ ℝ
scoped instance instTopGroupGLCR : IsTopologicalGroup GLCR := isTopologicalGroup_tensorGL ℝ ℂ ℝ
scoped instance instT2GLCR : T2Space GLCR := t2Space_tensorGL ℝ ℂ ℝ
scoped instance instLCGLCR : LocallyCompactSpace GLCR := locallyCompactSpace_tensorGL ℝ ℂ ℝ

def eRing : (ℂ ⊗[ℝ] ℝ) ≃+* ℂ :=
  @AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)

theorem eRing_tmul (z : ℂ) (a : ℝ) : eRing (z ⊗ₜ[ℝ] a) = (a : ℂ) * z := by
  show (Algebra.TensorProduct.rid ℝ ℝ ℂ) (z ⊗ₜ[ℝ] a) = (a : ℂ) * z
  rw [Algebra.TensorProduct.rid_tmul, Complex.real_smul]

def rGL : GLCR →* GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.map (eRing).toRingHom

theorem rGL_val (x : GLCR) (i j : Fin 2) :
    ((rGL x : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j = eRing ((x : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) i j) :=
  rfl

abbrev σGL : GLCR →* GLCR := sigmaGL ℝ ℂ ℝ Complex.conjAe

abbrev ιGL : GL (Fin 2) ℝ →* GLCR := toTensorGL ℝ ℂ ℝ

def jGL : GL (Fin 2) ℝ →* GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ)

theorem jGL_val (g : GL (Fin 2) ℝ) (i j : Fin 2) :
    ((jGL g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j = ((g : Matrix (Fin 2) (Fin 2) ℝ) i j : ℂ) :=
  rfl

theorem rGL_ιGL (g : GL (Fin 2) ℝ) : rGL (ιGL g) = jGL g := by
  apply Units.ext
  ext i j
  rw [jGL_val, rGL_val]
  show eRing ((1 : ℂ) ⊗ₜ[ℝ] ((g : Matrix (Fin 2) (Fin 2) ℝ) i j)) = _
  rw [eRing_tmul, mul_one]

theorem smul_tmul_eq (r : ℝ) (z : ℂ) (a : ℝ) : r • (z ⊗ₜ[ℝ] a) = z ⊗ₜ[ℝ] (r * a) := by
  rw [TensorProduct.RightActions.smul_def]
  simp [TensorProduct.smul_tmul', smul_eq_mul]

theorem smul_add_CR (r : ℝ) (x y : ℂ ⊗[ℝ] ℝ) : r • (x + y) = r • x + r • y := by
  rw [TensorProduct.RightActions.smul_def, TensorProduct.RightActions.smul_def,
    TensorProduct.RightActions.smul_def, map_add, smul_add, map_add]

def eLin : (ℂ ⊗[ℝ] ℝ) →ₗ[ℝ] ℂ where
  toFun := eRing
  map_add' := fun x y => map_add eRing x y
  map_smul' := by
    intro r x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
        rw [smul_tmul_eq, eRing_tmul, eRing_tmul, RingHom.id_apply, Complex.real_smul]
        push_cast
        ring
    | add x y hx hy =>
        rw [smul_add_CR, map_add, hx, hy, map_add, smul_add]

theorem continuous_eRing : Continuous (eRing : ℂ ⊗[ℝ] ℝ → ℂ) :=
  IsModuleTopology.continuous_of_linearMap eLin

theorem sigmaTensor_tmul (z : ℂ) (a : ℝ) :
    sigmaTensor ℝ ℂ ℝ Complex.conjAe (z ⊗ₜ[ℝ] a) = (Complex.conjAe z) ⊗ₜ[ℝ] a := by
  show (Algebra.TensorProduct.map (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom (AlgHom.id ℝ ℝ)) (z ⊗ₜ[ℝ] a) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

def σLin : (ℂ ⊗[ℝ] ℝ) →ₗ[ℝ] (ℂ ⊗[ℝ] ℝ) where
  toFun := sigmaTensor ℝ ℂ ℝ Complex.conjAe
  map_add' := fun x y => map_add _ x y
  map_smul' := by
    intro r x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
        rw [smul_tmul_eq, sigmaTensor_tmul, sigmaTensor_tmul, RingHom.id_apply, smul_tmul_eq]
    | add x y hx hy =>
        rw [smul_add_CR, map_add, hx, hy, map_add, smul_add_CR]

theorem continuous_sigmaTensor : Continuous (sigmaTensor ℝ ℂ ℝ Complex.conjAe : ℂ ⊗[ℝ] ℝ → ℂ ⊗[ℝ] ℝ) :=
  IsModuleTopology.continuous_of_linearMap σLin

theorem continuous_rGL : Continuous (rGL : GLCR → GL (Fin 2) ℂ) := by
  refine Continuous.units_map _ ?_
  change Continuous fun M : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) => M.map eRing
  exact continuous_id.matrix_map continuous_eRing

theorem continuous_σGL : Continuous (σGL : GLCR → GLCR) := by
  refine Continuous.units_map _ ?_
  change Continuous fun M : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) => M.map (sigmaTensor ℝ ℂ ℝ Complex.conjAe)
  exact continuous_id.matrix_map continuous_sigmaTensor

scoped instance instT2GLR : T2Space (GL (Fin 2) ℝ) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) ℝ) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → ℝ))
  exact Units.isEmbedding_embedProduct.t2Space

scoped instance instLCGLR : LocallyCompactSpace (GL (Fin 2) ℝ) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  haveI : T2Space (Matrix (Fin 2) (Fin 2) ℝ) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → ℝ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance instSCGLR : SecondCountableTopology (GL (Fin 2) ℝ) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℝ))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

abbrev Dd (d : ℝˣ) : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.scalar (Fin 2) d

abbrev Tσ (d : ℝˣ) : Subgroup GLCR := twistedCentralizer ℝ ℂ ℝ Complex.conjAe (ιGL (Dd d))

theorem main
    (d : ℝˣ) (φ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (τ' : @Measure
      (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)))
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))) τ') :
    ∃ w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ,
      IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe
          (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) τ' φ w ∧
        Continuous w := by
  letI : MeasurableSpace (Tσ d) := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (ιGL (Dd d))
  haveI : BorelSpace (Tσ d) := ⟨rfl⟩
  haveI : Measure.IsHaarMeasure τ' := hτ'
  letI : MeasurableSpace GLCR := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace GLCR := borelSpace_glBorelOf _
  letI : MeasurableSpace (GL (Fin 2) ℝ) := glBorelOf ℝ
  haveI : BorelSpace (GL (Fin 2) ℝ) := borelSpace_glBorelOf _

  obtain ⟨hι, U, hU, hT, hKC⟩ :=
    AutomorphicForm.isClosedEmbedding_toTensorGL_and_exists_nhds_one_twistedCentralizer_iff_and_forall_isCompact_conjAe d
  have h1U : (1 : GL (Fin 2) ℝ) ∈ U := mem_of_mem_nhds hU
  have hT1 : ∀ x : GLCR, x ∈ Tσ d ↔ ∃ m : GL (Fin 2) ℝ, x = ιGL m := by
    intro x
    have h := hT 1 h1U x
    rw [one_mul] at h
    change x ∈ Tσ d ↔ _ at h
    rw [h]
    constructor
    · rintro ⟨m, -, hm⟩; exact ⟨m, hm⟩
    · rintro ⟨m, hm⟩
      refine ⟨m, ?_, hm⟩
      rw [Subgroup.mem_centralizer_singleton_iff, mul_one, one_mul]

  have hKφc : IsCompact (tsupport φ) := hφc
  obtain ⟨K, hK, hKprop⟩ := hKC (rGL '' tsupport φ) (hKφc.image continuous_rGL)
  have hrep : ∀ x : GLCR, φ (x⁻¹ * ιGL (Dd d) * σGL x) ≠ 0 →
      ∃ (m : GL (Fin 2) ℝ) (k : GLCR), k ∈ K ∧ x = ιGL m * k := by
    intro x hx
    refine hKprop 1 h1U x ?_
    rw [one_mul]
    exact ⟨x⁻¹ * ιGL (Dd d) * σGL x, subset_tsupport _ hx, rfl⟩

  have hmemι : ∀ m : GL (Fin 2) ℝ, ιGL m ∈ Tσ d := fun m => (hT1 _).2 ⟨m, rfl⟩
  let eFun : GL (Fin 2) ℝ → Tσ d := fun m => ⟨ιGL m, hmemι m⟩
  have heFun_inj : Function.Injective eFun := by
    intro a b h
    exact hι.injective (congrArg Subtype.val h)
  have heFun_surj : Function.Surjective eFun := by
    intro t
    obtain ⟨m, hm⟩ := (hT1 t.1).1 t.2
    exact ⟨m, Subtype.ext hm.symm⟩
  let eEquiv : GL (Fin 2) ℝ ≃ Tσ d := Equiv.ofBijective eFun ⟨heFun_inj, heFun_surj⟩
  have heval : ∀ m, ((eEquiv m : Tσ d) : GLCR) = ιGL m := fun m => rfl
  have heval' : ∀ t : Tσ d, ιGL (eEquiv.symm t) = (t : GLCR) := by
    intro t
    have := heval (eEquiv.symm t)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have hcont : Continuous eFun :=
    Continuous.subtype_mk (hι.continuous) _
  have hcont_symm : Continuous eEquiv.symm := by
    rw [hι.isEmbedding.isInducing.continuous_iff]
    have : (ιGL : GL (Fin 2) ℝ → GLCR) ∘ eEquiv.symm = Subtype.val := funext heval'
    rw [this]
    exact continuous_subtype_val
  let eMul : GL (Fin 2) ℝ ≃ₜ* Tσ d :=
    { toEquiv := eEquiv
      map_mul' := fun a b => Subtype.ext (by
        show ιGL (a * b) = ιGL a * ιGL b
        exact map_mul _ a b)
      continuous_toFun := hcont
      continuous_invFun := hcont_symm }
  have heMul_meas : Measurable (eMul : GL (Fin 2) ℝ → Tσ d) :=
    (show Continuous (eMul : GL (Fin 2) ℝ → Tσ d) from hcont).measurable
  have heMul_symm_meas : Measurable (eMul.symm : Tσ d → GL (Fin 2) ℝ) :=
    (show Continuous (eMul.symm : Tσ d → GL (Fin 2) ℝ) from hcont_symm).measurable

  let ν : Measure (GL (Fin 2) ℝ) := Measure.map eMul.symm τ'
  haveI hνH : Measure.IsHaarMeasure ν := ContinuousMulEquiv.isHaarMeasure_map τ' eMul.symm
  haveI : Measure.IsMulRightInvariant ν :=
    (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two ν).1
  have hτ'eq : Measure.map eMul ν = τ' := by
    show Measure.map eMul (Measure.map eMul.symm τ') = τ'
    rw [Measure.map_map heMul_meas heMul_symm_meas]
    have : (eMul : GL (Fin 2) ℝ → Tσ d) ∘ (eMul.symm : Tσ d → GL (Fin 2) ℝ) = id :=
      funext fun t => eMul.apply_symm_apply t
    rw [this, Measure.map_id]

  obtain ⟨w, hwc, hws, hw0, hwn⟩ :=
    MeasureTheory.exists_continuous_hasCompactSupport_forall_integral_comp_mul_eq_one
      ν (toTensorGL ℝ ℂ ℝ) hι K hK
  refine ⟨w, ⟨hw0, hwc.measurable, hws, fun x hx => ?_⟩, hwc⟩
  obtain ⟨m, k, hk, rfl⟩ := hrep x hx
  change ∫ t : Tσ d, w ((t : GLCR) * (ιGL m * k)) ∂τ' = 1
  rw [← hτ'eq, MeasureTheory.integral_map heMul_meas.aemeasurable]
  · exact hwn m k hk
  · exact (hwc.comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable

end P2mRamModel
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_conjAe_toTensorGL_scalar_and_continuous.P2mRamModel"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_conjAe_toTensorGL_scalar_and_continuous.P2mRamModel"

theorem solution
    (d : ℝˣ) (φ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (τ' : @Measure
      (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)))
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))) τ') :
    ∃ w : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ,
      IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe
          (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) τ' φ w ∧
        Continuous w := by
  exact P2mRamModel.main d φ hφ hφc τ' hτ'

end S_AutomorphicForm_exists_isTwistedSectionFnOn_conjAe_toTensorGL_scalar_and_continuous
end P2MW
export P2MW.S_AutomorphicForm_exists_isTwistedSectionFnOn_conjAe_toTensorGL_scalar_and_continuous (solution)
