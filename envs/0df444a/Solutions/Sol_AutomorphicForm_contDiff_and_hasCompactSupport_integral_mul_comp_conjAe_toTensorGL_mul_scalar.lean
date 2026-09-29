-- Prove2me | solution 1 for AutomorphicForm.contDiff_and_hasCompactSupport_integral_mul_comp_conjAe_toTensorGL_mul_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b7b26d67-af1f-5060-9e81-36a285d7883e

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_contDiff_and_hasCompactSupport_integral_mul_comp_conjAe_toTensorGL_mul_scalar

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace P2mSmoothPsi

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

theorem secondCountable_CR : SecondCountableTopology (ℂ ⊗[ℝ] ℝ) := by
  let b := Module.finBasis ℝ (ℂ ⊗[ℝ] ℝ)
  let f : (ℂ ⊗[ℝ] ℝ) ≃ₗ[ℝ] (Fin (Module.finrank ℝ (ℂ ⊗[ℝ] ℝ)) → ℝ) := b.equivFun
  have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f.toLinearMap
  have hfs : Continuous f.symm := IsModuleTopology.continuous_of_linearMap f.symm.toLinearMap
  let h : (ℂ ⊗[ℝ] ℝ) ≃ₜ (Fin (Module.finrank ℝ (ℂ ⊗[ℝ] ℝ)) → ℝ) :=
    { toEquiv := f.toEquiv, continuous_toFun := hf, continuous_invFun := hfs }
  exact h.secondCountableTopology

scoped instance instSecondCountableGLCR : SecondCountableTopology GLCR := by
  haveI := secondCountable_CR
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ ⊗[ℝ] ℝ))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

scoped instance instT2GLR : T2Space (GL (Fin 2) ℝ) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) ℝ) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → ℝ))
  exact Units.isEmbedding_embedProduct.t2Space

theorem isClosedEmbedding_jGL : IsClosedEmbedding (jGL : GL (Fin 2) ℝ → GL (Fin 2) ℂ) := by
  let φM : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := (Algebra.linearMap ℝ ℂ).mapMatrix
  have hφMapp : ∀ M, φM M = M.map (algebraMap ℝ ℂ) := fun M => rfl
  haveI : T2Space (Matrix (Fin 2) (Fin 2) ℝ) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → ℝ))
  haveI : T2Space (Matrix (Fin 2) (Fin 2) ℂ) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → ℂ))
  haveI : IsTopologicalAddGroup (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin 2 → Fin 2 → ℝ))
  haveI : IsTopologicalAddGroup (Matrix (Fin 2) (Fin 2) ℂ) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin 2 → Fin 2 → ℂ))
  haveI : ContinuousSMul ℝ (Matrix (Fin 2) (Fin 2) ℝ) := inferInstanceAs (ContinuousSMul ℝ (Fin 2 → Fin 2 → ℝ))
  haveI : ContinuousSMul ℝ (Matrix (Fin 2) (Fin 2) ℂ) := inferInstanceAs (ContinuousSMul ℝ (Fin 2 → Fin 2 → ℂ))
  haveI : FiniteDimensional ℝ (Matrix (Fin 2) (Fin 2) ℝ) := inferInstanceAs (FiniteDimensional ℝ (Fin 2 → Fin 2 → ℝ))
  have hker : LinearMap.ker φM = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro M N h
    rw [hφMapp, hφMapp] at h
    exact Matrix.map_injective (RingHom.injective _) h
  have hφ : IsClosedEmbedding (φM : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℂ) :=
    LinearMap.isClosedEmbedding_of_injective hker
  have hψ : IsClosedEmbedding (MulOpposite.op ∘ φM ∘ MulOpposite.unop :
      (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ → (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.isClosedEmbedding.comp (hφ.comp MulOpposite.opHomeomorph.symm.isClosedEmbedding)
  have hcomp : IsClosedEmbedding
      (Prod.map φM (MulOpposite.op ∘ φM ∘ MulOpposite.unop) ∘ Units.embedProduct (Matrix (Fin 2) (Fin 2) ℝ)) :=
    (hφ.prodMap hψ).comp Units.isClosedEmbedding_embedProduct
  have heq : (Prod.map φM (MulOpposite.op ∘ φM ∘ MulOpposite.unop) ∘ Units.embedProduct (Matrix (Fin 2) (Fin 2) ℝ)) =
      Units.embedProduct (Matrix (Fin 2) (Fin 2) ℂ) ∘ jGL := by
    funext u; rfl
  rw [heq] at hcomp
  exact Units.isClosedEmbedding_embedProduct.of_comp_iff.1 hcomp

def cc (x : GLCR) : (Fin 2 → Fin 2 → ℂ) × (Fin 2 → Fin 2 → ℂ) :=
  (fun i j => ((rGL x⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j,
   fun i j => ((rGL (σGL x) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j)

theorem continuous_cc : Continuous cc := by
  have h1 : Continuous fun x : GLCR => ((rGL x⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :=
    Units.continuous_val.comp (continuous_rGL.comp continuous_inv)
  have h2 : Continuous fun x : GLCR => ((rGL (σGL x) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) :=
    Units.continuous_val.comp (continuous_rGL.comp continuous_σGL)
  refine Continuous.prodMk ?_ ?_
  · exact continuous_pi fun i => continuous_pi fun j => h1.matrix_elem i j
  · exact continuous_pi fun i => continuous_pi fun j => h2.matrix_elem i j

def bil (d : ℝ) (m : (Fin 2 → Fin 2 → ℂ) × (Fin 2 → Fin 2 → ℂ)) (E : Fin 2 → Fin 2 → ℝ) : Fin 2 → Fin 2 → ℂ :=
  fun i j => ∑ l, (∑ k, m.1 i k * ((E k l * d : ℝ) : ℂ)) * m.2 l j

theorem contDiff_bil (d : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ((Fin 2 → Fin 2 → ℂ) × (Fin 2 → Fin 2 → ℂ)) × (Fin 2 → Fin 2 → ℝ) =>
      bil d q.1 q.2) := by
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  simp only [bil]
  refine ContDiff.sum fun l _ => ContDiff.mul (ContDiff.sum fun k _ => ContDiff.mul ?_ ?_) ?_
  · exact (contDiff_apply_apply ℝ ℂ i k).comp (contDiff_fst.comp contDiff_fst)
  · have h : ContDiff ℝ (⊤ : ℕ∞) fun q : ((Fin 2 → Fin 2 → ℂ) × (Fin 2 → Fin 2 → ℂ)) × (Fin 2 → Fin 2 → ℝ) =>
        q.2 k l * d := ((contDiff_apply_apply ℝ ℝ k l).comp contDiff_snd).mul contDiff_const
    exact Complex.ofRealCLM.contDiff.comp h
  · exact (contDiff_apply_apply ℝ ℂ l j).comp (contDiff_snd.comp contDiff_fst)

theorem entries_eq_bil (d : ℝˣ) (x : GLCR) (g : GL (Fin 2) ℝ) :
    (fun i j => ((rGL (x⁻¹ * ιGL (g * Matrix.GeneralLinearGroup.scalar (Fin 2) d) * σGL x) : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) i j) = bil (d : ℝ) (cc x) (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  funext i j
  rw [map_mul, map_mul, rGL_ιGL, Units.val_mul, Units.val_mul, Matrix.mul_apply]
  simp only [bil, cc]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [jGL_val, Units.val_mul]
  have : ((Matrix.GeneralLinearGroup.scalar (Fin 2) d : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.diagonal fun _ => (d : ℝ) := rfl
  rw [this, Matrix.mul_diagonal]

theorem main
    (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
    (φ : GL (Fin 2) ℂ → ℂ)
    (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
    (d : ℝˣ)
    (α : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hαc : Continuous α) (hαs : HasCompactSupport α)
    (ψ : GL (Fin 2) ℝ → ℂ)
    (hψ : ∀ s : GL (Fin 2) ℝ, ψ s = ∫ x, (α x : ℂ) *
      φ (rGL (x⁻¹ * ιGL (s * Matrix.GeneralLinearGroup.scalar (Fin 2) d) * σGL x)) ∂μL) :
    (∃ Ψ : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧
        ∀ g, ψ g = Ψ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport ψ := by
  letI : MeasurableSpace GLCR := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace GLCR := borelSpace_glBorelOf _
  haveI : Measure.IsHaarMeasure μL := hμL
  obtain ⟨⟨Φ, hΦ, hφΦ⟩, hφc⟩ := hφ
  set D : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.scalar (Fin 2) d with hD

  set Kα : Set GLCR := tsupport α with hKα
  have hKαc : IsCompact Kα := hαs
  set Kφ : Set (GL (Fin 2) ℂ) := tsupport φ with hKφ
  have hKφc : IsCompact Kφ := hφc
  set conjMap : GLCR × GL (Fin 2) ℂ → GL (Fin 2) ℂ := fun p => rGL p.1 * p.2 * (rGL (σGL p.1))⁻¹ with hconjMap
  have hconjc : Continuous conjMap :=
    ((continuous_rGL.comp continuous_fst).mul continuous_snd).mul
      ((continuous_rGL.comp (continuous_σGL.comp continuous_fst)).inv)
  set C : Set (GL (Fin 2) ℂ) := conjMap '' (Kα ×ˢ Kφ) with hC
  have hCc : IsCompact C := (hKαc.prod hKφc).image hconjc
  set Kψ : Set (GL (Fin 2) ℝ) := (fun s => jGL (s * D)) ⁻¹' C with hKψ
  have hKψc : IsCompact Kψ := by
    have h1 : IsCompact (jGL ⁻¹' C) := isClosedEmbedding_jGL.isCompact_preimage hCc
    have h2 : Kψ = (Homeomorph.mulRight D) ⁻¹' (jGL ⁻¹' C) := rfl
    rw [h2]
    exact (Homeomorph.isCompact_preimage _).2 h1
  have hψ0 : ∀ s, s ∉ Kψ → ψ s = 0 := by
    intro s hs
    rw [hψ s]
    have : (fun x : GLCR => (α x : ℂ) * φ (rGL (x⁻¹ * ιGL (s * D) * σGL x))) = fun _ => 0 := by
      funext x
      by_cases hx : α x = 0
      · rw [hx, Complex.ofReal_zero, zero_mul]
      by_cases hg : φ (rGL (x⁻¹ * ιGL (s * D) * σGL x)) = 0
      · rw [hg, mul_zero]
      exfalso
      apply hs
      show jGL (s * D) ∈ C
      refine ⟨(x, rGL (x⁻¹ * ιGL (s * D) * σGL x)), ⟨subset_tsupport _ hx, subset_tsupport _ hg⟩, ?_⟩
      show rGL x * rGL (x⁻¹ * ιGL (s * D) * σGL x) * (rGL (σGL x))⁻¹ = jGL (s * D)
      rw [← rGL_ιGL, map_mul, map_mul, map_inv]
      group
    rw [this, integral_zero]
  have hψcs : HasCompactSupport ψ := HasCompactSupport.intro hKψc hψ0
  refine ⟨?_, hψcs⟩

  obtain ⟨RM, hRM⟩ := (hKαc.image continuous_cc).isBounded.subset_closedBall 0
  obtain ⟨RP, hRP⟩ := (hKψc.image (continuous_pi fun i => continuous_pi fun j =>
    (Units.continuous_val.matrix_elem i j : Continuous fun g : GL (Fin 2) ℝ =>
      (g : Matrix (Fin 2) (Fin 2) ℝ) i j))).isBounded.subset_closedBall 0
  let χM : ContDiffBump (0 : (Fin 2 → Fin 2 → ℂ) × (Fin 2 → Fin 2 → ℂ)) :=
    ⟨max RM 1, max RM 1 + 1, lt_max_of_lt_right one_pos, lt_add_one _⟩
  let χP : ContDiffBump (0 : Fin 2 → Fin 2 → ℝ) :=
    ⟨max RP 1, max RP 1 + 1, lt_max_of_lt_right one_pos, lt_add_one _⟩
  have hχM1 : ∀ x, α x ≠ 0 → (χM : _ → ℝ) (cc x) = 1 := by
    intro x hx
    apply χM.one_of_mem_closedBall
    have : cc x ∈ Metric.closedBall 0 RM := hRM ⟨x, subset_tsupport _ hx, rfl⟩
    exact Metric.closedBall_subset_closedBall (le_max_left _ _) this
  have hχP1 : ∀ g : GL (Fin 2) ℝ, ψ g ≠ 0 →
      (χP : _ → ℝ) (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) = 1 := by
    intro g hg
    apply χP.one_of_mem_closedBall
    have hgK : g ∈ Kψ := by
      by_contra h
      exact hg (hψ0 g h)
    have : (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) ∈ Metric.closedBall 0 RP := hRP ⟨g, hgK, rfl⟩
    exact Metric.closedBall_subset_closedBall (le_max_left _ _) this

  let Ψk : ((Fin 2 → Fin 2 → ℂ) × (Fin 2 → Fin 2 → ℂ)) × (Fin 2 → Fin 2 → ℝ) → ℂ :=
    fun q => (((χM : _ → ℝ) q.1 * (χP : _ → ℝ) q.2 : ℝ) : ℂ) * Φ (bil (d : ℝ) q.1 q.2)
  have hΨk : ContDiff ℝ (⊤ : ℕ∞) Ψk := by
    refine ContDiff.mul ?_ (hΦ.comp (contDiff_bil (d : ℝ)))
    exact Complex.ofRealCLM.contDiff.comp
      ((χM.contDiff.comp contDiff_fst).mul (χP.contDiff.comp contDiff_snd))
  have hΨkc : HasCompactSupport Ψk := by
    refine HasCompactSupport.intro (χM.hasCompactSupport.prod χP.hasCompactSupport) ?_
    intro q hq
    rw [Set.mem_prod, not_and_or] at hq
    rcases hq with h | h
    · simp only [Ψk, image_eq_zero_of_notMem_tsupport h, zero_mul, Complex.ofReal_zero]
    · simp only [Ψk, image_eq_zero_of_notMem_tsupport h, mul_zero, Complex.ofReal_zero, zero_mul]

  have hsmooth := MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
    μL cc continuous_cc α hαc hαs Ψk hΨk hΨkc
  refine ⟨fun E => ∫ x, α x • Ψk (cc x, E) ∂μL, hsmooth, fun g => ?_⟩

  set E : Fin 2 → Fin 2 → ℝ := fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j with hE
  have hpt : ∀ x, α x • Ψk (cc x, E) =
      ((χP : _ → ℝ) E : ℂ) * ((α x : ℂ) * φ (rGL (x⁻¹ * ιGL (g * D) * σGL x))) := by
    intro x
    by_cases hx : α x = 0
    · rw [hx, zero_smul, Complex.ofReal_zero, zero_mul, mul_zero]
    rw [hφΦ, entries_eq_bil, Complex.real_smul]
    simp only [Ψk, hχM1 x hx, one_mul]
    ring
  show ψ g = ∫ x, α x • Ψk (cc x, E) ∂μL
  simp_rw [hpt]
  rw [integral_const_mul, ← hψ g]
  by_cases hg : ψ g = 0
  · rw [hg, mul_zero]
  · rw [hχP1 g hg, Complex.ofReal_one, one_mul]

end P2mSmoothPsi
p2m_reactivate "P2MW.S_AutomorphicForm_contDiff_and_hasCompactSupport_integral_mul_comp_conjAe_toTensorGL_mul_scalar.P2mSmoothPsi"

end
p2m_reactivate "P2MW.S_AutomorphicForm_contDiff_and_hasCompactSupport_integral_mul_comp_conjAe_toTensorGL_mul_scalar.P2mSmoothPsi"

theorem solution
    (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
    (φ : GL (Fin 2) ℂ → ℂ)
    (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
    (d : ℝˣ)
    (α : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ) (hαc : Continuous α) (hαs : HasCompactSupport α)
    (ψ : GL (Fin 2) ℝ → ℂ)
    (hψ : ∀ s : GL (Fin 2) ℝ, ψ s = ∫ x, (α x : ℂ) *
      φ (Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom (x⁻¹ * toTensorGL ℝ ℂ ℝ (s * Matrix.GeneralLinearGroup.scalar (Fin 2) d) * sigmaGL ℝ ℂ ℝ Complex.conjAe x) : GL (Fin 2) ℂ) ∂μL) :
    (∃ Ψ : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Ψ ∧
        ∀ g, ψ g = Ψ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport ψ := by
  exact P2mSmoothPsi.main μL hμL φ hφ d α hαc hαs ψ hψ

end S_AutomorphicForm_contDiff_and_hasCompactSupport_integral_mul_comp_conjAe_toTensorGL_mul_scalar
end P2MW
export P2MW.S_AutomorphicForm_contDiff_and_hasCompactSupport_integral_mul_comp_conjAe_toTensorGL_mul_scalar (solution)
