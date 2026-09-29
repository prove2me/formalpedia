-- Prove2me | solution 1 for AutomorphicForm.exists_isSigmaConjugate_scalar_of_coupled
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/322fcc34-3571-5e8f-9b09-1abd2e878624

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_of_coupled

set_option autoImplicit false

open MeasureTheory NumberField
open scoped TensorProduct
open scoped TensorProduct.RightActions

noncomputable section

namespace R1SigmaConjScalar

section LinearAlgebra

variable {R : Type*} [CommRing R]

def unipUpper : GL (Fin 2) R :=
  ⟨!![1, 1; 0, 1], !![1, -1; 0, 1],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp,
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp⟩

def unipLower : GL (Fin 2) R :=
  ⟨!![1, 0; 1, 1], !![1, 0; -1, 1],
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp,
    by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp⟩

@[scoped simp] theorem coe_unipUpper : ((unipUpper : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![1, 1; 0, 1] :=
  rfl

@[scoped simp] theorem coe_unipLower : ((unipLower : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![1, 0; 1, 1] :=
  rfl

theorem entries_of_commute_unip (M : Matrix (Fin 2) (Fin 2) R)
    (h₁ : !![(1 : R), 1; 0, 1] * M = M * !![(1 : R), 1; 0, 1])
    (h₂ : !![(1 : R), 0; 1, 1] * M = M * !![(1 : R), 0; 1, 1]) :
    M 1 0 = 0 ∧ M 0 1 = 0 ∧ M 1 1 = M 0 0 := by
  have e00 := congrFun (congrFun h₁ 0) 0
  have e01 := congrFun (congrFun h₁ 0) 1
  have f11 := congrFun (congrFun h₂ 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, one_mul, mul_one, mul_zero,
    add_zero, zero_add] at e00 e01 f11

  have hc : M 1 0 = 0 := by linear_combination e00
  have hb : M 0 1 = 0 := by linear_combination f11
  exact ⟨hc, hb, by linear_combination e01⟩

theorem exists_eq_scalar_of_commute_unip (ε : GL (Fin 2) R)
    (h₁ : (unipUpper : GL (Fin 2) R) * ε = ε * unipUpper)
    (h₂ : (unipLower : GL (Fin 2) R) * ε = ε * unipLower) :
    ∃ d : Rˣ, ε = Matrix.GeneralLinearGroup.scalar (Fin 2) d := by
  have h₁' : !![(1 : R), 1; 0, 1] * (ε : Matrix (Fin 2) (Fin 2) R) = ε * !![(1 : R), 1; 0, 1] := by
    simpa using congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R)) h₁
  have h₂' : !![(1 : R), 0; 1, 1] * (ε : Matrix (Fin 2) (Fin 2) R) = ε * !![(1 : R), 0; 1, 1] := by
    simpa using congrArg (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R)) h₂
  obtain ⟨hc, hb, hd⟩ := entries_of_commute_unip (ε : Matrix (Fin 2) (Fin 2) R) h₁' h₂'

  have hinv : (ε : Matrix (Fin 2) (Fin 2) R) 0 0 * (ε⁻¹ : GL (Fin 2) R) 0 0 = 1 := by
    have h := congrFun (congrFun (ε.mul_inv) 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h
    rw [hb, zero_mul, add_zero] at h
    exact h
  refine ⟨⟨(ε : Matrix (Fin 2) (Fin 2) R) 0 0, (ε⁻¹ : GL (Fin 2) R) 0 0, hinv, by rw [mul_comm]; exact hinv⟩, ?_⟩
  ext i j
  change (ε : Matrix (Fin 2) (Fin 2) R) i j = Matrix.scalar (Fin 2) ((ε : Matrix (Fin 2) (Fin 2) R) 0 0) i j
  fin_cases i <;> fin_cases j
  · simp
  · simpa using hb
  · simpa using hc
  · simpa using hd

end LinearAlgebra

section Coupling

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L) (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in

theorem sigmaTensor_includeRight (a : A) :
    AutomorphicForm.sigmaTensor K L A σ ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a) =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a := by
  simp [AutomorphicForm.sigmaTensor]

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in

theorem sigmaGL_toTensorGL (g : GL (Fin 2) A) :
    AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.toTensorGL K L A g) = AutomorphicForm.toTensorGL K L A g := by
  ext i j
  change AutomorphicForm.sigmaTensor K L A σ
      ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom ((g : Matrix (Fin 2) (Fin 2) A) i j)) =
    (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom ((g : Matrix (Fin 2) (Fin 2) A) i j)
  exact sigmaTensor_includeRight K L σ A _

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in

theorem coe_toTensorGL (g : GL (Fin 2) A) :
    ((AutomorphicForm.toTensorGL K L A g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (g : Matrix (Fin 2) (Fin 2) A).map (fun a => (1 : L) ⊗ₜ[K] a) :=
  rfl

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem toTensorGL_unipUpper :
    AutomorphicForm.toTensorGL K L A (unipUpper : GL (Fin 2) A) = (unipUpper : GL (Fin 2) (L ⊗[K] A)) := by
  ext i j
  rw [coe_toTensorGL, coe_unipUpper, coe_unipUpper]
  fin_cases i <;> fin_cases j <;> simp [Algebra.TensorProduct.one_def]

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem toTensorGL_unipLower :
    AutomorphicForm.toTensorGL K L A (unipLower : GL (Fin 2) A) = (unipLower : GL (Fin 2) (L ⊗[K] A)) := by
  ext i j
  rw [coe_toTensorGL, coe_unipLower, coe_unipLower]
  fin_cases i <;> fin_cases j <;> simp [Algebra.TensorProduct.one_def]

def sigmaLinear : (L ⊗[K] A) →ₗ[A] (L ⊗[K] A) where
  toFun := AutomorphicForm.sigmaTensor K L A σ
  map_add' := map_add _
  map_smul' a x := by
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    exact sigmaTensor_includeRight K L σ A a

omit [IsTopologicalRing A] in

theorem continuous_sigmaTensor : Continuous (AutomorphicForm.sigmaTensor K L A σ) :=
  IsModuleTopology.continuous_of_linearMap (sigmaLinear K L σ A)

omit [IsTopologicalRing A] in

theorem continuous_sigmaGL : Continuous (AutomorphicForm.sigmaGL K L A σ) := by
  refine Continuous.units_map _ ?_
  change Continuous fun M : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) => M.map (AutomorphicForm.sigmaTensor K L A σ)
  exact continuous_id.matrix_map (continuous_sigmaTensor K L σ A)

omit [IsTopologicalRing A] in

theorem continuous_includeRight :
    Continuous (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
  have h : Continuous fun a : A => a • (1 : L ⊗[K] A) := continuous_id.fun_smul continuous_const
  refine h.congr fun a => ?_
  rw [← Algebra.algebraMap_eq_smul_one]
  rfl

omit [IsTopologicalRing A] in

theorem continuous_toTensorGL : Continuous (AutomorphicForm.toTensorGL K L A) := by
  refine Continuous.units_map _ ?_
  change Continuous fun M : Matrix (Fin 2) (Fin 2) A =>
    M.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom)
  exact continuous_id.matrix_map (continuous_includeRight K L A)

theorem isClosed_twistedCentralizer [T2Space A] (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed (AutomorphicForm.twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  have hset : (AutomorphicForm.twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t => t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    simp [AutomorphicForm.mem_sigmaCentralizer_iff]
  rw [hset]
  refine IsClosed.preimage ?_ isClosed_singleton
  exact (continuous_id.mul continuous_const).mul ((continuous_sigmaGL K L σ A).comp continuous_id).inv

omit [TopologicalSpace A] [IsTopologicalRing A] in

theorem mem_centralizer_of_scalar (c : Aˣ) (g : GL (Fin 2) A) :
    g ∈ Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  ext1
  push_cast
  exact ((Matrix.scalar_commute (c : A) (fun r' => Commute.all _ _) (g : Matrix (Fin 2) (Fin 2) A)).eq).symm

theorem toTensorGL_mem_conj_twistedCentralizer [T2Space A]
    (γ : GL (Fin 2) A) (hγ : ∃ c : Aˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (δ y : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hτ : @Measure.IsOpenPosMeasure _ _ (AutomorphicForm.centralizerBorel A γ) τ)
    (hc : AutomorphicForm.Coupled K L A σ γ δ y τ τ') (g : GL (Fin 2) A) :
    y * AutomorphicForm.toTensorGL K L A g * y⁻¹ ∈ AutomorphicForm.twistedCentralizer K L A σ δ := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  letI mG : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.borelSpace_glBorelOf _
  letI mC : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) :=
    AutomorphicForm.centralizerBorel A γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  letI mT : MeasurableSpace (AutomorphicForm.twistedCentralizer K L A σ δ) :=
    AutomorphicForm.twistedCentralizerBorel K L A σ δ
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L A σ δ) := ⟨rfl⟩

  set S : Set (GL (Fin 2) (L ⊗[K] A)) :=
    (fun x => y * x * y⁻¹) ⁻¹' (AutomorphicForm.twistedCentralizer K L A σ δ : Set (GL (Fin 2) (L ⊗[K] A)))
    with hS_def
  have hS : IsClosed S :=
    (isClosed_twistedCentralizer K L σ A δ).preimage ((continuous_const.mul continuous_id).mul continuous_const)

  set cj : AutomorphicForm.twistedCentralizer K L A σ δ → GL (Fin 2) (L ⊗[K] A) :=
    fun t => y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y with hcj_def
  set e : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) → GL (Fin 2) (L ⊗[K] A) :=
    fun t => AutomorphicForm.toTensorGL K L A (t : GL (Fin 2) A) with he_def
  have hc' : Measure.map cj τ' = Measure.map e τ := hc

  have hL : Measure.map cj τ' Sᶜ = 0 := by
    by_cases hm : AEMeasurable cj τ'
    · rw [Measure.map_apply_of_aemeasurable hm hS.measurableSet.compl]
      have hemp : cj ⁻¹' Sᶜ = ∅ := by
        ext t
        simp only [Set.mem_preimage, Set.mem_compl_iff, hS_def, hcj_def, Set.mem_empty_iff_false, iff_false,
          not_not, SetLike.mem_coe]
        have : y * (y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y) * y⁻¹ = t := by group
        rw [this]
        exact t.2
      rw [hemp, measure_empty]
    · rw [Measure.map_of_not_aemeasurable hm]
      rfl

  have he : Continuous e := (continuous_toTensorGL K L A).comp continuous_subtype_val
  have hR : τ (e ⁻¹' Sᶜ) = 0 := by
    rw [← Measure.map_apply he.measurable hS.measurableSet.compl, ← hc']
    exact hL
  have hempty : e ⁻¹' Sᶜ = ∅ := (hS.isOpen_compl.preimage he).eq_empty_of_measure_zero hR

  obtain ⟨c, rfl⟩ := hγ
  have hg : g ∈ Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A)) :=
    mem_centralizer_of_scalar A c g
  have hmem : e ⟨g, hg⟩ ∈ S := by
    by_contra hnot
    have : (⟨g, hg⟩ : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) A))) ∈
        e ⁻¹' Sᶜ := hnot
    rw [hempty] at this
    exact this
  simpa [hS_def, he_def] using hmem

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in

theorem commute_of_mem (δ y : GL (Fin 2) (L ⊗[K] A)) (g : GL (Fin 2) A)
    (h : y * AutomorphicForm.toTensorGL K L A g * y⁻¹ ∈ AutomorphicForm.twistedCentralizer K L A σ δ) :
    AutomorphicForm.toTensorGL K L A g * (y⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ y) =
      (y⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ y) * AutomorphicForm.toTensorGL K L A g := by
  set eg := AutomorphicForm.toTensorGL K L A g with heg
  set sy := AutomorphicForm.sigmaGL K L A σ y with hsy
  have h1 : (y * eg * y⁻¹) * δ * (AutomorphicForm.sigmaGL K L A σ (y * eg * y⁻¹))⁻¹ = δ :=
    AutomorphicForm.mem_sigmaCentralizer_iff.1 h
  rw [map_mul, map_mul, map_inv, sigmaGL_toTensorGL K L σ A g] at h1
  have h2 : y⁻¹ * δ * sy = eg * (y⁻¹ * δ * sy) * eg⁻¹ := by
    calc y⁻¹ * δ * sy = y⁻¹ * ((y * eg * y⁻¹) * δ * (sy * eg * sy⁻¹)⁻¹) * sy := by rw [h1]
      _ = eg * (y⁻¹ * δ * sy) * eg⁻¹ := by group
  calc eg * (y⁻¹ * δ * sy) = (eg * (y⁻¹ * δ * sy) * eg⁻¹) * eg := by group
    _ = (y⁻¹ * δ * sy) * eg := by rw [← h2]

end Coupling

end R1SigmaConjScalar
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_of_coupled.R1SigmaConjScalar"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_of_coupled.R1SigmaConjScalar"

open R1SigmaConjScalar in
theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    (γ : GL (Fin 2) A) (hγ : ∃ c : Aˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (δ y : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hτ : @Measure.IsOpenPosMeasure _ _ (AutomorphicForm.centralizerBorel A γ) τ)
    (hc : AutomorphicForm.Coupled K L A σ γ δ y τ τ') :
    ∃ d : (L ⊗[K] A)ˣ, AutomorphicForm.IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) d) := by
  have hmem := toTensorGL_mem_conj_twistedCentralizer K L σ A γ hγ δ y τ τ' hτ hc
  have hU := commute_of_mem K L σ A δ y unipUpper (hmem unipUpper)
  have hLo := commute_of_mem K L σ A δ y unipLower (hmem unipLower)
  rw [toTensorGL_unipUpper] at hU
  rw [toTensorGL_unipLower] at hLo
  obtain ⟨d, hd⟩ := exists_eq_scalar_of_commute_unip (y⁻¹ * δ * AutomorphicForm.sigmaGL K L A σ y) hU hLo
  exact ⟨d, y, hd.symm⟩

end S_AutomorphicForm_exists_isSigmaConjugate_scalar_of_coupled
end P2MW
export P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_of_coupled (solution)
