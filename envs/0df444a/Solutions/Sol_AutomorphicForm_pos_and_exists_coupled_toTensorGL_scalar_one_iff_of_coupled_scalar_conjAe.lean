-- Prove2me | solution 1 for AutomorphicForm.pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8e6cf3dc-0058-5958-bbfb-0783952650a8

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace K42RRS

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

end K42RRS
p2m_reactivate "P2MW.S_AutomorphicForm_pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe.K42RRS"

namespace K42RRS2

open scoped Pointwise

section Generic

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem sigmaTensor_tmul (x : L) (a : A) : sigmaTensor K L A σ (x ⊗ₜ[K] a) = σ x ⊗ₜ[K] a := by
  show (Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A)) (x ⊗ₜ a) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem sigmaGL_apply (g : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((sigmaGL K L A σ g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      sigmaTensor K L A σ ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) :=
  rfl

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem sigmaGL_scalar (u : (L ⊗[K] A)ˣ) :
    sigmaGL K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (sigmaTensor K L A σ).toMonoidHom u) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [sigmaGL_apply]
  show sigmaTensor K L A σ (Matrix.scalar (Fin 2) (u : L ⊗[K] A) i j) =
    Matrix.scalar (Fin 2) (sigmaTensor K L A σ (u : L ⊗[K] A)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero _

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem toTensorGL_scalar (c : Aˣ) :
    toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom).toMonoidHom c) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  show (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom (Matrix.scalar (Fin 2) (c : A) i j) =
    Matrix.scalar (Fin 2) ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom (c : A)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero _

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem scalar_val_zero_zero (u : (L ⊗[K] A)ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) 0 0 = u := by
  show Matrix.scalar (Fin 2) (u : L ⊗[K] A) 0 0 = u
  rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]

omit [FiniteDimensional K L] [TopologicalSpace A] [IsTopologicalRing A] in
theorem scalar_comm (u : (L ⊗[K] A)ˣ) (g : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  apply Units.ext
  show Matrix.scalar (Fin 2) (u : L ⊗[K] A) * (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
    (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * Matrix.scalar (Fin 2) (u : L ⊗[K] A)
  exact (Matrix.scalar_commute (u : L ⊗[K] A) (fun r => Commute.all _ r) _).eq

def conjEquiv (δ δ₁ x : GL (Fin 2) (L ⊗[K] A)) (hx : δ₁ = x⁻¹ * δ * sigmaGL K L A σ x) :
    twistedCentralizer K L A σ δ ≃ₜ* twistedCentralizer K L A σ δ₁ where
  toFun t := ⟨x⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * x, by
    have ht := mem_sigmaCentralizer_iff.mp t.2
    rw [mem_sigmaCentralizer_iff, hx, map_mul, map_mul, map_inv]
    calc x⁻¹ * ↑t * x * (x⁻¹ * δ * sigmaGL K L A σ x) * ((sigmaGL K L A σ x)⁻¹ * sigmaGL K L A σ ↑t * sigmaGL K L A σ x)⁻¹
        = x⁻¹ * (↑t * δ * (sigmaGL K L A σ ↑t)⁻¹) * sigmaGL K L A σ x := by group
      _ = x⁻¹ * δ * sigmaGL K L A σ x := by rw [ht]⟩
  invFun s := ⟨x * (s : GL (Fin 2) (L ⊗[K] A)) * x⁻¹, by
    have hs := mem_sigmaCentralizer_iff.mp s.2
    rw [mem_sigmaCentralizer_iff, map_mul, map_mul, map_inv]
    calc x * ↑s * x⁻¹ * δ * (sigmaGL K L A σ x * sigmaGL K L A σ ↑s * (sigmaGL K L A σ x)⁻¹)⁻¹
        = x * (↑s * (x⁻¹ * δ * sigmaGL K L A σ x) * (sigmaGL K L A σ ↑s)⁻¹) * (sigmaGL K L A σ x)⁻¹ := by group
      _ = x * (↑s * δ₁ * (sigmaGL K L A σ ↑s)⁻¹) * (sigmaGL K L A σ x)⁻¹ := by rw [← hx]
      _ = x * δ₁ * (sigmaGL K L A σ x)⁻¹ := by rw [hs]
      _ = δ := by rw [hx]; group⟩
  left_inv t := Subtype.ext (by simp [mul_assoc])
  right_inv s := Subtype.ext (by simp [mul_assoc])
  map_mul' t s := Subtype.ext (by
    show x⁻¹ * (↑t * ↑s) * x = x⁻¹ * ↑t * x * (x⁻¹ * ↑s * x)
    group)
  continuous_toFun := by
    haveI := isTopologicalRing_tensor K L A
    haveI := isTopologicalGroup_tensorGL K L A
    exact continuous_induced_rng.2 ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  continuous_invFun := by
    haveI := isTopologicalRing_tensor K L A
    haveI := isTopologicalGroup_tensorGL K L A
    exact continuous_induced_rng.2 ((continuous_const.mul continuous_subtype_val).mul continuous_const)

theorem conjEquiv_apply_val (δ δ₁ x : GL (Fin 2) (L ⊗[K] A)) (hx : δ₁ = x⁻¹ * δ * sigmaGL K L A σ x)
    (t : twistedCentralizer K L A σ δ) :
    ((conjEquiv K L A σ δ δ₁ x hx t : twistedCentralizer K L A σ δ₁) : GL (Fin 2) (L ⊗[K] A)) =
      x⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * x :=
  rfl

theorem transport (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (hμ : ∀ g : GL (Fin 2) (L ⊗[K] A),
      @Measure.map _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)) (fun z => g * z) μ = μ)
    (δ δ₁ x : GL (Fin 2) (L ⊗[K] A)) (hx : δ₁ = x⁻¹ * δ * sigmaGL K L A σ x)
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (τ₁ : @Measure (twistedCentralizer K L A σ δ₁) (twistedCentralizerBorel K L A σ δ₁))
    (hτ : τ₁ = @Measure.map _ _ (twistedCentralizerBorel K L A σ δ) (twistedCentralizerBorel K L A σ δ₁)
      (conjEquiv K L A σ δ δ₁ x hx) τ')
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I : ℂ)
    (h : IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I) :
    IsTwistedOrbitalIntegralOn K L A σ μ δ₁ τ₁ φ I := by
  letI mG : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := borelSpace_glBorelOf _
  letI m0 : MeasurableSpace (twistedCentralizer K L A σ δ) := twistedCentralizerBorel K L A σ δ
  haveI : BorelSpace (twistedCentralizer K L A σ δ) := ⟨rfl⟩
  letI m1 : MeasurableSpace (twistedCentralizer K L A σ δ₁) := twistedCentralizerBorel K L A σ δ₁
  haveI : BorelSpace (twistedCentralizer K L A σ δ₁) := ⟨rfl⟩
  haveI := isTopologicalRing_tensor K L A
  haveI := isTopologicalGroup_tensorGL K L A
  obtain ⟨w, ⟨hw0, hwm, hwc, hw1⟩, hI⟩ := h
  have hconj : ∀ z : GL (Fin 2) (L ⊗[K] A),
      (x * z)⁻¹ * δ * sigmaGL K L A σ (x * z) = z⁻¹ * δ₁ * sigmaGL K L A σ z := by
    intro z; rw [hx, map_mul]; group
  set e := conjEquiv K L A σ δ δ₁ x hx with he
  refine ⟨fun z => w (x * z), ⟨fun z => hw0 _, hwm.comp (measurable_const_mul x),
    hwc.comp_homeomorph (Homeomorph.mulLeft x), fun z hz => ?_⟩, ?_⟩
  · have hz' : φ ((x * z)⁻¹ * δ * sigmaGL K L A σ (x * z)) ≠ 0 := by rwa [hconj]
    rw [← hw1 (x * z) hz', hτ]
    show ∫ s, w (x * ((s : GL (Fin 2) (L ⊗[K] A)) * z)) ∂(Measure.map (e.toHomeomorph.toMeasurableEquiv) τ') =
      ∫ t, w ((t : GL (Fin 2) (L ⊗[K] A)) * (x * z)) ∂τ'
    rw [integral_map_equiv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show w (x * (x⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * x * z)) = w ((t : GL (Fin 2) (L ⊗[K] A)) * (x * z))
    congr 1; group
  · rw [hI]
    have hμ' : Measure.map (⇑(Homeomorph.mulLeft x).toMeasurableEquiv) μ = μ := hμ x
    conv_lhs => rw [← hμ']
    rw [integral_map_equiv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show φ ((x * z)⁻¹ * δ * sigmaGL K L A σ (x * z)) * (w (x * z) : ℂ) = φ (z⁻¹ * δ₁ * sigmaGL K L A σ z) * (w (x * z) : ℂ)
    rw [hconj]

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe.K42RRS"

section RealComplex

theorem sigmaTensor_conj_conj (z : ℂ ⊗[ℝ] ℝ) :
    sigmaTensor ℝ ℂ ℝ Complex.conjAe (sigmaTensor ℝ ℂ ℝ Complex.conjAe z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul x a =>
    rw [sigmaTensor_tmul, sigmaTensor_tmul]
    congr 1
    exact Complex.conj_conj x
  | add z w hz hw => rw [map_add, map_add, hz, hw]

theorem sigmaGL_conj_conj (g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    sigmaGL ℝ ℂ ℝ Complex.conjAe (sigmaGL ℝ ℂ ℝ Complex.conjAe g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [sigmaGL_apply, sigmaGL_apply, sigmaTensor_conj_conj]

theorem normString_conj (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    normString ℝ ℂ ℝ Complex.conjAe δ = δ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ := by
  rw [AutomorphicForm.normString, Complex.finrank_real_complex]
  simp [List.range_succ]

def ρ : ℂ ⊗[ℝ] ℝ ≃+* ℂ :=
  @AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)

theorem ρ_tmul (x : ℂ) (r : ℝ) : ρ (x ⊗ₜ[ℝ] r) = (r : ℂ) * x := by
  rw [← Complex.real_smul]
  exact Algebra.TensorProduct.rid_tmul (R := ℝ) (S := ℝ) (A := ℂ) r x

theorem ρ_one_tmul (r : ℝ) : ρ ((1 : ℂ) ⊗ₜ[ℝ] r) = (r : ℂ) := by
  rw [ρ_tmul, mul_one]

theorem ρ_sigmaTensor (z : ℂ ⊗[ℝ] ℝ) :
    ρ (sigmaTensor ℝ ℂ ℝ Complex.conjAe z) = (starRingEnd ℂ) (ρ z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul x a =>
    rw [sigmaTensor_tmul, ρ_tmul, ρ_tmul, map_mul, Complex.conj_ofReal]
    rfl
  | add z w hz hw => simp only [map_add, hz, hw]

end RealComplex
p2m_reactivate "P2MW.S_AutomorphicForm_pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe.K42RRS"

end K42RRS2
p2m_reactivate "P2MW.S_AutomorphicForm_pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe.K42RRS"

end
p2m_reactivate "P2MW.S_AutomorphicForm_pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe.K42RRS"

theorem solution
    (μ : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμ : ∀ g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
      @Measure.map _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)) (fun z => g * z) μ = μ)
    (c : ℝˣ) (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
        (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
    (hC : Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ') :
    0 < (c : ℝ) ∧
    ∃ d : ℝˣ, (d : ℝ) * d = c ∧
      ∃ τ₁ : @Measure
          (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)))
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
            (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))),
        @Measure.IsHaarMeasure _ _ _
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe
            (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d))) τ₁ ∧
        Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
          (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) 1 τ τ₁ ∧
        ∀ (φ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℂ) (I : ℂ),
          IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μ δ τ' φ I ↔
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μ
              (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) τ₁ φ I := by
  classical

  haveI := isTopologicalRing_tensor ℝ ℂ ℝ
  haveI := isTopologicalGroup_tensorGL ℝ ℂ ℝ
  haveI := t2Space_tensorGL ℝ ℂ ℝ
  letI mG : MeasurableSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := glBorelOf (ℂ ⊗[ℝ] ℝ)
  haveI : BorelSpace (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borelSpace_glBorelOf _
  letI mT : MeasurableSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
  haveI : BorelSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) := ⟨rfl⟩
  letI mZ : MeasurableSpace (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) :=
    centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
  haveI : BorelSpace (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) := ⟨rfl⟩
  haveI : Measure.IsHaarMeasure τ := hτ
  haveI : Measure.IsHaarMeasure τ' := hτ'

  have hmem := K42RRS.toTensorGL_mem_conj_twistedCentralizer ℝ ℂ Complex.conjAe ℝ
    (Matrix.GeneralLinearGroup.scalar (Fin 2) c) ⟨c, rfl⟩ δ y τ τ' inferInstance hC
  have hU := K42RRS.commute_of_mem ℝ ℂ Complex.conjAe ℝ δ y K42RRS.unipUpper (hmem K42RRS.unipUpper)
  have hLo := K42RRS.commute_of_mem ℝ ℂ Complex.conjAe ℝ δ y K42RRS.unipLower (hmem K42RRS.unipLower)
  rw [K42RRS.toTensorGL_unipUpper] at hU
  rw [K42RRS.toTensorGL_unipLower] at hLo
  obtain ⟨d, hd⟩ := K42RRS.exists_eq_scalar_of_commute_unip
    (y⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe y) hU hLo

  have hN : Matrix.GeneralLinearGroup.scalar (Fin 2) d *
      sigmaGL ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) d) =
      toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
    rw [← hd, map_mul, map_mul, map_inv, K42RRS2.sigmaGL_conj_conj, hδ, K42RRS2.normString_conj]
    group
  rw [K42RRS2.sigmaGL_scalar, ← map_mul, K42RRS2.toTensorGL_scalar] at hN
  have hunits := congrArg (fun g : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) => (g : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) 0 0) hN
  simp only [K42RRS2.scalar_val_zero_zero] at hunits
  rw [Units.val_mul, Units.coe_map, Units.coe_map] at hunits
  have hent : (d : ℂ ⊗[ℝ] ℝ) * sigmaTensor ℝ ℂ ℝ Complex.conjAe d = (1 : ℂ) ⊗ₜ[ℝ] (c : ℝ) := hunits

  set α : ℂ := K42RRS2.ρ (d : ℂ ⊗[ℝ] ℝ) with hα_def
  have hα : α * (starRingEnd ℂ) α = ((c : ℝ) : ℂ) := by
    have h := congrArg K42RRS2.ρ hent
    rw [map_mul, K42RRS2.ρ_sigmaTensor, K42RRS2.ρ_one_tmul] at h
    exact h
  have hα0 : α ≠ 0 := ((Units.isUnit d).map K42RRS2.ρ).ne_zero
  have hc : (c : ℝ) = Complex.normSq α := by
    have h1 : ((Complex.normSq α : ℝ) : ℂ) = ((c : ℝ) : ℂ) := by rw [← Complex.mul_conj]; exact hα
    exact_mod_cast h1.symm
  have hcpos : 0 < (c : ℝ) := by rw [hc]; exact Complex.normSq_pos.mpr hα0
  refine ⟨hcpos, ?_⟩

  set r : ℝ := Real.sqrt c with hr_def
  have hr0 : 0 < r := Real.sqrt_pos.mpr hcpos
  have hrr : r * r = c := Real.mul_self_sqrt hcpos.le
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  let dr : ℝˣ := Units.mk0 r hr0.ne'
  refine ⟨dr, hrr, ?_⟩
  set lam : ℂ := α / r with hlam_def
  have hlam1 : lam * (starRingEnd ℂ) lam = 1 := by
    rw [hlam_def, map_div₀, Complex.conj_ofReal, div_mul_div_comm, hα, ← Complex.ofReal_mul, hrr]
    exact div_self (by exact_mod_cast hcpos.ne')
  have hlam0 : lam ≠ 0 := fun h => by rw [h, zero_mul] at hlam1; exact zero_ne_one hlam1
  have hαeq : α = r * lam := by rw [hlam_def]; field_simp
  obtain ⟨ω, hω0, hω⟩ : ∃ ω : ℂ, ω ≠ 0 ∧ ω = lam * (starRingEnd ℂ) ω := by
    by_cases h1 : lam = -1
    · exact ⟨Complex.I, Complex.I_ne_zero, by rw [h1, Complex.conj_I]; ring⟩
    · refine ⟨1 + lam, fun h => h1 (by linear_combination h), ?_⟩
      rw [map_add, map_one, mul_add, mul_one, hlam1]; ring
  have hconjω : (starRingEnd ℂ) ω = lam⁻¹ * ω := by
    calc (starRingEnd ℂ) ω = lam⁻¹ * (lam * (starRingEnd ℂ) ω) := by field_simp
      _ = lam⁻¹ * ω := by rw [← hω]
  have hkey : ω⁻¹ * α * (starRingEnd ℂ) ω = r := by
    rw [hconjω, hαeq]; field_simp

  let ωt : (ℂ ⊗[ℝ] ℝ)ˣ := Units.map K42RRS2.ρ.symm.toRingHom.toMonoidHom (Units.mk0 ω hω0)
  have hωt : K42RRS2.ρ ((ωt : (ℂ ⊗[ℝ] ℝ)ˣ) : ℂ ⊗[ℝ] ℝ) = ω := K42RRS2.ρ.apply_symm_apply ω
  have hωt' : K42RRS2.ρ ((ωt⁻¹ : (ℂ ⊗[ℝ] ℝ)ˣ) : ℂ ⊗[ℝ] ℝ) = ω⁻¹ := K42RRS2.ρ.apply_symm_apply ω⁻¹
  set x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) := y * Matrix.GeneralLinearGroup.scalar (Fin 2) ωt with hx_def
  have hx : toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) dr) =
      x⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe x := by
    rw [hx_def, mul_inv_rev, map_mul]
    have hre : (Matrix.GeneralLinearGroup.scalar (Fin 2) ωt)⁻¹ * y⁻¹ * δ *
        (sigmaGL ℝ ℂ ℝ Complex.conjAe y * sigmaGL ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) ωt)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2) ωt)⁻¹ * (y⁻¹ * δ * sigmaGL ℝ ℂ ℝ Complex.conjAe y) *
          sigmaGL ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) ωt) := by group
    rw [hre, hd, K42RRS2.sigmaGL_scalar, ← map_inv, ← map_mul, ← map_mul, K42RRS2.toTensorGL_scalar]
    congr 1
    apply Units.ext
    apply K42RRS2.ρ.injective
    show K42RRS2.ρ ((1 : ℂ) ⊗ₜ[ℝ] (r : ℝ)) =
      K42RRS2.ρ (((ωt⁻¹ : (ℂ ⊗[ℝ] ℝ)ˣ) : ℂ ⊗[ℝ] ℝ) * (d : ℂ ⊗[ℝ] ℝ) *
        sigmaTensor ℝ ℂ ℝ Complex.conjAe ((ωt : (ℂ ⊗[ℝ] ℝ)ˣ) : ℂ ⊗[ℝ] ℝ))
    rw [map_mul, map_mul, K42RRS2.ρ_sigmaTensor, hωt, hωt', K42RRS2.ρ_one_tmul, ← hα_def, hkey]

  letI m1 : MeasurableSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe
      (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) dr))) :=
    twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) dr))
  haveI : BorelSpace (twistedCentralizer ℝ ℂ ℝ Complex.conjAe
      (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) dr))) := ⟨rfl⟩
  set e := K42RRS2.conjEquiv ℝ ℂ ℝ Complex.conjAe δ _ x hx with he_def
  haveI hH1 : Measure.IsHaarMeasure (τ'.map e) := ContinuousMulEquiv.isHaarMeasure_map τ' e
  have hx' : δ = (x⁻¹)⁻¹ * toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) dr) *
      sigmaGL ℝ ℂ ℝ Complex.conjAe x⁻¹ := by
    rw [hx, map_inv]; group
  set e' := K42RRS2.conjEquiv ℝ ℂ ℝ Complex.conjAe _ δ x⁻¹ hx' with he'_def
  have hme : Measurable (e : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ →
      twistedCentralizer ℝ ℂ ℝ Complex.conjAe (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) dr))) :=
    e.continuous.measurable
  have hme' : Measurable (e' : twistedCentralizer ℝ ℂ ℝ Complex.conjAe
      (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) dr)) → twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) :=
    e'.continuous.measurable
  have hback : τ' = (τ'.map e).map e' := by
    rw [Measure.map_map hme' hme]
    have hid : ((e' : _ → _) ∘ (e : _ → _)) = id := funext fun t => Subtype.ext (by
      show (x⁻¹)⁻¹ * (x⁻¹ * (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * x) * x⁻¹ = t
      group)
    rw [hid, Measure.map_id]
  refine ⟨τ'.map e, hH1, ?_, fun φ I => ⟨fun h => ?_, fun h => ?_⟩⟩
  ·
    show Measure.map (fun s : twistedCentralizer ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) dr)) =>
        (1 : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))⁻¹ * (s : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * 1) (τ'.map e) =
      Measure.map (fun t : Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)) => toTensorGL ℝ ℂ ℝ (t : GL (Fin 2) ℝ)) τ
    have hmeas : Measurable (fun s : twistedCentralizer ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) dr)) =>
        (1 : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))⁻¹ * (s : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * 1) :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    rw [Measure.map_map hmeas hme]
    have hfun : ((fun s : twistedCentralizer ℝ ℂ ℝ Complex.conjAe
        (toTensorGL ℝ ℂ ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) dr)) =>
        (1 : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))⁻¹ * (s : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * 1) ∘ (e : _ → _)) =
        fun t : twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ => y⁻¹ * (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * y := by
      funext t
      show (1 : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))⁻¹ * (x⁻¹ * (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) * x) * 1 = y⁻¹ * ↑t * y
      rw [inv_one, one_mul, mul_one, hx_def, mul_inv_rev, ← map_inv]
      calc Matrix.GeneralLinearGroup.scalar (Fin 2) ωt⁻¹ * y⁻¹ * ↑t * (y * Matrix.GeneralLinearGroup.scalar (Fin 2) ωt)
          = Matrix.GeneralLinearGroup.scalar (Fin 2) ωt⁻¹ * (y⁻¹ * ↑t * y) * Matrix.GeneralLinearGroup.scalar (Fin 2) ωt := by group
        _ = (y⁻¹ * ↑t * y) * Matrix.GeneralLinearGroup.scalar (Fin 2) ωt⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) ωt := by
          rw [K42RRS2.scalar_comm]
        _ = y⁻¹ * ↑t * y := by rw [map_inv]; group
    rw [hfun]
    exact hC
  · exact K42RRS2.transport ℝ ℂ ℝ Complex.conjAe μ hμ δ _ x hx τ' (τ'.map e) rfl φ I h
  · exact K42RRS2.transport ℝ ℂ ℝ Complex.conjAe μ hμ _ δ x⁻¹ hx' (τ'.map e) τ' hback φ I h

end S_AutomorphicForm_pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe
end P2MW
export P2MW.S_AutomorphicForm_pos_and_exists_coupled_toTensorGL_scalar_one_iff_of_coupled_scalar_conjAe (solution)
