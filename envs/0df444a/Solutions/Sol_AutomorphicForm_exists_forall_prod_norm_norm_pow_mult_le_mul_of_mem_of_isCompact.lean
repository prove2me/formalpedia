-- Prove2me | solution 1 for AutomorphicForm.exists_forall_prod_norm_norm_pow_mult_le_mul_of_mem_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2f226dc3-e7a4-5465-86bf-6bec3e7db6d0

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_prod_norm_norm_pow_mult_le_mul_of_mem_of_isCompact
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace IwArchL

section GLmaps

variable {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)

theorem map_scalar (u : Aˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : A →* B) u) := by
  apply Units.ext
  ext i j
  change f ((Matrix.scalar (Fin 2) (u : A)) i j) = Matrix.scalar (Fin 2) (f (u : A)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · exact map_zero f

theorem map_diagUnits2 (a b : Aˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (diagUnits2 a b) =
      diagUnits2 (Units.map (f : A →* B) a) (Units.map (f : A →* B) b) := by
  apply Units.ext
  ext i j
  change f ((diagUnits2 a b : GL (Fin 2) A) i j) = (diagUnits2 (Units.map (f : A →* B) a) (Units.map (f : A →* B) b) : GL (Fin 2) B) i j
  fin_cases i <;> fin_cases j <;>
    simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem map_unipotentGL2 (x : A) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (AutomorphicForm.unipotentGL2 x) =
      AutomorphicForm.unipotentGL2 (f x) := by
  apply Units.ext
  ext i j
  change f ((AutomorphicForm.unipotentGL2 x : GL (Fin 2) A) i j) = (AutomorphicForm.unipotentGL2 (f x) : GL (Fin 2) B) i j
  fin_cases i <;> fin_cases j <;> simp [AutomorphicForm.unipotentGL2_coe]

omit f in
theorem scalar_mul_diagUnits2 (u t : Aˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u * diagUnits2 t 1 = diagUnits2 (u * t) u := by
  apply Units.ext
  ext i j
  change (Matrix.scalar (Fin 2) (u : A) * (diagUnits2 t 1 : GL (Fin 2) A)) i j =
    (diagUnits2 (u * t) u : GL (Fin 2) A) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      LanglandsTunnell.CubicInduction.coe_diagUnits2]

end GLmaps

section Cont

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_diagUnits2 : Continuous fun p : Aˣ × Aˣ => diagUnits2 p.1 p.2 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa [Function.comp_def] using Units.continuous_val.comp continuous_fst
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa [Function.comp_def] using Units.continuous_val.comp continuous_snd
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa [diagUnits2, Function.comp_def] using Units.continuous_coe_inv.comp continuous_fst
    · simpa [diagUnits2] using continuous_const
    · simpa [diagUnits2] using continuous_const
    · simpa [diagUnits2, Function.comp_def] using Units.continuous_coe_inv.comp continuous_snd

theorem continuous_unipotentGL2 : Continuous (AutomorphicForm.unipotentGL2 : A → GL (Fin 2) A) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa using continuous_const
    · simpa using continuous_id'
    · simpa using continuous_const
    · simpa using continuous_const
  · have h : (fun x : A => (((AutomorphicForm.unipotentGL2 x)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)) =
        fun x => !![(1 : A), -x; 0, 1] := by
      funext x; rfl
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa using continuous_const
    · simpa using continuous_neg
    · simpa using continuous_const
    · simpa using continuous_const

end Cont

attribute [local instance] AutomorphicForm.glBorelOf AutomorphicForm.borelSpace_glBorelOf

section InstL

variable (L : Type) [Field L] [NumberField L]

abbrev KcL : Subgroup (GL (Fin 2) (InfiniteAdeleRing L)) := (⨅ w : InfinitePlace L, (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent L w) : Subgroup (GL (Fin 2) (InfiniteAdeleRing L)))

scoped instance secondCountable_inf : SecondCountableTopology (InfiniteAdeleRing L) := by
  haveI : ∀ v : InfinitePlace L, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace L) → v.Completion))

@[reducible] scoped instance measKcL : MeasurableSpace ↥(KcL L) := borel _
scoped instance borelKcL : BorelSpace ↥(KcL L) := ⟨rfl⟩
scoped instance compactKcL : CompactSpace ↥(KcL L) := isCompact_iff_compactSpace.mp
  (NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup L).2
@[reducible] scoped instance measInfL : MeasurableSpace (InfiniteAdeleRing L) := borel _
scoped instance borelInfL : BorelSpace (InfiniteAdeleRing L) := ⟨rfl⟩
@[reducible] scoped instance measInfLu : MeasurableSpace (InfiniteAdeleRing L)ˣ := borel _
scoped instance borelInfLu : BorelSpace (InfiniteAdeleRing L)ˣ := ⟨rfl⟩

end InstL

section InstE

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

abbrev KcE : Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := (KcL L).comap (AutomorphicForm.archIdentGL K L)

scoped instance topRing_E : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.isTopologicalRing_tensor K L _
scoped instance topGroup_GE : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := AutomorphicForm.isTopologicalGroup_tensorGL K L _
scoped instance t2_E : T2Space (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.t2Space_tensor K L _
scoped instance lc_E : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.locallyCompactSpace_tensor K L _
scoped instance sc_E : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K) := (AutomorphicForm.archIdentHomeomorph K L).secondCountableTopology
scoped instance sc_Eop : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
scoped instance sc_Eu : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K)ˣ := Units.isInducing_embedProduct.secondCountableTopology
scoped instance lc_Eop : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
scoped instance lc_Eu : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
scoped instance sc_M : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → (L ⊗[K] InfiniteAdeleRing K)))
scoped instance sc_Mop : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
scoped instance sc_GE : SecondCountableTopology (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := Units.isInducing_embedProduct.secondCountableTopology
@[reducible] scoped instance measKcE : MeasurableSpace ↥(KcE K L) := borel _
scoped instance borelKcE : BorelSpace ↥(KcE K L) := ⟨rfl⟩
scoped instance sc_KcE : SecondCountableTopology ↥(KcE K L) := TopologicalSpace.Subtype.secondCountableTopology _

def sigmaLinear (σ : L ≃ₐ[K] L) : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K) :=
  { toFun := AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ
    map_add' := map_add _
    map_smul' := fun a z => by
      simp only [RingHom.id_apply]
      rw [AutomorphicForm.rightActions_smul_eq K L (InfiniteAdeleRing K) a z,
        AutomorphicForm.rightActions_smul_eq K L (InfiniteAdeleRing K) a, map_mul]
      congr 1
      change Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K (InfiniteAdeleRing K)) ((1 : L) ⊗ₜ[K] a) =
        (1 : L) ⊗ₜ[K] a
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] }

theorem continuous_sigmaTensor (σ : L ≃ₐ[K] L) :
    Continuous (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ) :=
  IsModuleTopology.continuous_of_linearMap (sigmaLinear K L σ)

theorem continuous_sigmaGL (σ : L ≃ₐ[K] L) :
    Continuous (AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ) :=
  AutomorphicForm.continuous_glMap _ (continuous_sigmaTensor K L σ)

def sigmaAlgEquiv (σ : L ≃ₐ[K] L) : (L ⊗[K] InfiniteAdeleRing K) ≃ₐ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K) :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.congr σ (AlgEquiv.refl : InfiniteAdeleRing K ≃ₐ[K] InfiniteAdeleRing K)).toRingEquiv)
    (fun a => by
      change Algebra.TensorProduct.map (σ : L →ₐ[K] L)
          ((AlgEquiv.refl : InfiniteAdeleRing K ≃ₐ[K] InfiniteAdeleRing K) : InfiniteAdeleRing K →ₐ[K] InfiniteAdeleRing K)
          ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl)

theorem sigmaAlgEquiv_apply (σ : L ≃ₐ[K] L) (x : (L ⊗[K] InfiniteAdeleRing K)) :
    sigmaAlgEquiv K L σ x = AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ x := rfl

theorem norm_sigmaTensor (σ : L ≃ₐ[K] L) (x : (L ⊗[K] InfiniteAdeleRing K)) :
    Algebra.norm (InfiniteAdeleRing K) (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ x) =
      Algebra.norm (InfiniteAdeleRing K) x := by
  rw [← sigmaAlgEquiv_apply]
  exact Algebra.norm_eq_of_algEquiv (sigmaAlgEquiv K L σ) x

theorem continuous_algebraNorm :
    Continuous (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) → InfiniteAdeleRing K) := by
  classical
  let b := Module.Free.chooseBasis (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  have h : (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) → InfiniteAdeleRing K) =
      fun s => (Algebra.leftMulMatrix b s).det := by
    funext s; exact Algebra.norm_eq_matrix_det b s
  rw [h]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  exact IsModuleTopology.continuous_of_linearMap
    ((Matrix.entryLinearMap (InfiniteAdeleRing K) (InfiniteAdeleRing K) i j).comp
      (Algebra.leftMulMatrix b).toLinearMap)

def eK : ↥(KcE K L) ≃ₜ* ↥(KcL L) :=
  { toFun := fun k => ⟨AutomorphicForm.archIdentGLEquiv K L (k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))), Subgroup.mem_comap.mp k.2⟩
    invFun := fun k => ⟨(AutomorphicForm.archIdentGLEquiv K L).symm (k : (GL (Fin 2) (InfiniteAdeleRing L))), Subgroup.mem_comap.mpr (by
      rw [← AutomorphicForm.archIdentGLEquiv_apply, ContinuousMulEquiv.apply_symm_apply]; exact k.2)⟩
    left_inv := fun k => Subtype.ext ((AutomorphicForm.archIdentGLEquiv K L).symm_apply_apply (k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))
    right_inv := fun k => Subtype.ext ((AutomorphicForm.archIdentGLEquiv K L).apply_symm_apply (k : (GL (Fin 2) (InfiniteAdeleRing L))))
    map_mul' := fun a b => Subtype.ext (by
      show AutomorphicForm.archIdentGLEquiv K L ((a : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) * (b : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) =
        AutomorphicForm.archIdentGLEquiv K L (a : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) * AutomorphicForm.archIdentGLEquiv K L (b : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))
      exact map_mul _ _ _)
    continuous_toFun := ((AutomorphicForm.archIdentGLEquiv K L).continuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := ((AutomorphicForm.archIdentGLEquiv K L).symm.continuous.comp continuous_subtype_val).subtype_mk _ }

theorem eK_apply (k : ↥(KcE K L)) :
    ((eK K L k : ↥(KcL L)) : (GL (Fin 2) (InfiniteAdeleRing L))) = AutomorphicForm.archIdentGLEquiv K L (k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := rfl

scoped instance compactKcE : CompactSpace ↥(KcE K L) := (eK K L).toHomeomorph.symm.compactSpace

end InstE

end IwArchL
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_prod_norm_norm_pow_mult_le_mul_of_mem_of_isCompact.IwArchL"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_prod_norm_norm_pow_mult_le_mul_of_mem_of_isCompact.IwArchL"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
open IwArchL in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L)
    (Ω : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ)) (hΩ : IsCompact Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α β a₁ a₂ : (L ⊗[K] InfiniteAdeleRing K)ˣ),
      (α * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a₁ * a₁⁻¹, β * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a₂ * a₂⁻¹) ∈ Ω →
      (∏ v : InfinitePlace K, ‖(Algebra.norm (InfiniteAdeleRing K) (α : (L ⊗[K] InfiniteAdeleRing K))) v‖ ^ v.mult) ≤
          C * ∏ v : InfinitePlace K, ‖(Algebra.norm (InfiniteAdeleRing K) (β : (L ⊗[K] InfiniteAdeleRing K))) v‖ ^ v.mult ∧
      (∏ v : InfinitePlace K, ‖(Algebra.norm (InfiniteAdeleRing K) (β : (L ⊗[K] InfiniteAdeleRing K))) v‖ ^ v.mult) ≤
          C * ∏ v : InfinitePlace K, ‖(Algebra.norm (InfiniteAdeleRing K) (α : (L ⊗[K] InfiniteAdeleRing K))) v‖ ^ v.mult := by
  classical

  let P : (InfiniteAdeleRing K) → ℝ := fun y => ∏ v : InfinitePlace K, ‖y v‖ ^ v.mult
  let F : (L ⊗[K] InfiniteAdeleRing K)ˣ → ℝ := fun x => P (Algebra.norm (InfiniteAdeleRing K) (x : (L ⊗[K] InfiniteAdeleRing K)))
  have hP : Continuous P :=
    continuous_finsetProd _ fun v _ => ((continuous_apply v).norm).pow _
  have hF : Continuous F := hP.comp ((continuous_algebraNorm K L).comp Units.continuous_val)
  have hFpos : ∀ x : (L ⊗[K] InfiniteAdeleRing K)ˣ, 0 < F x := by
    intro x
    obtain ⟨u, hu⟩ := (Units.isUnit x).map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* (InfiniteAdeleRing K))
    refine Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.mpr ?_) _
    have h1 : ((u : (InfiniteAdeleRing K)) * ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : (InfiniteAdeleRing K))) v = (1 : (InfiniteAdeleRing K)) v := by rw [u.mul_inv]
    have h2 : (u : (InfiniteAdeleRing K)) v * ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : (InfiniteAdeleRing K)) v = 1 := h1
    rw [← hu]
    exact left_ne_zero_of_mul_eq_one h2
  have hG : Continuous fun x : (L ⊗[K] InfiniteAdeleRing K)ˣ => (F x)⁻¹ := hF.inv₀ fun x => (hFpos x).ne'

  have hinv : ∀ x a : (L ⊗[K] InfiniteAdeleRing K)ˣ,
      F (x * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a * a⁻¹) = F x := by
    intro x a
    show P _ = P _
    congr 1
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul, Units.coe_map]
    have hσ : Algebra.norm (InfiniteAdeleRing K) ((AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom (a : (L ⊗[K] InfiniteAdeleRing K))) =
        Algebra.norm (InfiniteAdeleRing K) (a : (L ⊗[K] InfiniteAdeleRing K)) := norm_sigmaTensor K L σ (a : (L ⊗[K] InfiniteAdeleRing K))
    rw [hσ, mul_assoc, ← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one, mul_one]

  obtain ⟨A₁, hA₁⟩ := hΩ.exists_bound_of_continuousOn ((hF.comp continuous_fst).continuousOn)
  obtain ⟨A₂, hA₂⟩ := hΩ.exists_bound_of_continuousOn ((hF.comp continuous_snd).continuousOn)
  obtain ⟨B₁, hB₁⟩ := hΩ.exists_bound_of_continuousOn ((hG.comp continuous_fst).continuousOn)
  obtain ⟨B₂, hB₂⟩ := hΩ.exists_bound_of_continuousOn ((hG.comp continuous_snd).continuousOn)
  have hAB : ∀ {t c : ℝ}, ‖t‖ ≤ c → t ≤ |c| := fun h => (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (h.trans (le_abs_self _)))
  refine ⟨(|A₁| + |A₂|) * (|B₁| + |B₂|), by positivity, ?_⟩
  intro α β a₁ a₂ hmem
  have e1 := hinv α a₁
  have e2 := hinv β a₂
  have h1 : F α ≤ |A₁| + |A₂| := by
    have := hAB (hA₁ _ hmem); simp only [Function.comp] at this; rw [e1] at this
    exact this.trans (le_add_of_nonneg_right (abs_nonneg _))
  have h2 : F β ≤ |A₁| + |A₂| := by
    have := hAB (hA₂ _ hmem); simp only [Function.comp] at this; rw [e2] at this
    exact this.trans (le_add_of_nonneg_left (abs_nonneg _))
  have h3 : (F α)⁻¹ ≤ |B₁| + |B₂| := by
    have := hAB (hB₁ _ hmem); simp only [Function.comp] at this; rw [e1] at this
    exact this.trans (le_add_of_nonneg_right (abs_nonneg _))
  have h4 : (F β)⁻¹ ≤ |B₁| + |B₂| := by
    have := hAB (hB₂ _ hmem); simp only [Function.comp] at this; rw [e2] at this
    exact this.trans (le_add_of_nonneg_left (abs_nonneg _))
  have hA0 : 0 ≤ |A₁| + |A₂| := by positivity
  have key : ∀ {p q : ℝ}, 0 < q → p ≤ |A₁| + |A₂| → q⁻¹ ≤ |B₁| + |B₂| →
      p ≤ (|A₁| + |A₂|) * (|B₁| + |B₂|) * q := by
    intro p q hq hp hq'
    calc p ≤ |A₁| + |A₂| := hp
      _ = (|A₁| + |A₂|) * q⁻¹ * q := by rw [mul_assoc, inv_mul_cancel₀ hq.ne', mul_one]
      _ ≤ (|A₁| + |A₂|) * (|B₁| + |B₂|) * q :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq' hA0) hq.le
  exact ⟨key (hFpos β) h1 h4, key (hFpos α) h2 h3⟩

end S_AutomorphicForm_exists_forall_prod_norm_norm_pow_mult_le_mul_of_mem_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_prod_norm_norm_pow_mult_le_mul_of_mem_of_isCompact (solution)
