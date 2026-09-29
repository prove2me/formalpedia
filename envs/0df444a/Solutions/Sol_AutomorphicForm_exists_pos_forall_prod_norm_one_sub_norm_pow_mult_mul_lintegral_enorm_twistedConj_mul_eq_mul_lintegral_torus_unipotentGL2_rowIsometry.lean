-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_prod_norm_one_sub_norm_pow_mult_mul_lintegral_enorm_twistedConj_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/81461006-8f7f-59e0-9101-16061a41ac42

import Theorems.Thm_AutomorphicForm_exists_lintegral_tensor_infiniteAdeleRing_eq_mul_lintegral_diagUnits2_unipotentGL2_archIdentGL_rowIsometry
import Theorems.Thm_AutomorphicForm_lintegral_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry_of_forall_lintegral_toTensorGL_diagUnits2_mul_eq_one
import Theorems.Thm_AutomorphicForm_inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_prod_norm_one_sub_norm_pow_mult_mul_lintegral_comp_sigmaTensor_sub_mul_eq_lintegral
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_prod_norm_one_sub_norm_pow_mult_mul_lintegral_enorm_twistedConj_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace TwHCArch

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
    · first
        | simpa using Units.continuous_val.comp continuous_fst
        | (simpa using (Units.continuous_val.comp continuous_fst :)) | (simpa [Function.comp_def] using Units.continuous_val.comp continuous_fst) | exact Units.continuous_val.comp continuous_fst | (have h__ := Units.continuous_val.comp continuous_fst; (try simp at h__); (try simp); exact h__)
    · simpa using continuous_const
    · simpa using continuous_const
    · first
        | simpa using Units.continuous_val.comp continuous_snd
        | (simpa using (Units.continuous_val.comp continuous_snd :)) | (simpa [Function.comp_def] using Units.continuous_val.comp continuous_snd) | exact Units.continuous_val.comp continuous_snd | (have h__ := Units.continuous_val.comp continuous_snd; (try simp at h__); (try simp); exact h__)
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · first
        | simpa [diagUnits2] using Units.continuous_coe_inv.comp continuous_fst
        | (simpa [diagUnits2] using (Units.continuous_coe_inv.comp continuous_fst :)) | (simpa [Function.comp_def] using Units.continuous_coe_inv.comp continuous_fst) | exact Units.continuous_coe_inv.comp continuous_fst | (have h__ := Units.continuous_coe_inv.comp continuous_fst; (try simp [diagUnits2] at h__); (try simp [diagUnits2]); exact h__)
    · simpa [diagUnits2] using continuous_const
    · simpa [diagUnits2] using continuous_const
    · first
        | simpa [diagUnits2] using Units.continuous_coe_inv.comp continuous_snd
        | (simpa [diagUnits2] using (Units.continuous_coe_inv.comp continuous_snd :)) | (simpa [Function.comp_def] using Units.continuous_coe_inv.comp continuous_snd) | exact Units.continuous_coe_inv.comp continuous_snd | (have h__ := Units.continuous_coe_inv.comp continuous_snd; (try simp [diagUnits2] at h__); (try simp [diagUnits2]); exact h__)

theorem continuous_unipotentGL2 : Continuous (AutomorphicForm.unipotentGL2 : A → GL (Fin 2) A) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa using continuous_const
    · first
        | simpa using continuous_id
        | (simpa using (continuous_id :)) | (simpa [Function.comp_def] using continuous_id) | exact continuous_id | (have h__ := continuous_id; (try simp at h__); (try simp); exact h__)
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

end TwHCArch
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_prod_norm_one_sub_norm_pow_mult_mul_lintegral_enorm_twistedConj_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry.TwHCArch"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_prod_norm_one_sub_norm_pow_mult_mul_lintegral_enorm_twistedConj_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry.TwHCArch"

attribute [local instance] AutomorphicForm.glBorelOf AutomorphicForm.borelSpace_glBorelOf

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
open TwHCArch in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ] (νA : Measure (InfiniteAdeleRing K)ˣ)
    [νA.IsHaarMeasure]
    (ν : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) ν)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (ρ : Measure (L ⊗[K] InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    (κ : @Measure (↥(((⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent L w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing L))).comap (AutomorphicForm.archIdentGL K L) :
        Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ)
    (β : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ) (hβm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] β) (hβ0 : ∀ x, 0 ≤ β x)
    (hβ1 : ∀ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
        ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
            β (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * diagUnits2 a.1 a.2)
          ∂(νA.prod νA) = 1) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
    ∀ (α β' : (L ⊗[K] InfiniteAdeleRing K)ˣ),
      IsUnit (1 - Algebra.norm (InfiniteAdeleRing K) (((β' * α⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))) →
    ∀ (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)), (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) = !![(α : (L ⊗[K] InfiniteAdeleRing K)), 0; 0, (β' : (L ⊗[K] InfiniteAdeleRing K))] →
    ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
          (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ)),
      (∀ g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ,
        ∫ s : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ, g (s : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) ∂τ' =
          ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
            g (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2)) ∂(νA.prod νA)) →
    ∀ (φ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ), Measurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] φ →
    ∀ (w : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ), AutomorphicForm.IsTwistedSectionFnOn K L (InfiniteAdeleRing K) σ δ τ' φ w →
      ENNReal.ofReal (∏ v : InfinitePlace K,
          ‖(1 - Algebra.norm (InfiniteAdeleRing K) (((β' * α⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))) v‖ ^ v.mult) *
        @lintegral _ (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) ν (fun x =>
          ‖φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x)‖ₑ * ENNReal.ofReal (w x)) =
      c * ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, ENNReal.ofReal (β (diagUnits2 a.1 a.2)) *
            ∫⁻ ξ : (L ⊗[K] InfiniteAdeleRing K), @lintegral _ (borel _) κ (fun k =>
              ‖φ ((k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ *
                  diagUnits2 (α * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.1 * a.1⁻¹) (β' * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.2 * a.2⁻¹) *
                  AutomorphicForm.unipotentGL2 ξ * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))‖ₑ) ∂lam
          ∂(ρ.prod ρ) := by
  classical

  have hσlin : ∃ f : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K), ∀ x, f x = AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ x := by
    refine ⟨{ toFun := AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ, map_add' := map_add _, map_smul' := ?_ }, fun x => rfl⟩
    intro a z
    rw [AutomorphicForm.rightActions_smul_eq, AutomorphicForm.rightActions_smul_eq, map_mul]
    congr 1
    simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul]
  have hσTc : Continuous (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ) := by
    obtain ⟨f, hf⟩ := hσlin
    have : Continuous f := IsModuleTopology.continuous_of_linearMap f
    exact this.congr hf
  have hσc : Continuous (AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ) := AutomorphicForm.continuous_glMap _ hσTc

  obtain ⟨c, hc0, hc1, hIw⟩ :=
    AutomorphicForm.exists_lintegral_tensor_infiniteAdeleRing_eq_mul_lintegral_diagUnits2_unipotentGL2_archIdentGL_rowIsometry K L ν hν lam ρ κ hκ
  refine ⟨c, hc0, hc1, ?_⟩
  intro α β' hreg δ hδ τ' hτ' φ hφm w hw

  have hδ' : δ = diagUnits2 α β' := by
    apply Units.ext
    rw [hδ, LanglandsTunnell.CubicInduction.coe_diagUnits2]

  set F : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞ := fun x => ‖φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x)‖ₑ with hFdef
  have hFm : Measurable F := by
    have hc : Continuous fun x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => x⁻¹ * δ * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x :=
      (continuous_inv.mul continuous_const).mul hσc
    exact (hφm.comp hc.measurable).enorm

  have hcoeσ : ∀ g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K), ((AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)).map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ) := fun g => rfl
  have hcoeι : ∀ g : GL (Fin 2) (InfiniteAdeleRing K),
      ((AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
          (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)) := fun g => rfl
  have hσι : ∀ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
      AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2)) =
        AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) := by
    intro p
    apply Units.ext
    rw [hcoeσ, hcoeι]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.map_apply, AutomorphicForm.sigmaTensor,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hcomm : ∀ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
      AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * δ =
        δ * AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) := by
    intro p
    rw [hδ']
    apply Units.ext
    simp only [Units.val_mul, hcoeι, LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, mul_comm]
  have hF : ∀ (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) (x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      F (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * x) = F x := by
    intro p x
    simp only [hFdef]
    congr 2
    rw [map_mul, hσι, mul_inv_rev]
    calc x⁻¹ * (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2))⁻¹ * δ *
          (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x)
        = x⁻¹ * ((AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2))⁻¹ *
            (δ * AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2))) * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x := by
          simp only [mul_assoc]
      _ = x⁻¹ * δ * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x := by rw [← hcomm p]; group

  have hw1 : ∀ x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K), F x ≠ 0 →
      ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
          w (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * x) ∂(νA.prod νA) = 1 := by
    intro x hx
    have hx' : φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x) ≠ 0 := by
      simpa [hFdef] using hx
    have h1 := hw.2.2.2 x hx'
    have h2 := hτ' (fun y => ((w (y * x) : ℝ) : ℂ))
    have e1 := @integral_complex_ofReal _
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ'
      (fun s : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ => w ((s : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * x))
    have e2 := integral_complex_ofReal (μ := νA.prod νA)
      (f := fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
        w (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * x))
    rw [e1, e2] at h2
    have h3 := Complex.ofReal_injective h2
    rw [← h3]
    exact h1

  have hswap :=
    AutomorphicForm.lintegral_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry_of_forall_lintegral_toTensorGL_diagUnits2_mul_eq_one
      K L νA ν lam ρ κ hκ c hIw F hFm hF β hβm hβ0 hβ1 w hw.2.1 hw.1 hw1

  have hnf := fun (a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) (ξ : (L ⊗[K] InfiniteAdeleRing K)) (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =>
    AutomorphicForm.inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul K L (InfiniteAdeleRing K) σ α β' a.1 a.2 ξ k

  have hσalg : ∃ e : (L ⊗[K] InfiniteAdeleRing K) ≃ₐ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K), ∀ x, e x = AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ x := by
    refine ⟨AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.congr σ (AlgEquiv.refl (R := K) (A₁ := InfiniteAdeleRing K))).toRingEquiv) ?_, ?_⟩
    · intro a
      simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    · intro x
      rfl
  have hNσ : ∀ u : (L ⊗[K] InfiniteAdeleRing K)ˣ, Algebra.norm (InfiniteAdeleRing K) ((Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom u : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) =
      Algebra.norm (InfiniteAdeleRing K) (u : (L ⊗[K] InfiniteAdeleRing K)) := by
    intro u
    obtain ⟨e, he⟩ := hσalg
    have hu : ((Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom u : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) = AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (u : (L ⊗[K] InfiniteAdeleRing K)) := rfl
    rw [hu, ← he, Algebra.norm_eq_of_algEquiv]
  have hN : ∀ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
      Algebra.norm (InfiniteAdeleRing K)
          ((((β' * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.2 * a.2⁻¹) * (α * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.1 * a.1⁻¹)⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)) =
        Algebra.norm (InfiniteAdeleRing K) (((β' * α⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) := by
    intro a
    have key : Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)
          ((β' * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.2 * a.2⁻¹) * (α * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.1 * a.1⁻¹)⁻¹) =
        Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) (β' * α⁻¹) := by
      have h1 : Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) (Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.1) =
          Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) a.1 :=
        Units.ext (by rw [Units.coe_map, Units.coe_map]; exact hNσ a.1)
      have h2 : Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) (Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.2) =
          Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) a.2 :=
        Units.ext (by rw [Units.coe_map, Units.coe_map]; exact hNσ a.2)
      simp only [map_mul, map_inv, h1, h2, mul_inv_cancel_right]
    have := congrArg Units.val key
    rwa [Units.coe_map, Units.coe_map] at this

  have hjac := fun (a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) (Ga : (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞) (hGa : Measurable Ga) =>
    AutomorphicForm.prod_norm_one_sub_norm_pow_mult_mul_lintegral_comp_sigmaTensor_sub_mul_eq_lintegral
      K L σ hgen lam ((β' * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.2 * a.2⁻¹) * (α * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.1 * a.1⁻¹)⁻¹) ((hN a).symm ▸ hreg) Ga hGa

  haveI hκi : κ.IsHaarMeasure := hκ
  have hPtop : ENNReal.ofReal (∏ v : InfinitePlace K,
      ‖(1 - Algebra.norm (InfiniteAdeleRing K) (((β' * α⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K))) v‖ ^ v.mult) ≠ ∞ :=
    ENNReal.ofReal_ne_top

  have hGa : ∀ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, Measurable fun η : (L ⊗[K] InfiniteAdeleRing K) =>
      ∫⁻ k : ↥(KcE K L), ‖φ ((k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ *
          diagUnits2 (α * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.1 * a.1⁻¹) (β' * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.2 * a.2⁻¹) *
          AutomorphicForm.unipotentGL2 η * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))‖ₑ ∂κ := by
    intro a
    apply Measurable.lintegral_prod_right
    have h1 : Continuous fun q : (L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L) => ((q.2 : ↥(KcE K L)) : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
      continuous_subtype_val.comp continuous_snd
    have hc : Continuous fun q : (L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L) =>
        ((q.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ * diagUnits2 (α * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.1 * a.1⁻¹) (β' * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.2 * a.2⁻¹) *
          AutomorphicForm.unipotentGL2 q.1 * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (q.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) :=
      ((h1.inv.mul continuous_const).mul (TwHCArch.continuous_unipotentGL2.comp continuous_fst)).mul (hσc.comp h1)
    exact (hφm.comp hc.measurable).enorm

  have hinner : ∀ (a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) (ξ : (L ⊗[K] InfiniteAdeleRing K)) (k : ↥(KcE K L)),
      F (diagUnits2 a.1 a.2 * AutomorphicForm.unipotentGL2 ξ * (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
        ‖φ ((k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ * diagUnits2 (α * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.1 * a.1⁻¹) (β' * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.2 * a.2⁻¹) *
            AutomorphicForm.unipotentGL2 (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ ξ -
              (((β' * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.2 * a.2⁻¹) * (α * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.1 * a.1⁻¹)⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * ξ) *
            AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))‖ₑ := by
    intro a ξ k
    simp only [hFdef]
    rw [hδ', hnf a ξ (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))]
    simp only [mul_assoc]

  have hslice : ∀ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
      ENNReal.ofReal (∏ v : InfinitePlace K,
          ‖(1 - Algebra.norm (InfiniteAdeleRing K) (((β' * α⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K))) v‖ ^ v.mult) *
        ∫⁻ ξ : (L ⊗[K] InfiniteAdeleRing K), ∫⁻ k : ↥(KcE K L), F (diagUnits2 a.1 a.2 * AutomorphicForm.unipotentGL2 ξ * (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) ∂κ ∂lam =
      ∫⁻ ξ : (L ⊗[K] InfiniteAdeleRing K), ∫⁻ k : ↥(KcE K L), ‖φ ((k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ *
          diagUnits2 (α * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.1 * a.1⁻¹) (β' * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a.2 * a.2⁻¹) *
          AutomorphicForm.unipotentGL2 ξ * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))‖ₑ ∂κ ∂lam := by
    intro a
    have hj := hjac a _ (hGa a)
    rw [hN a] at hj
    rw [← hj]
    congr 1
    apply lintegral_congr
    intro ξ
    simp only [hinner]
  rw [hswap, mul_left_comm, ← lintegral_const_mul' _ _ hPtop]
  congr 1
  apply lintegral_congr
  intro a
  rw [mul_left_comm, hslice a]

end S_AutomorphicForm_exists_pos_forall_prod_norm_one_sub_norm_pow_mult_mul_lintegral_enorm_twistedConj_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_prod_norm_one_sub_norm_pow_mult_mul_lintegral_enorm_twistedConj_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry (solution)
