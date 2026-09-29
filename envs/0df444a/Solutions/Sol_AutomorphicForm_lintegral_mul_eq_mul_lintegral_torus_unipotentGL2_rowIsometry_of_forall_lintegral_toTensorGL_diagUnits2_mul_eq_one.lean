-- Prove2me | solution 1 for AutomorphicForm.lintegral_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry_of_forall_lintegral_toTensorGL_diagUnits2_mul_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3344f852-729d-577e-a6b2-d4360e83be18

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

namespace P2MW.S_AutomorphicForm_lintegral_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry_of_forall_lintegral_toTensorGL_diagUnits2_mul_eq_one
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

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
p2m_reactivate "P2MW.S_AutomorphicForm_lintegral_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry_of_forall_lintegral_toTensorGL_diagUnits2_mul_eq_one.TwHCArch"

end
p2m_reactivate "P2MW.S_AutomorphicForm_lintegral_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry_of_forall_lintegral_toTensorGL_diagUnits2_mul_eq_one.TwHCArch"

namespace TwP3
variable (K : Type) [Field K] [NumberField K]
scoped instance sc_Kop : SecondCountableTopology (InfiniteAdeleRing K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
scoped instance sc_Ku : SecondCountableTopology (InfiniteAdeleRing K)ˣ := Units.isInducing_embedProduct.secondCountableTopology
scoped instance lc_Kop : LocallyCompactSpace (InfiniteAdeleRing K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
scoped instance lc_Ku : LocallyCompactSpace (InfiniteAdeleRing K)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
end TwP3
p2m_reactivate "P2MW.S_AutomorphicForm_lintegral_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry_of_forall_lintegral_toTensorGL_diagUnits2_mul_eq_one.TwHCArch P2MW.S_AutomorphicForm_lintegral_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry_of_forall_lintegral_toTensorGL_diagUnits2_mul_eq_one.TwP3"

attribute [local instance] AutomorphicForm.glBorelOf AutomorphicForm.borelSpace_glBorelOf

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
open TwHCArch in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ] (νA : Measure (InfiniteAdeleRing K)ˣ)
    [νA.IsHaarMeasure]
    (ν : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (ρ : Measure (L ⊗[K] InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    (κ : @Measure (↥(((⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent L w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing L))).comap (AutomorphicForm.archIdentGL K L) :
        Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ)
    (c : ℝ≥0∞)
    (hIw : ∀ φ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞,
        Measurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] φ →
        @lintegral _ (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) ν φ =
          c * ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, ∫⁻ x : (L ⊗[K] InfiniteAdeleRing K), @lintegral _ (borel _) κ (fun k =>
                φ (diagUnits2 a.1 a.2 * AutomorphicForm.unipotentGL2 x *
                  (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) ∂lam ∂(ρ.prod ρ))
    (F : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞) (hFm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] F)
    (hF : ∀ (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) (x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
        F (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * x) = F x)
    (β : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ) (hβm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] β) (hβ0 : ∀ x, 0 ≤ β x)
    (hβ1 : ∀ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
        ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
            β (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * diagUnits2 a.1 a.2)
          ∂(νA.prod νA) = 1)
    (w : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ) (hwm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] w) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∀ x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K), F x ≠ 0 →
        ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
            w (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * x) ∂(νA.prod νA) = 1) :
    @lintegral _ (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) ν (fun x => F x * ENNReal.ofReal (w x)) =
      c * ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, ENNReal.ofReal (β (diagUnits2 a.1 a.2)) *
            ∫⁻ x : (L ⊗[K] InfiniteAdeleRing K), @lintegral _ (borel _) κ (fun k =>
                F (diagUnits2 a.1 a.2 * AutomorphicForm.unipotentGL2 x * (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) ∂lam
          ∂(ρ.prod ρ) := by
  classical
  haveI hκi : κ.IsHaarMeasure := hκ
  haveI iSCE : SigmaCompactSpace (L ⊗[K] InfiniteAdeleRing K)ˣ := inferInstance
  haveI iSFρ : SigmaFinite ρ := inferInstance
  haveI iLIρ : (ρ.prod ρ).IsMulLeftInvariant := inferInstance
  haveI iSCK : SigmaCompactSpace (InfiniteAdeleRing K)ˣ := inferInstance
  haveI iSFν : SigmaFinite νA := inferInstance
  haveI iHν2 : (νA.prod νA).IsHaarMeasure := inferInstance
  haveI iPMK : TopologicalSpace.PseudoMetrizableSpace (InfiniteAdeleRing K)ˣ := Units.isInducing_embedProduct.pseudoMetrizableSpace
  haveI iRegν2 : (νA.prod νA).Regular := inferInstance
  haveI iInvν2 : (νA.prod νA).IsInvInvariant := inferInstance

  set j : InfiniteAdeleRing K →* (L ⊗[K] InfiniteAdeleRing K) :=
    ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)) : InfiniteAdeleRing K →* (L ⊗[K] InfiniteAdeleRing K)) with hj
  set ιA : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ →* (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ :=
    (Units.map j).prodMap (Units.map j) with hιA
  have hιA_apply : ∀ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
      ιA p = (Units.map j p.1, Units.map j p.2) := fun p => rfl
  have hcoeι : ∀ g : GL (Fin 2) (InfiniteAdeleRing K),
      ((AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
          (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)) := fun g => rfl

  have hdiag : ∀ (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) (a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ),
      AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * diagUnits2 a.1 a.2 =
        diagUnits2 ((ιA p * a).1) ((ιA p * a).2) := by
    intro p a
    apply Units.ext
    simp only [Units.val_mul, hcoeι, LanglandsTunnell.CubicInduction.coe_diagUnits2, hιA_apply, Prod.fst_mul,
      Prod.snd_mul]
    ext i s
    fin_cases i <;> fin_cases s <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, hj]

  have hιc : Continuous ιA := by
    have hjc : Continuous j := by
      have : Continuous (algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)) := continuous_algebraMap _ _
      exact this
    exact ((Units.continuous_map (f := j) hjc).comp continuous_fst).prodMk
      ((Units.continuous_map (f := j) hjc).comp continuous_snd)

  obtain ⟨D, hD⟩ : ∃ D : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ → (L ⊗[K] InfiniteAdeleRing K) → ↥(TwHCArch.KcE K L) → GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
      D = fun (a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) (x : (L ⊗[K] InfiniteAdeleRing K)) (k : ↥(TwHCArch.KcE K L)) =>
        diagUnits2 a.1 a.2 * AutomorphicForm.unipotentGL2 x * (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := ⟨_, rfl⟩
  have hDc : Continuous fun q : ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) × ((L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L)) => D q.1 q.2.1 q.2.2 := by
    simp only [hD]
    exact ((TwHCArch.continuous_diagUnits2.comp continuous_fst).mul
      (TwHCArch.continuous_unipotentGL2.comp (continuous_fst.comp continuous_snd))).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  have hDa : ∀ y : (L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L), Continuous fun a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ => D a y.1 y.2 := fun y =>
    hDc.comp (continuous_id.prodMk continuous_const)
  have hDy : ∀ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, Continuous fun y : (L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L) => D a y.1 y.2 := fun a =>
    hDc.comp (continuous_const.prodMk continuous_id)
  have hwm' : Measurable fun g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => ENNReal.ofReal (w g) := ENNReal.measurable_ofReal.comp hwm
  have hbm' : Measurable fun a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ => ENNReal.ofReal (β (diagUnits2 a.1 a.2)) :=
    ENNReal.measurable_ofReal.comp (hβm.comp TwHCArch.continuous_diagUnits2.measurable)

  have hDι : ∀ (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) (a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) (y : (L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L)),
      AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * D a y.1 y.2 = D (ιA p * a) y.1 y.2 := by
    intro p a y
    simp only [hD]
    rw [← hdiag p a]
    simp only [mul_assoc]

  have hB1 : ∀ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, ∫⁻ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, ENNReal.ofReal (β (diagUnits2 (ιA p * a).1 (ιA p * a).2)) ∂(νA.prod νA) = 1 := by
    intro a
    have h := hβ1 a
    simp_rw [hdiag] at h
    have hint : Integrable (fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => β (diagUnits2 (ιA p * a).1 (ιA p * a).2)) (νA.prod νA) :=
      Integrable.of_integral_ne_zero (by rw [h]; exact one_ne_zero)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun p => hβ0 _), h,
      ENNReal.ofReal_one]
  have hW1 : ∀ (a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) (y : (L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L)), F (D a y.1 y.2) ≠ 0 →
      ∫⁻ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, ENNReal.ofReal (w (D (ιA p * a) y.1 y.2)) ∂(νA.prod νA) = 1 := by
    intro a y ha
    have h := hw1 (D a y.1 y.2) ha
    simp_rw [hDι] at h
    have hint : Integrable (fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => w (D (ιA p * a) y.1 y.2)) (νA.prod νA) :=
      Integrable.of_integral_ne_zero (by rw [h]; exact one_ne_zero)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun p => hw0 _), h,
      ENNReal.ofReal_one]
  have hFι : ∀ (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) (a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) (y : (L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L)), F (D (ιA p * a) y.1 y.2) = F (D a y.1 y.2) := by
    intro p a y
    rw [← hDι, hF]

  have hslice : ∀ y : (L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L),
      ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, F (D a y.1 y.2) * ENNReal.ofReal (w (D a y.1 y.2)) ∂(ρ.prod ρ) =
        ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, F (D a y.1 y.2) * ENNReal.ofReal (β (diagUnits2 a.1 a.2)) ∂(ρ.prod ρ) := by
    intro y
    have hΦm : Measurable fun a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ => F (D a y.1 y.2) := hFm.comp (hDa y).measurable
    have hWm : Measurable fun a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ => ENNReal.ofReal (w (D a y.1 y.2)) := hwm'.comp (hDa y).measurable

    have hmix : Measurable fun q : ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) × ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) =>
        F (D q.1 y.1 y.2) * ENNReal.ofReal (w (D q.1 y.1 y.2)) *
          ENNReal.ofReal (β (diagUnits2 (ιA q.2 * q.1).1 (ιA q.2 * q.1).2)) := by
      have h3 : Measurable fun q : ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) × ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) => ιA q.2 * q.1 :=
        ((hιc.comp continuous_snd).mul continuous_fst).measurable
      exact ((hΦm.comp measurable_fst).mul (hWm.comp measurable_fst)).mul (hbm'.comp h3)
    have hmix2 : Measurable fun q : ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) × ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) =>
        F (D q.1 y.1 y.2) * ENNReal.ofReal (w (D ((ιA q.2)⁻¹ * q.1) y.1 y.2)) *
          ENNReal.ofReal (β (diagUnits2 q.1.1 q.1.2)) := by
      have h3 : Measurable fun q : ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) × ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) => (ιA q.2)⁻¹ * q.1 :=
        ((hιc.comp continuous_snd).inv.mul continuous_fst).measurable
      exact ((hΦm.comp measurable_fst).mul (hwm'.comp ((hDa y).measurable.comp h3))).mul (hbm'.comp measurable_fst)
    calc ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, F (D a y.1 y.2) * ENNReal.ofReal (w (D a y.1 y.2)) ∂(ρ.prod ρ)
        = ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, F (D a y.1 y.2) * ENNReal.ofReal (w (D a y.1 y.2)) *
            ∫⁻ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, ENNReal.ofReal (β (diagUnits2 (ιA p * a).1 (ιA p * a).2)) ∂(νA.prod νA) ∂(ρ.prod ρ) := by
          simp_rw [hB1, mul_one]
      _ = ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, ∫⁻ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, F (D a y.1 y.2) * ENNReal.ofReal (w (D a y.1 y.2)) *
            ENNReal.ofReal (β (diagUnits2 (ιA p * a).1 (ιA p * a).2)) ∂(νA.prod νA) ∂(ρ.prod ρ) := by
          apply lintegral_congr; intro a
          rw [lintegral_const_mul]
          exact hbm'.comp ((hιc.mul continuous_const).measurable)
      _ = ∫⁻ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, F (D a y.1 y.2) * ENNReal.ofReal (w (D a y.1 y.2)) *
            ENNReal.ofReal (β (diagUnits2 (ιA p * a).1 (ιA p * a).2)) ∂(ρ.prod ρ) ∂(νA.prod νA) :=
          lintegral_lintegral_swap hmix.aemeasurable
      _ = ∫⁻ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, F (D a y.1 y.2) * ENNReal.ofReal (w (D ((ιA p)⁻¹ * a) y.1 y.2)) *
            ENNReal.ofReal (β (diagUnits2 a.1 a.2)) ∂(ρ.prod ρ) ∂(νA.prod νA) := by
          apply lintegral_congr; intro p
          rw [← lintegral_mul_left_eq_self _ (ιA p)⁻¹]
          apply lintegral_congr; intro a
          rw [mul_inv_cancel_left, ← map_inv, hFι]
      _ = ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, ∫⁻ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, F (D a y.1 y.2) * ENNReal.ofReal (w (D ((ιA p)⁻¹ * a) y.1 y.2)) *
            ENNReal.ofReal (β (diagUnits2 a.1 a.2)) ∂(νA.prod νA) ∂(ρ.prod ρ) :=
          (lintegral_lintegral_swap hmix2.aemeasurable).symm
      _ = ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, F (D a y.1 y.2) * ENNReal.ofReal (β (diagUnits2 a.1 a.2)) *
            ∫⁻ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, ENNReal.ofReal (w (D (ιA p * a) y.1 y.2)) ∂(νA.prod νA) ∂(ρ.prod ρ) := by
          apply lintegral_congr; intro a
          have hm : Measurable fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => ENNReal.ofReal (w (D ((ιA p)⁻¹ * a) y.1 y.2)) :=
            hwm'.comp ((hDa y).measurable.comp ((hιc.inv.mul continuous_const).measurable))
          conv_rhs => rw [← lintegral_inv_eq_self]
          simp only [map_inv]
          rw [← lintegral_const_mul _ hm]
          apply lintegral_congr; intro p
          rw [mul_right_comm]
      _ = ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, F (D a y.1 y.2) * ENNReal.ofReal (β (diagUnits2 a.1 a.2)) ∂(ρ.prod ρ) := by
          apply lintegral_congr; intro a
          by_cases ha : F (D a y.1 y.2) = 0
          · simp [ha]
          · rw [hW1 a y ha, mul_one]

  have hFw : Measurable fun g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => F g * ENNReal.ofReal (w g) := hFm.mul hwm'
  rw [hIw _ hFw]
  congr 1
  have hD' : ∀ (a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) (x : (L ⊗[K] InfiniteAdeleRing K)) (k : ↥(TwHCArch.KcE K L)),
      diagUnits2 a.1 a.2 * AutomorphicForm.unipotentGL2 x * (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) = D a x k := by
    intro a x k; rw [hD]
  simp only [hD']
  have hprod : ∀ (a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) (h : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞), Measurable h →
      ∫⁻ x : (L ⊗[K] InfiniteAdeleRing K), ∫⁻ k : ↥(TwHCArch.KcE K L), h (D a x k) ∂κ ∂lam =
        ∫⁻ y : (L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L), h (D a y.1 y.2) ∂(lam.prod κ) := by
    intro a h hh
    have hm : Measurable (fun y : (L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L) => h (D a y.1 y.2)) := hh.comp (hDy a).measurable
    rw [lintegral_prod _ hm.aemeasurable]
  have hL : ∀ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, ∫⁻ x : (L ⊗[K] InfiniteAdeleRing K), ∫⁻ k : ↥(TwHCArch.KcE K L),
      F (D a x k) * ENNReal.ofReal (w (D a x k)) ∂κ ∂lam =
        ∫⁻ y : (L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L), F (D a y.1 y.2) * ENNReal.ofReal (w (D a y.1 y.2)) ∂(lam.prod κ) :=
    fun a => hprod a _ hFw
  have hR : ∀ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, ∫⁻ x : (L ⊗[K] InfiniteAdeleRing K), ∫⁻ k : ↥(TwHCArch.KcE K L), F (D a x k) ∂κ ∂lam =
      ∫⁻ y : (L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L), F (D a y.1 y.2) ∂(lam.prod κ) :=
    fun a => hprod a _ hFm
  have hm1 : Measurable fun q : ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) × ((L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L)) =>
      F (D q.1 q.2.1 q.2.2) * ENNReal.ofReal (w (D q.1 q.2.1 q.2.2)) := hFw.comp hDc.measurable
  have hm2 : Measurable fun q : ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) × ((L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L)) =>
      F (D q.1 q.2.1 q.2.2) * ENNReal.ofReal (β (diagUnits2 q.1.1 q.1.2)) :=
    (hFm.comp hDc.measurable).mul (hbm'.comp measurable_fst)
  calc ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, ∫⁻ x : (L ⊗[K] InfiniteAdeleRing K), ∫⁻ k : ↥(TwHCArch.KcE K L),
          F (D a x k) * ENNReal.ofReal (w (D a x k)) ∂κ ∂lam ∂(ρ.prod ρ)
      = ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, ∫⁻ y : (L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L), F (D a y.1 y.2) * ENNReal.ofReal (w (D a y.1 y.2)) ∂(lam.prod κ) ∂(ρ.prod ρ) := by
        apply lintegral_congr; intro a; exact hL a
    _ = ∫⁻ y : (L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L), ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, F (D a y.1 y.2) * ENNReal.ofReal (w (D a y.1 y.2)) ∂(ρ.prod ρ) ∂(lam.prod κ) :=
        lintegral_lintegral_swap hm1.aemeasurable
    _ = ∫⁻ y : (L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L), ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, F (D a y.1 y.2) * ENNReal.ofReal (β (diagUnits2 a.1 a.2)) ∂(ρ.prod ρ) ∂(lam.prod κ) := by
        apply lintegral_congr; intro y; exact hslice y
    _ = ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, ∫⁻ y : (L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L), F (D a y.1 y.2) * ENNReal.ofReal (β (diagUnits2 a.1 a.2)) ∂(lam.prod κ) ∂(ρ.prod ρ) :=
        (lintegral_lintegral_swap hm2.aemeasurable).symm
    _ = ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, ENNReal.ofReal (β (diagUnits2 a.1 a.2)) * ∫⁻ y : (L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L), F (D a y.1 y.2) ∂(lam.prod κ) ∂(ρ.prod ρ) := by
        apply lintegral_congr; intro a
        have hm : Measurable (fun y : (L ⊗[K] InfiniteAdeleRing K) × ↥(TwHCArch.KcE K L) => F (D a y.1 y.2)) := hFm.comp (hDy a).measurable
        rw [← lintegral_const_mul _ hm]
        apply lintegral_congr; intro y
        rw [mul_comm]
    _ = ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, ENNReal.ofReal (β (diagUnits2 a.1 a.2)) *
          ∫⁻ x : (L ⊗[K] InfiniteAdeleRing K), ∫⁻ k : ↥(TwHCArch.KcE K L), F (D a x k) ∂κ ∂lam ∂(ρ.prod ρ) := by
        apply lintegral_congr; intro a; rw [hR a]

end S_AutomorphicForm_lintegral_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry_of_forall_lintegral_toTensorGL_diagUnits2_mul_eq_one
end P2MW
export P2MW.S_AutomorphicForm_lintegral_mul_eq_mul_lintegral_torus_unipotentGL2_rowIsometry_of_forall_lintegral_toTensorGL_diagUnits2_mul_eq_one (solution)
