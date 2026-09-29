-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_forall_lintegral_lintegral_enorm_diagUnits2_unipotentGL2_sigmaGL_le_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6a1359b5-659b-57b7-a742-0507f15a6f31

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

namespace P2MW.S_AutomorphicForm_exists_isCompact_forall_lintegral_lintegral_enorm_diagUnits2_unipotentGL2_sigmaGL_le_indicator
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
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isCompact_forall_lintegral_lintegral_enorm_diagUnits2_unipotentGL2_sigmaGL_le_indicator.IwArchL"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isCompact_forall_lintegral_lintegral_enorm_diagUnits2_unipotentGL2_sigmaGL_le_indicator.IwArchL"

attribute [local instance] AutomorphicForm.glBorelOf AutomorphicForm.borelSpace_glBorelOf

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
open IwArchL in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (κ : @Measure (↥(((⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent L w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing L))).comap (AutomorphicForm.archIdentGL K L) :
        Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ)
    (φ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ) (hφs : HasCompactSupport φ) (hφb : ∃ M : ℝ, ∀ g, ‖φ g‖ ≤ M) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∃ Ω : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ), IsCompact Ω ∧
      ∀ d : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
        ∫⁻ ξ : (L ⊗[K] InfiniteAdeleRing K), @lintegral _ (borel _) κ (fun k =>
            ‖φ ((k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ * diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ *
                AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))‖ₑ) ∂lam ≤
          Ω.indicator (fun _ => C) d := by
  classical
  haveI := hκ
  haveI : IsFiniteMeasure κ := CompactSpace.isFiniteMeasure
  obtain ⟨M, hM⟩ := hφb

  have hKc : IsCompact ((KcE K L : Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) :=
    isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace ↥(KcE K L)))
  have hσc : Continuous (AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ) := continuous_sigmaGL K L σ
  have hT : Continuous fun p : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) × (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) × (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =>
      p.1 * p.2.1 * (AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ p.2.2)⁻¹ :=
    (continuous_fst.mul (continuous_fst.comp continuous_snd)).mul
      (hσc.comp (continuous_snd.comp continuous_snd)).inv
  obtain ⟨Ω', hΩ'def⟩ : ∃ Ω' : Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)), Ω' = (fun p : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) × (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) × (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =>
      p.1 * p.2.1 * (AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ p.2.2)⁻¹) ''
        (((KcE K L : Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) ×ˢ (tsupport φ ×ˢ ((KcE K L : Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))) := ⟨_, rfl⟩
  have hΩ' : IsCompact Ω' := hΩ'def ▸ (hKc.prod (hφs.prod hKc)).image hT

  have hc : Continuous fun g : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := Units.continuous_val
  have hci : Continuous fun g : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) => ((g⁻¹ : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := Units.continuous_coe_inv
  obtain ⟨f1, hf1def⟩ : ∃ f1 : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) → (L ⊗[K] InfiniteAdeleRing K) × (L ⊗[K] InfiniteAdeleRing K)ᵐᵒᵖ, f1 = fun g : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =>
      ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 0, MulOpposite.op (((g⁻¹ : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 0)) := ⟨_, rfl⟩
  obtain ⟨f2, hf2def⟩ : ∃ f2 : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) → (L ⊗[K] InfiniteAdeleRing K) × (L ⊗[K] InfiniteAdeleRing K)ᵐᵒᵖ, f2 = fun g : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =>
      ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 1, MulOpposite.op (((g⁻¹ : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 1)) := ⟨_, rfl⟩
  obtain ⟨fN, hfNdef⟩ : ∃ fN : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) → (L ⊗[K] InfiniteAdeleRing K), fN = fun g : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =>
      (((g⁻¹ : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 0) * ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1) := ⟨_, rfl⟩
  have hf1 : Continuous f1 := hf1def ▸ (hc.matrix_elem 0 0).prodMk (MulOpposite.continuous_op.comp (hci.matrix_elem 0 0))
  have hf2 : Continuous f2 := hf2def ▸ (hc.matrix_elem 1 1).prodMk (MulOpposite.continuous_op.comp (hci.matrix_elem 1 1))
  have hfN : Continuous fN := hfNdef ▸ (hci.matrix_elem 0 0).mul (hc.matrix_elem 0 1)
  obtain ⟨Ω₁, hΩ₁def⟩ : ∃ Ω₁ : Set (L ⊗[K] InfiniteAdeleRing K)ˣ, Ω₁ = Units.embedProduct (L ⊗[K] InfiniteAdeleRing K) ⁻¹' (f1 '' Ω') := ⟨_, rfl⟩
  obtain ⟨Ω₂, hΩ₂def⟩ : ∃ Ω₂ : Set (L ⊗[K] InfiniteAdeleRing K)ˣ, Ω₂ = Units.embedProduct (L ⊗[K] InfiniteAdeleRing K) ⁻¹' (f2 '' Ω') := ⟨_, rfl⟩
  obtain ⟨ΩN, hΩNdef⟩ : ∃ ΩN : Set (L ⊗[K] InfiniteAdeleRing K), ΩN = fN '' Ω' := ⟨_, rfl⟩
  have hΩ₁ : IsCompact Ω₁ := hΩ₁def ▸ Units.isClosedEmbedding_embedProduct.isCompact_preimage (hΩ'.image hf1)
  have hΩ₂ : IsCompact Ω₂ := hΩ₂def ▸ Units.isClosedEmbedding_embedProduct.isCompact_preimage (hΩ'.image hf2)
  have hΩN : IsCompact ΩN := hΩNdef ▸ hΩ'.image hfN

  have key : ∀ (d : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) (ξ : (L ⊗[K] InfiniteAdeleRing K)) (k : ↥(KcE K L)),
      φ ((k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))⁻¹ * diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ *
        AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) ≠ 0 →
      d.1 ∈ Ω₁ ∧ d.2 ∈ Ω₂ ∧ ξ ∈ ΩN := by
    intro d ξ k h
    have hmem : diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ ∈ Ω' := by
      rw [hΩ'def]
      refine ⟨((k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))), (k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))⁻¹ * diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ *
        AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))), (k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))), ⟨k.2, subset_tsupport _ h, k.2⟩, ?_⟩
      show (k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) * ((k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))⁻¹ * diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ *
        AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) *
        (AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))⁻¹ = diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ
      group
    have e00 : ((diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 0 = (d.1 : (L ⊗[K] InfiniteAdeleRing K)) := by
      rw [Units.val_mul]; simp [Matrix.mul_apply, Fin.sum_univ_two]
    have e01 : ((diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1 = (d.1 : (L ⊗[K] InfiniteAdeleRing K)) * ξ := by
      rw [Units.val_mul]; simp [Matrix.mul_apply, Fin.sum_univ_two]
    have e11 : ((diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 1 = (d.2 : (L ⊗[K] InfiniteAdeleRing K)) := by
      rw [Units.val_mul]; simp [Matrix.mul_apply, Fin.sum_univ_two]
    have i00 : (((diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ)⁻¹ : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 0 = ((d.1⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) := by
      rw [mul_inv_rev, Units.val_mul]
      change (!![(1 : (L ⊗[K] InfiniteAdeleRing K)), -ξ; 0, 1] * !![((d.1⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)), 0; 0, ((d.2⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))]) 0 0 = _
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have i11 : (((diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ)⁻¹ : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 1 1 = ((d.2⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) := by
      rw [mul_inv_rev, Units.val_mul]
      change (!![(1 : (L ⊗[K] InfiniteAdeleRing K)), -ξ; 0, 1] * !![((d.1⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)), 0; 0, ((d.2⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))]) 1 1 = _
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨?_, ?_, ?_⟩
    · rw [hΩ₁def]
      refine ⟨_, hmem, ?_⟩
      rw [hf1def, Units.embedProduct_apply]
      beta_reduce
      rw [e00, i00]
    · rw [hΩ₂def]
      refine ⟨_, hmem, ?_⟩
      rw [hf2def, Units.embedProduct_apply]
      beta_reduce
      rw [e11, i11]
    · rw [hΩNdef]
      refine ⟨_, hmem, ?_⟩
      rw [hfNdef]
      show (((diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ)⁻¹ : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 0 *
        ((diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) 0 1 = ξ
      rw [i00, e01, Units.inv_mul_cancel_left]

  have hΩNm : MeasurableSet ΩN := hΩN.isClosed.measurableSet
  refine ⟨ENNReal.ofReal M * κ Set.univ * lam ΩN, ?_, Ω₁ ×ˢ Ω₂, hΩ₁.prod hΩ₂, fun d => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top κ _)) hΩN.measure_lt_top.ne
  by_cases hd : d ∈ Ω₁ ×ˢ Ω₂
  · rw [Set.indicator_of_mem hd]
    have hpt : ∀ (ξ : (L ⊗[K] InfiniteAdeleRing K)) (k : ↥(KcE K L)),
        ‖φ ((k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))⁻¹ * diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ *
          AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))‖ₑ ≤
        ΩN.indicator (fun _ => ENNReal.ofReal M) ξ := by
      intro ξ k
      by_cases h : φ ((k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))⁻¹ * diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ *
          AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) = 0
      · rw [h, enorm_zero]; exact zero_le
      · rw [Set.indicator_of_mem (key d ξ k h).2.2, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hM _)
    calc _ ≤ ∫⁻ ξ : (L ⊗[K] InfiniteAdeleRing K), ∫⁻ _k : ↥(KcE K L), ΩN.indicator (fun _ => ENNReal.ofReal M) ξ ∂κ ∂lam :=
          lintegral_mono fun ξ => lintegral_mono fun k => hpt ξ k
      _ = ∫⁻ ξ : (L ⊗[K] InfiniteAdeleRing K), ΩN.indicator (fun _ => ENNReal.ofReal M) ξ * κ Set.univ ∂lam := by
          simp only [lintegral_const]
      _ = ∫⁻ ξ : (L ⊗[K] InfiniteAdeleRing K), ΩN.indicator (fun _ => ENNReal.ofReal M * κ Set.univ) ξ ∂lam := by
          congr 1; funext ξ; by_cases hξ : ξ ∈ ΩN <;> simp [hξ]
      _ = ENNReal.ofReal M * κ Set.univ * lam ΩN := lintegral_indicator_const hΩNm _
  · rw [Set.indicator_of_notMem hd]
    have h0 : ∀ (ξ : (L ⊗[K] InfiniteAdeleRing K)) (k : ↥(KcE K L)),
        φ ((k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))⁻¹ * diagUnits2 d.1 d.2 * AutomorphicForm.unipotentGL2 ξ *
          AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) = 0 := by
      intro ξ k
      by_contra h
      exact hd ⟨(key d ξ k h).1, (key d ξ k h).2.1⟩
    simp [h0]

end S_AutomorphicForm_exists_isCompact_forall_lintegral_lintegral_enorm_diagUnits2_unipotentGL2_sigmaGL_le_indicator
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_forall_lintegral_lintegral_enorm_diagUnits2_unipotentGL2_sigmaGL_le_indicator (solution)
