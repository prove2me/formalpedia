-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_twistedOrbital_archHaarL_diagUnits2_eq_mul_integral_ker_norm_integral_integral_and_twistedWeighted_eq_of_coupled
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/64ff433a-e04d-520a-b15f-4a274676f144

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_eq_smul_map_diagUnits2_mul_unipotentGL2_mul_and_integral_eq_of_isHaarMeasure_tensor_infiniteAdeleRing
import Theorems.Thm_AutomorphicForm_integrable_archIdentGL_inv_mul_diagUnits2_mul_unipotentGL2_sigmaTensor_sub_mul_sigmaGL_mul_of_isArchTestFactor_of_isRegularSemisimple
import Theorems.Thm_AutomorphicForm_inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_twistedOrbital_archHaarL_diagUnits2_eq_mul_integral_ker_norm_integral_integral_and_twistedWeighted_eq_of_coupled
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace TwA3

section Cont

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_diagUnits2 : Continuous fun p : Aˣ × Aˣ => diagUnits2 p.1 p.2 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · exact Units.continuous_val.comp continuous_fst
    · simpa using continuous_const
    · simpa using continuous_const
    · exact Units.continuous_val.comp continuous_snd
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · first | exact Units.continuous_coe_inv.comp continuous_fst | simpa [diagUnits2, Function.comp_def] using Units.continuous_coe_inv.comp continuous_fst
    · simpa [diagUnits2] using continuous_const
    · simpa [diagUnits2] using continuous_const
    · first | exact Units.continuous_coe_inv.comp continuous_snd | simpa [diagUnits2, Function.comp_def] using Units.continuous_coe_inv.comp continuous_snd

theorem continuous_unipotentGL2 : Continuous (AutomorphicForm.unipotentGL2 : A → GL (Fin 2) A) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · simpa using continuous_const
    · exact continuous_id
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

omit [TopologicalSpace A] [IsTopologicalRing A] in
theorem scalar_mul_diagUnits2 (u t : Aˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u * diagUnits2 t 1 = diagUnits2 (u * t) u := by
  apply Units.ext
  ext i j
  change (Matrix.scalar (Fin 2) (u : A) * (diagUnits2 t 1 : GL (Fin 2) A)) i j =
    (diagUnits2 (u * t) u : GL (Fin 2) A) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      LanglandsTunnell.CubicInduction.coe_diagUnits2]

omit [TopologicalSpace A] [IsTopologicalRing A] in
theorem diagUnits2_mul (a b c d : Aˣ) : diagUnits2 a b * diagUnits2 c d = diagUnits2 (a * c) (b * d) := by
  apply Units.ext
  ext i j
  change ((diagUnits2 a b : GL (Fin 2) A) * (diagUnits2 c d : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j =
    (diagUnits2 (a * c) (b * d) : GL (Fin 2) A) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, LanglandsTunnell.CubicInduction.coe_diagUnits2]

end Cont

attribute [local instance] AutomorphicForm.glBorelOf AutomorphicForm.borelSpace_glBorelOf

section InstL

variable (L : Type) [Field L] [NumberField L]

scoped instance secondCountable_inf : SecondCountableTopology (InfiniteAdeleRing L) := by
  haveI : ∀ v : InfinitePlace L, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace L) → v.Completion))

scoped instance secondCountable_infUnits : SecondCountableTopology (InfiniteAdeleRing L)ˣ := by
  haveI : SecondCountableTopology (InfiniteAdeleRing L)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance locallyCompact_infUnits : LocallyCompactSpace (InfiniteAdeleRing L)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end InstL

section InstE

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

abbrev KcE : Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
  ⨅ w : InfinitePlace L,
    (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
      ((archComponent L w).comp (AutomorphicForm.archIdentGL K L))

theorem KcE_eq_comap :
    KcE K L = (⨅ w : InfinitePlace L,
      (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent L w) :
        Subgroup (GL (Fin 2) (InfiniteAdeleRing L))).comap (AutomorphicForm.archIdentGL K L) := by
  rw [KcE, Subgroup.comap_iInf]
  simp_rw [Subgroup.comap_comap]

scoped instance topRing_E : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.isTopologicalRing_tensor K L _
scoped instance topGroup_GE : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := AutomorphicForm.isTopologicalGroup_tensorGL K L _
scoped instance t2_E : T2Space (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.t2Space_tensor K L _
scoped instance t2_GE : T2Space (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := AutomorphicForm.t2Space_tensorGL K L _
scoped instance lc_E : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.locallyCompactSpace_tensor K L _
scoped instance lc_GE : LocallyCompactSpace (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := AutomorphicForm.locallyCompactSpace_tensorGL K L _
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

theorem continuous_sigmaTensor (σ : L ≃ₐ[K] L) :
    Continuous (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ) := by
  have hσlin : ∃ f : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K),
      ∀ x, f x = AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ x := by
    refine ⟨{ toFun := AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ, map_add' := map_add _, map_smul' := ?_ }, fun x => rfl⟩
    intro a z
    rw [AutomorphicForm.rightActions_smul_eq, AutomorphicForm.rightActions_smul_eq, map_mul]
    congr 1
    simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul]
  obtain ⟨f, hf⟩ := hσlin
  have : Continuous f := IsModuleTopology.continuous_of_linearMap f
  exact this.congr hf

theorem continuous_sigmaGL (σ : L ≃ₐ[K] L) :
    Continuous (AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ) :=
  AutomorphicForm.continuous_glMap _ (continuous_sigmaTensor K L σ)

theorem continuous_archIdentGL : Continuous (AutomorphicForm.archIdentGL K L) :=
  (AutomorphicForm.archIdentGLEquiv K L).continuous

theorem isCompact_KcE : IsCompact ((KcE K L : Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) :
    Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := by
  rw [KcE_eq_comap K L, Subgroup.coe_comap]
  have hK := (NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup L).2
  have : (⇑(AutomorphicForm.archIdentGL K L) : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → GL (Fin 2) (InfiniteAdeleRing L)) =
      ⇑(AutomorphicForm.archIdentGLEquiv K L) := rfl
  rw [this]
  exact (AutomorphicForm.archIdentGLEquiv K L).toHomeomorph.isCompact_preimage.mpr hK

scoped instance compact_KcE : CompactSpace ↥(KcE K L) := isCompact_iff_compactSpace.mp (isCompact_KcE K L)

theorem continuous_includeRight :
    Continuous (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K) := by
  have h : (⇑(Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) =
      fun a : InfiniteAdeleRing K => a • (1 : L ⊗[K] InfiniteAdeleRing K) := by
    funext a
    rw [AutomorphicForm.rightActions_smul_eq, mul_one]
    rfl
  rw [h]
  exact continuous_id.fun_smul continuous_const

theorem continuous_toTensorGL : Continuous (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)) :=
  AutomorphicForm.continuous_glMap _ (continuous_includeRight K L)

end InstE

section ArchTest
variable (F : Type) [Field F] [NumberField F]

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion in
theorem continuous_ringEquiv_mixedSpace : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_archEntries : Continuous (AutomorphicForm.archEntries F : GL (Fin 2) (InfiniteAdeleRing F) → _) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_ringEquiv_mixedSpace F).comp (Units.continuous_val.matrix_elem i j)

namespace IsArchTestFactor
open scoped Classical in
private theorem _root_.TwA3.IsArchTestFactor.continuous {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : AutomorphicForm.IsArchTestFactor F fa) :
    Continuous fa := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, -⟩ := h
  have : fa = Φ ∘ AutomorphicForm.archEntries F := funext hfa
  rw [this]
  exact hΦ.continuous.comp (continuous_archEntries F)

end IsArchTestFactor
p2m_export "TwA3" "IsArchTestFactor.continuous"
end ArchTest

section SectionKill

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L)
  [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
  (ρ : Measure (InfiniteAdeleRing K)ˣ)

theorem section_kill (γ : GL (Fin 2) (InfiniteAdeleRing K)) (δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))))
    (hτ : ∀ g : GL (Fin 2) (InfiniteAdeleRing K) → ℂ,
      ∫ x, g (x : GL (Fin 2) (InfiniteAdeleRing K)) ∂τ =
        ∫ r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, g (diagUnits2 r.1 r.2) ∂(ρ.prod ρ))
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ))
    (hc : AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ γ δ 1 τ τ')
    (s : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ) (hsm : Measurable s)
    (x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    ∫ t, s ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * x) ∂τ' =
      ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
        s (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * x) ∂(ρ.prod ρ) := by
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := ⟨rfl⟩
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) := ⟨rfl⟩
  have hsx : Measurable fun g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) => s (g * x) :=
    hsm.comp (measurable_id.mul_const x)

  have hc' : Measure.map (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ =>
        (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τ' =
      Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
        AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (t : GL (Fin 2) (InfiniteAdeleRing K))) τ := by
    have h1 : (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ =>
        (1 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ * (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * 1) =
        fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ =>
          (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := by
      funext t; simp
    have := hc
    unfold AutomorphicForm.Coupled at this
    rw [h1] at this
    exact this
  have hval : Measurable fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ =>
      (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := continuous_subtype_val.measurable
  have htT : Measurable fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
      AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (t : GL (Fin 2) (InfiniteAdeleRing K)) :=
    ((continuous_toTensorGL K L).comp continuous_subtype_val).measurable
  calc ∫ t, s ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * x) ∂τ'
      = ∫ g, s (g * x) ∂(Measure.map (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ =>
          (t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τ') :=
        (integral_map hval.aemeasurable hsx.aestronglyMeasurable).symm
    _ = ∫ g, s (g * x) ∂(Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (t : GL (Fin 2) (InfiniteAdeleRing K))) τ) := by rw [hc']
    _ = ∫ t, s (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (t : GL (Fin 2) (InfiniteAdeleRing K)) * x) ∂τ :=
        integral_map htT.aemeasurable hsx.aestronglyMeasurable
    _ = _ := by
        have h := hτ (fun y => ((s (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) y * x) : ℝ) : ℂ))
        rw [integral_complex_ofReal, integral_complex_ofReal] at h
        exact_mod_cast h

end SectionKill

section Torus

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L)
  [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
  (ρ : Measure (InfiniteAdeleRing K)ˣ) [SFinite ρ]
  [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
  (ρE : Measure (L ⊗[K] InfiniteAdeleRing K)ˣ) [SFinite ρE]
  (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) :
      (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) [SFinite θ]

def A1Lint (C2 : ℝ≥0∞) : Prop :=
  ∀ (Θ : (L ⊗[K] InfiniteAdeleRing K)ˣ → ℝ≥0∞), Measurable Θ →
    ∀ (G : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) :
        (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker → ℝ≥0∞), Measurable G →
      (∀ (s : (L ⊗[K] InfiniteAdeleRing K)ˣ)
          (v : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker),
          ((v : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) :
              (L ⊗[K] InfiniteAdeleRing K)ˣ) =
            s⁻¹ * Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)) s →
          ∫⁻ p, Θ (s * Units.map
              ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom.toMonoidHom) p) ∂ρ =
            G v) →
      ∫⁻ s, Θ s ∂ρE = C2 * ∫⁻ v, G v ∂θ

theorem torus_master (C2 : ℝ≥0∞) (hA1 : A1Lint K L σ ρ ρE θ C2)
    (F : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ → ℝ≥0∞) (hF : Measurable F)
    (ξ₀ : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
        ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker → ℝ≥0∞)
    (hξ : Measurable ξ₀)
    (hfib : ∀ (s₁ s₂ : (L ⊗[K] InfiniteAdeleRing K)ˣ)
        (v₁ v₂ : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker),
        ((v₁ : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) :
            (L ⊗[K] InfiniteAdeleRing K)ˣ) = s₁⁻¹ * Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)) s₁ →
        ((v₂ : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) :
            (L ⊗[K] InfiniteAdeleRing K)ˣ) = s₂⁻¹ * Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)) s₂ →
        ∫⁻ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
            F (s₁ * Units.map ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom.toMonoidHom) p.1,
               s₂ * Units.map ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom.toMonoidHom) p.2)
          ∂(ρ.prod ρ) = ξ₀ (v₁, v₂)) :
    ∫⁻ a, F a ∂(ρE.prod ρE) = C2 ^ 2 * ∫⁻ v, ξ₀ v ∂(θ.prod θ) := by
  set ιU : (InfiniteAdeleRing K)ˣ →* (L ⊗[K] InfiniteAdeleRing K)ˣ :=
    Units.map ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom.toMonoidHom) with hιU
  have hιc : Continuous ιU := by
    rw [hιU]; exact Continuous.units_map _ (continuous_includeRight K L)
  have hιm : Measurable ιU := hιc.measurable
  rw [lintegral_prod _ hF.aemeasurable]
  have hΘ₁m : Measurable fun a₁ : (L ⊗[K] InfiniteAdeleRing K)ˣ => ∫⁻ a₂, F (a₁, a₂) ∂ρE := hF.lintegral_prod_right'
  have hG₁m : Measurable fun v₁ : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker =>
      C2 * ∫⁻ v₂, ξ₀ (v₁, v₂) ∂θ := hξ.lintegral_prod_right'.const_mul _
  rw [hA1 _ hΘ₁m _ hG₁m ?_, lintegral_const_mul _ hξ.lintegral_prod_right', ← lintegral_prod _ hξ.aemeasurable,
    ← mul_assoc, sq]
  intro s₁ v₁ hv₁

  have hF₁m : Measurable fun q : (InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ => F (s₁ * ιU q.1, q.2) :=
    hF.comp ((measurable_const.mul (hιm.comp measurable_fst)).prodMk measurable_snd)
  change ∫⁻ p₁, ∫⁻ a₂, F (s₁ * ιU p₁, a₂) ∂ρE ∂ρ = C2 * ∫⁻ v₂, ξ₀ (v₁, v₂) ∂θ
  rw [lintegral_lintegral_swap hF₁m.aemeasurable]
  have hΘ₂m : Measurable fun a₂ : (L ⊗[K] InfiniteAdeleRing K)ˣ => ∫⁻ p₁, F (s₁ * ιU p₁, a₂) ∂ρ :=
    (hF.comp ((measurable_const.mul (hιm.comp measurable_snd)).prodMk measurable_fst)).lintegral_prod_right'
  rw [hA1 _ hΘ₂m (fun v₂ => ξ₀ (v₁, v₂)) (hξ.comp (measurable_const.prodMk measurable_id)) ?_]
  intro s₂ v₂ hv₂
  have hF₂m : Measurable fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => F (s₁ * ιU p.1, s₂ * ιU p.2) :=
    hF.comp ((measurable_const.mul (hιm.comp measurable_fst)).prodMk (measurable_const.mul (hιm.comp measurable_snd)))
  change ∫⁻ p₂, ∫⁻ p₁, F (s₁ * ιU p₁, s₂ * ιU p₂) ∂ρ ∂ρ = ξ₀ (v₁, v₂)
  rw [← lintegral_prod_symm _ hF₂m.aemeasurable]
  exact hfib s₁ s₂ v₁ v₂ hv₁ hv₂

end Torus

section Master

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L)
  [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
  (ρ : Measure (InfiniteAdeleRing K)ˣ) [SFinite ρ]
  [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
  (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [SFinite lam]
  [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
  (ρE : Measure (L ⊗[K] InfiniteAdeleRing K)ˣ) [SFinite ρE]
  (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) :
      (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) [SFinite θ]
  (κ : Measure ↥(KcE K L)) [SFinite κ]

def Psi (p : ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) ×
    ((L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L))) : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) :=
  diagUnits2 p.1.1 p.1.2 * AutomorphicForm.unipotentGL2 p.2.1 * (p.2.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))

theorem continuous_Psi : Continuous (Psi K L) :=
  ((continuous_diagUnits2.comp continuous_fst).mul
    (continuous_unipotentGL2.comp (continuous_fst.comp continuous_snd))).mul
    (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))

abbrev iotaU : (InfiniteAdeleRing K)ˣ →* (L ⊗[K] InfiniteAdeleRing K)ˣ :=
  Units.map ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom.toMonoidHom)

abbrev sigmaU : (L ⊗[K] InfiniteAdeleRing K)ˣ →* (L ⊗[K] InfiniteAdeleRing K)ˣ :=
  Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ))

theorem sigmaU_iotaU (p : (InfiniteAdeleRing K)ˣ) : sigmaU K L σ (iotaU K L p) = iotaU K L p := by
  apply Units.ext
  show AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)) (p : InfiniteAdeleRing K)) =
    (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)) (p : InfiniteAdeleRing K)
  simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem inv_mul_sigmaU_mul_iotaU (s : (L ⊗[K] InfiniteAdeleRing K)ˣ) (p : (InfiniteAdeleRing K)ˣ) :
    (s * iotaU K L p)⁻¹ * sigmaU K L σ (s * iotaU K L p) = s⁻¹ * sigmaU K L σ s := by
  rw [map_mul, sigmaU_iotaU, mul_inv_rev, mul_comm (sigmaU K L σ s) (iotaU K L p), ← mul_assoc,
    mul_assoc (iotaU K L p)⁻¹, mul_comm s⁻¹ (iotaU K L p), ← mul_assoc (iotaU K L p)⁻¹, inv_mul_cancel, one_mul]

theorem toTensorGL_diagUnits2 (p₁ p₂ : (InfiniteAdeleRing K)ˣ) :
    AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p₁ p₂) = diagUnits2 (iotaU K L p₁) (iotaU K L p₂) := by
  apply Units.ext
  ext i j
  change (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom
      ((diagUnits2 p₁ p₂ : GL (Fin 2) (InfiniteAdeleRing K)) i j) =
    (diagUnits2 (iotaU K L p₁) (iotaU K L p₂) : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) i j
  fin_cases i <;> fin_cases j <;>
    simp [LanglandsTunnell.CubicInduction.coe_diagUnits2]

theorem toTensorGL_diagUnits2_mul_Psi (p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)
    (a₁ a₂ : (L ⊗[K] InfiniteAdeleRing K)ˣ) (q : (L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L)) :
    AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * Psi K L ((a₁, a₂), q) =
      Psi K L ((a₁ * iotaU K L p.1, a₂ * iotaU K L p.2), q) := by
  simp only [Psi, toTensorGL_diagUnits2, ← mul_assoc, diagUnits2_mul, mul_comm (iotaU K L _)]

theorem lint_master (C1 C2 : ℝ≥0∞)
    (ν : Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))
    (hν : ν = C1 • Measure.map (Psi K L) ((ρE.prod ρE).prod (lam.prod κ)))
    (hA1 : A1Lint K L σ ρ ρE θ C2)
    (Ξ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞) (hΞ : Measurable Ξ)
    (ξ : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) ×
        ((L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L)) → ℝ≥0∞) (hξm : Measurable ξ)
    (hcompat : ∀ (a₁ a₂ : (L ⊗[K] InfiniteAdeleRing K)ˣ) (q : (L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L))
        (v₁ v₂ : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker),
        ((v₁ : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) :
            (L ⊗[K] InfiniteAdeleRing K)ˣ) = a₁⁻¹ * sigmaU K L σ a₁ →
        ((v₂ : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) :
            (L ⊗[K] InfiniteAdeleRing K)ˣ) = a₂⁻¹ * sigmaU K L σ a₂ →
        Ξ (Psi K L ((a₁, a₂), q)) = ξ ((v₁, v₂), q))
    (s : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ) (hsm : Measurable s)
    (hkill : ∀ x, Ξ x ≠ 0 →
        ∫⁻ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
          ENNReal.ofReal (s (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * x)) ∂(ρ.prod ρ) = 1) :
    ∫⁻ x, Ξ x * ENNReal.ofReal (s x) ∂ν = C1 * C2 ^ 2 * ∫⁻ z, ξ z ∂((θ.prod θ).prod (lam.prod κ)) := by
  have hΨm : Measurable (Psi K L) := (continuous_Psi K L).measurable
  have hIm : Measurable fun x => Ξ x * ENNReal.ofReal (s x) := hΞ.mul (ENNReal.measurable_ofReal.comp hsm)
  have hImΨ : Measurable fun a => Ξ (Psi K L a) * ENNReal.ofReal (s (Psi K L a)) := hIm.comp hΨm
  rw [hν, lintegral_smul_measure, smul_eq_mul, lintegral_map hIm hΨm, lintegral_prod_symm _ hImΨ.aemeasurable,
    lintegral_prod_symm _ hξm.aemeasurable, mul_assoc, ← lintegral_const_mul _ hξm.lintegral_prod_left']
  congr 1
  refine lintegral_congr fun q => ?_

  refine torus_master K L σ ρ ρE θ C2 hA1 (fun aa => Ξ (Psi K L (aa, q)) * ENNReal.ofReal (s (Psi K L (aa, q))))
    (hIm.comp (hΨm.comp (measurable_id.prodMk measurable_const))) (fun u => ξ (u, q))
    (hξm.comp (measurable_id.prodMk measurable_const)) ?_
  intro s₁ s₂ v₁ v₂ hv₁ hv₂
  have hc : ∀ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
      Ξ (Psi K L ((s₁ * iotaU K L p.1, s₂ * iotaU K L p.2), q)) = ξ ((v₁, v₂), q) := fun p =>
    hcompat _ _ q v₁ v₂ (by rw [inv_mul_sigmaU_mul_iotaU]; exact hv₁) (by rw [inv_mul_sigmaU_mul_iotaU]; exact hv₂)
  simp_rw [show ∀ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
      Ξ (Psi K L ((s₁ * iotaU K L p.1, s₂ * iotaU K L p.2), q)) * ENNReal.ofReal (s (Psi K L ((s₁ * iotaU K L p.1, s₂ * iotaU K L p.2), q))) =
        ξ ((v₁, v₂), q) * ENNReal.ofReal (s (Psi K L ((s₁ * iotaU K L p.1, s₂ * iotaU K L p.2), q))) from fun p => by rw [hc p]]
  have hsm' : Measurable fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
      ENNReal.ofReal (s (Psi K L ((s₁ * iotaU K L p.1, s₂ * iotaU K L p.2), q))) := by
    refine ENNReal.measurable_ofReal.comp (hsm.comp (hΨm.comp ?_))
    have hι : Measurable (iotaU K L) := (Continuous.units_map _ (continuous_includeRight K L)).measurable
    exact (((measurable_const.mul (hι.comp measurable_fst)).prodMk
      (measurable_const.mul (hι.comp measurable_snd))).prodMk measurable_const)
  rw [lintegral_const_mul _ hsm']
  by_cases h0 : ξ ((v₁, v₂), q) = 0
  · rw [h0, zero_mul]
  · have hx : Ξ (Psi K L ((s₁, s₂), q)) ≠ 0 := by rwa [hcompat s₁ s₂ q v₁ v₂ hv₁ hv₂]
    have := hkill _ hx
    simp_rw [toTensorGL_diagUnits2_mul_Psi] at this
    rw [this, mul_one]

end Master

section Signed

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L)
  [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
  (ρ : Measure (InfiniteAdeleRing K)ˣ) [SFinite ρ]
  [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
  (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [SFinite lam]
  [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
  (ρE : Measure (L ⊗[K] InfiniteAdeleRing K)ˣ) [SFinite ρE]
  (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) :
      (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) [SFinite θ]
  (κ : Measure ↥(KcE K L)) [SFinite κ]

theorem signed_master (C1 C2 : ℝ≥0∞) (hC1 : C1 ≠ ∞) (hC2 : C2 ≠ ∞)
    (ν : Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))
    (hν : ν = C1 • Measure.map (Psi K L) ((ρE.prod ρE).prod (lam.prod κ)))
    (hA1 : A1Lint K L σ ρ ρE θ C2)
    (Ξc : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ) (hΞc : Measurable Ξc)
    (ξc : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) ×
        ((L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L)) → ℂ) (hξcm : Measurable ξc)
    (hξci : Integrable ξc ((θ.prod θ).prod (lam.prod κ)))
    (hcompat : ∀ (a₁ a₂ : (L ⊗[K] InfiniteAdeleRing K)ˣ) (q : (L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L))
        (v₁ v₂ : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker),
        ((v₁ : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) :
            (L ⊗[K] InfiniteAdeleRing K)ˣ) = a₁⁻¹ * sigmaU K L σ a₁ →
        ((v₂ : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) :
            (L ⊗[K] InfiniteAdeleRing K)ˣ) = a₂⁻¹ * sigmaU K L σ a₂ →
        Ξc (Psi K L ((a₁, a₂), q)) = ξc ((v₁, v₂), q))
    (s : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ) (hsm : Measurable s) (hs0 : ∀ x, 0 ≤ s x)
    (hkill : ∀ x, Ξc x ≠ 0 →
        ∫⁻ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
          ENNReal.ofReal (s (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * x)) ∂(ρ.prod ρ) = 1) :
    Integrable (fun x => Ξc x * (s x : ℂ)) ν ∧
    ∫ x, Ξc x * (s x : ℂ) ∂ν = ((C1 * C2 ^ 2).toReal : ℂ) * ∫ z, ξc z ∂((θ.prod θ).prod (lam.prod κ)) := by
  set Pm := (θ.prod θ).prod (lam.prod κ) with hPm
  set C := C1 * C2 ^ 2 with hC
  have hCtop : C ≠ ∞ := ENNReal.mul_ne_top hC1 (ENNReal.pow_ne_top hC2)

  have part : ∀ (P : ℂ → ℝ≥0∞), Measurable P → P 0 = 0 →
      ∫⁻ x, P (Ξc x) * ENNReal.ofReal (s x) ∂ν = C * ∫⁻ z, P (ξc z) ∂Pm := by
    intro P hP hP0
    refine lint_master K L σ ρ lam ρE θ κ C1 C2 ν hν hA1 (fun x => P (Ξc x)) (hP.comp hΞc) (fun z => P (ξc z))
      (hP.comp hξcm) (fun a₁ a₂ q v₁ v₂ h₁ h₂ => by
        show P (Ξc (Psi K L ((a₁, a₂), q))) = P (ξc ((v₁, v₂), q))
        rw [hcompat a₁ a₂ q v₁ v₂ h₁ h₂]) s hsm (fun x hx => hkill x ?_)
    intro h0
    exact hx (show P (Ξc x) = 0 by rw [h0, hP0])

  have henorm : ∀ x, ‖Ξc x * (s x : ℂ)‖ₑ = ‖Ξc x‖ₑ * ENNReal.ofReal (s x) := by
    intro x
    rw [enorm_mul]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hs0 x)]

  have hmeas : Measurable fun x => Ξc x * (s x : ℂ) := hΞc.mul (Complex.measurable_ofReal.comp hsm)
  have hint : Integrable (fun x => Ξc x * (s x : ℂ)) ν := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    show ∫⁻ x, ‖Ξc x * (s x : ℂ)‖ₑ ∂ν < ∞
    simp_rw [henorm]
    rw [part (fun z => ‖z‖ₑ) measurable_enorm enorm_zero]
    exact ENNReal.mul_lt_top hCtop.lt_top hξci.2
  refine ⟨hint, ?_⟩

  have hre_int : Integrable (fun x => (Ξc x).re * s x) ν := by
    have := hint.re
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.mul_re]
  have him_int : Integrable (fun x => (Ξc x).im * s x) ν := by
    have := hint.im
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.mul_im]
  have hξre : Integrable (fun z => (ξc z).re) Pm := hξci.re
  have hξim : Integrable (fun z => (ξc z).im) Pm := hξci.im

  have hP1 := part (fun z => ENNReal.ofReal z.re) (ENNReal.measurable_ofReal.comp Complex.measurable_re) (by simp)
  have hP2 := part (fun z => ENNReal.ofReal (-z.re)) (ENNReal.measurable_ofReal.comp Complex.measurable_re.neg) (by simp)
  have hP3 := part (fun z => ENNReal.ofReal z.im) (ENNReal.measurable_ofReal.comp Complex.measurable_im) (by simp)
  have hP4 := part (fun z => ENNReal.ofReal (-z.im)) (ENNReal.measurable_ofReal.comp Complex.measurable_im.neg) (by simp)
  have hmul : ∀ (r : ℝ) (x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      ENNReal.ofReal (r * s x) = ENNReal.ofReal r * ENNReal.ofReal (s x) := fun r x => ENNReal.ofReal_mul' (hs0 x)
  apply Complex.ext
  ·
    have h1 : (∫ x, Ξc x * (s x : ℂ) ∂ν).re = ∫ x, (Ξc x).re * s x ∂ν := by
      rw [← RCLike.re_to_complex, ← integral_re hint]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [Complex.mul_re]
    have h2 : ((C.toReal : ℂ) * ∫ z, ξc z ∂Pm).re = C.toReal * ∫ z, (ξc z).re ∂Pm := by
      rw [Complex.re_ofReal_mul, ← RCLike.re_to_complex, ← integral_re hξci]
      simp only [RCLike.re_to_complex]
    rw [h1, h2, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hre_int,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hξre]
    simp_rw [← neg_mul, hmul]
    have e1 : (C * ∫⁻ z, (fun z => ENNReal.ofReal z.re) (ξc z) ∂Pm).toReal =
        C.toReal * (∫⁻ z, ENNReal.ofReal (ξc z).re ∂Pm).toReal := ENNReal.toReal_mul
    have e2 : (C * ∫⁻ z, (fun z => ENNReal.ofReal (-z.re)) (ξc z) ∂Pm).toReal =
        C.toReal * (∫⁻ z, ENNReal.ofReal (-(ξc z).re) ∂Pm).toReal := ENNReal.toReal_mul
    rw [hP1, hP2, e1, e2, mul_sub]
  ·
    have h1 : (∫ x, Ξc x * (s x : ℂ) ∂ν).im = ∫ x, (Ξc x).im * s x ∂ν := by
      rw [← RCLike.im_to_complex, ← integral_im hint]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [Complex.mul_im]
    have h2 : ((C.toReal : ℂ) * ∫ z, ξc z ∂Pm).im = C.toReal * ∫ z, (ξc z).im ∂Pm := by
      rw [Complex.im_ofReal_mul, ← RCLike.im_to_complex, ← integral_im hξci]
      simp only [RCLike.im_to_complex]
    rw [h1, h2, integral_eq_lintegral_pos_part_sub_lintegral_neg_part him_int,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hξim]
    simp_rw [← neg_mul, hmul]
    have e1 : (C * ∫⁻ z, (fun z => ENNReal.ofReal z.im) (ξc z) ∂Pm).toReal =
        C.toReal * (∫⁻ z, ENNReal.ofReal (ξc z).im ∂Pm).toReal := ENNReal.toReal_mul
    have e2 : (C * ∫⁻ z, (fun z => ENNReal.ofReal (-z.im)) (ξc z) ∂Pm).toReal =
        C.toReal * (∫⁻ z, ENNReal.ofReal (-(ξc z).im) ∂Pm).toReal := ENNReal.toReal_mul
    rw [hP3, hP4, e1, e2, mul_sub]

end Signed

section NormOne
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

theorem continuous_algebraNorm :
    Continuous (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) → InfiniteAdeleRing K) := by
  classical
  let b := Module.Free.chooseBasis (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
  have h : (⇑(Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)) =
      fun x => (Algebra.leftMulMatrix b x).det := funext fun x => Algebra.norm_eq_matrix_det b x
  rw [h]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  have hl : Continuous (b.coord i) := IsModuleTopology.continuous_of_linearMap _
  have hm : Continuous fun x : L ⊗[K] InfiniteAdeleRing K => x * b j := continuous_id.mul continuous_const
  refine (hl.comp hm).congr fun x => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.coord_apply]

theorem isClosed_normOne :
    IsClosed ((Units.map (Algebra.norm (InfiniteAdeleRing K) :
      (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker : Set (L ⊗[K] InfiniteAdeleRing K)ˣ) := by
  rw [MonoidHom.coe_ker]
  exact isClosed_singleton.preimage (Continuous.units_map _ (continuous_algebraNorm K L))

scoped instance lc_normOne : LocallyCompactSpace ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) :
      (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker :=
  (isClosed_normOne K L).isClosedEmbedding_subtypeVal.locallyCompactSpace

scoped instance sc_normOne : SecondCountableTopology ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) :
      (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker :=
  TopologicalSpace.Subtype.secondCountableTopology _

end NormOne

end TwA3
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_twistedOrbital_archHaarL_diagUnits2_eq_mul_integral_ker_norm_integral_integral_and_twistedWeighted_eq_of_coupled.TwA3"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_twistedOrbital_archHaarL_diagUnits2_eq_mul_integral_ker_norm_integral_integral_and_twistedWeighted_eq_of_coupled.TwA3"

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel
attribute [local instance] AutomorphicForm.glBorelOf AutomorphicForm.borelSpace_glBorelOf

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 16000000 in
open TwA3 in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) :
        (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker)
    [θ.IsHaarMeasure]
    (κ : @Measure (↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ), AutomorphicForm.IsArchTestFactor L φa →
      ∀ (ω : L ⊗[K] InfiniteAdeleRing K → ℝ), Continuous ω →
      ∀ (W : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ), Continuous W →
        (∀ (u' t' : (L ⊗[K] InfiniteAdeleRing K)ˣ) (y : L ⊗[K] InfiniteAdeleRing K)
            (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
            k ∈ (⨅ w : InfinitePlace L,
              (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
                ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
                Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) →
            W (Matrix.GeneralLinearGroup.scalar (Fin 2) u' * diagUnits2 t' 1 * AutomorphicForm.unipotentGL2 y * k) =
              ω y) →
      ∀ (a t : (InfiniteAdeleRing K)ˣ), AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t)) →
      ∀ (τ : Measure (Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
        (∀ g : GL (Fin 2) (InfiniteAdeleRing K) → ℂ,
            ∫ x, g (x : GL (Fin 2) (InfiniteAdeleRing K)) ∂τ =
              ∫ r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, g (diagUnits2 r.1 r.2) ∂(ρ.prod ρ)) →
      ∀ α β : (L ⊗[K] InfiniteAdeleRing K)ˣ,
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)) →
      ∀ (τ' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (diagUnits2 α β))),
        τ'.IsHaarMeasure →
        AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (diagUnits2 a (a * t)) (diagUnits2 α β) 1 τ τ' →
      (∀ I' : ℂ, AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (AutomorphicForm.archHaarL K L)
          (diagUnits2 α β) τ' (φa ∘ AutomorphicForm.archIdentGL K L) I' →
        I' = (c : ℂ) *
          ∫ u, ∫ y, @integral _ ℂ _ _ (borel _) κ (fun k =>
              φa (AutomorphicForm.archIdentGL K L
                ((k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ *
                  (diagUnits2 (α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) *
                    AutomorphicForm.unipotentGL2
                      (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y -
                        (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) :
                          (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) * y)) *
                  AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))) ∂lam
            ∂(θ.prod θ)) ∧
      (∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.archHaarL K L) W (diagUnits2 α β) τ' (φa ∘ AutomorphicForm.archIdentGL K L) J' →
        J' = (c : ℂ) *
          ∫ u, ∫ y, (@integral _ ℂ _ _ (borel _) κ (fun k =>
              φa (AutomorphicForm.archIdentGL K L
                ((k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ *
                  (diagUnits2 (α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) *
                    AutomorphicForm.unipotentGL2
                      (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y -
                        (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) :
                          (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) * y)) *
                  AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))))) *
              ((ω y : ℝ) : ℂ) ∂lam
            ∂(θ.prod θ)) := by
  classical

  haveI : κ.IsHaarMeasure := hκ
  haveI : IsFiniteMeasure κ := CompactSpace.isFiniteMeasure
  haveI : SigmaFinite κ := IsFiniteMeasure.toSigmaFinite κ
  haveI : SigmaFinite θ := by infer_instance
  haveI : SigmaFinite ρ := by infer_instance
  set ρE : Measure (L ⊗[K] InfiniteAdeleRing K)ˣ := Measure.haar with hρE
  haveI : ρE.IsHaarMeasure := by rw [hρE]; infer_instance
  have hν : (AutomorphicForm.archHaarL K L).IsHaarMeasure := by
    delta AutomorphicForm.archHaarL
    infer_instance

  obtain ⟨c₁, hc₁0, hc₁t, hνeq, -⟩ :=
    AutomorphicForm.exists_eq_smul_map_diagUnits2_mul_unipotentGL2_mul_and_integral_eq_of_isHaarMeasure_tensor_infiniteAdeleRing
      K L (AutomorphicForm.archHaarL K L) hν lam ρE κ hκ
  obtain ⟨c₂, hc₂, hA1l, -⟩ :=
    AutomorphicForm.exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq
      K L σ hgen hdeg ρ ρE θ
  have hA1 : A1Lint K L σ ρ ρE θ (ENNReal.ofReal c₂) := fun Θ hΘ G hG h => hA1l Θ hΘ G hG h
  have hC0 : c₁ * ENNReal.ofReal c₂ ^ 2 ≠ 0 :=
    mul_ne_zero hc₁0 (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hc₂).ne')
  have hCt : c₁ * ENNReal.ofReal c₂ ^ 2 ≠ ⊤ := ENNReal.mul_ne_top hc₁t (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  refine ⟨(c₁ * ENNReal.ofReal c₂ ^ 2).toReal, ENNReal.toReal_pos hC0 hCt, ?_⟩
  intro φa hφa ω hω W hWc hW a t hreg τ hτ α β hδ τ' hτ' hcoup

  have hφc : Continuous (φa ∘ AutomorphicForm.archIdentGL K L) :=
    (IsArchTestFactor.continuous L hφa).comp (continuous_archIdentGL K L)
  have htwc : Continuous fun x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
      x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x :=
    (continuous_inv.mul continuous_const).mul (continuous_sigmaGL K L σ)
  have hΞm : Measurable fun x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
      φa (AutomorphicForm.archIdentGL K L (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x)) :=
    (hφc.comp htwc).measurable

  set ξ0 : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
        ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) ×
      ((L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L)) → ℂ := fun p =>
    φa (AutomorphicForm.archIdentGL K L
      ((p.2.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ *
        (diagUnits2 (α * (p.1.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) (β * (p.1.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) *
          AutomorphicForm.unipotentGL2
            (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ p.2.1 -
              (((α * (p.1.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (p.1.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) :
                (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) * p.2.1)) *
        AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (p.2.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) with hξ0
  have hξ0c : Continuous ξ0 := by
    have hk : Continuous fun p : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) ×
        ((L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L)) => (p.2.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    have hu1 : Continuous fun p : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) ×
        ((L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L)) => α * (p.1.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) :=
      continuous_const.mul (continuous_subtype_val.comp (continuous_fst.comp continuous_fst))
    have hu2 : Continuous fun p : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) ×
        ((L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L)) => β * (p.1.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) :=
      continuous_const.mul (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
    have hy : Continuous fun p : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) ×
        ((L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L)) => p.2.1 := continuous_fst.comp continuous_snd
    have hdiag := continuous_diagUnits2.comp (hu1.prodMk hu2)
    have hr : Continuous fun p : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) ×
        ((L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L)) =>
        (((α * (p.1.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (p.1.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) :
          (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) :=
      Units.continuous_val.comp (hu1.inv.mul hu2)
    have hbig : Continuous fun p : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) ×
        ((L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L)) =>
        (p.2.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ *
          (diagUnits2 (α * (p.1.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) (β * (p.1.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) *
            AutomorphicForm.unipotentGL2
              (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ p.2.1 -
                (((α * (p.1.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (p.1.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) :
                  (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) * p.2.1)) *
          AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (p.2.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := by
      apply Continuous.mul
      apply Continuous.mul
      · exact hk.inv
      · apply Continuous.mul
        · exact hdiag
        · apply continuous_unipotentGL2.comp
          exact ((continuous_sigmaTensor K L σ).comp hy).sub (hr.mul hy)
      · exact (continuous_sigmaGL K L σ).comp hk
    rw [hξ0]
    exact hφc.comp hbig
  have hξ0m : Measurable ξ0 := hξ0c.measurable

  have hcompat0 : ∀ (a₁ a₂ : (L ⊗[K] InfiniteAdeleRing K)ˣ) (q : (L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L))
      (v₁ v₂ : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker),
      ((v₁ : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) :
          (L ⊗[K] InfiniteAdeleRing K)ˣ) = a₁⁻¹ * sigmaU K L σ a₁ →
      ((v₂ : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) :
          (L ⊗[K] InfiniteAdeleRing K)ˣ) = a₂⁻¹ * sigmaU K L σ a₂ →
      φa (AutomorphicForm.archIdentGL K L ((Psi K L ((a₁, a₂), q))⁻¹ * diagUnits2 α β *
        AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (Psi K L ((a₁, a₂), q)))) = ξ0 ((v₁, v₂), q) := by
    intro a₁ a₂ q v₁ v₂ h1 h2
    simp only [Psi, hξ0]
    rw [AutomorphicForm.inv_mul_diagUnits2_mul_sigmaGL_of_diagUnits2_mul_unipotentGL2_mul K L (InfiniteAdeleRing K) σ α β a₁ a₂
      q.1 (q.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))]
    have e1 : α * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a₁ * a₁⁻¹ =
        α * (v₁ : (L ⊗[K] InfiniteAdeleRing K)ˣ) := by
      rw [h1]
      show α * sigmaU K L σ a₁ * a₁⁻¹ = α * (a₁⁻¹ * sigmaU K L σ a₁)
      rw [mul_comm a₁⁻¹, mul_assoc]
    have e2 : β * Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a₂ * a₂⁻¹ =
        β * (v₂ : (L ⊗[K] InfiniteAdeleRing K)ˣ) := by
      rw [h2]
      show β * sigmaU K L σ a₂ * a₂⁻¹ = β * (a₂⁻¹ * sigmaU K L σ a₂)
      rw [mul_comm a₂⁻¹, mul_assoc]
    rw [e1, e2, mul_comm (β * (v₂ : (L ⊗[K] InfiniteAdeleRing K)ˣ)) (α * (v₁ : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹]

  have hkill_of : ∀ s : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ,
      AutomorphicForm.IsTwistedSectionFnOn K L (InfiniteAdeleRing K) σ (diagUnits2 α β) τ' (φa ∘ AutomorphicForm.archIdentGL K L) s →
      ∀ x, φa (AutomorphicForm.archIdentGL K L (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x)) ≠ 0 →
        ∫⁻ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
          ENNReal.ofReal (s (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * x)) ∂(ρ.prod ρ) = 1 := by
    intro s hs x hx
    obtain ⟨hs0, hsm, -, hsec⟩ := hs
    have h1 : ∫ t, s ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) * x) ∂τ' = 1 := hsec x hx
    rw [section_kill K L σ ρ (diagUnits2 a (a * t)) (diagUnits2 α β) τ hτ τ' hcoup s hsm x] at h1
    have hint : Integrable (fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
        s (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * x)) (ρ.prod ρ) := by
      by_contra h
      rw [integral_undef h] at h1
      exact zero_ne_one h1
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun p => hs0 _), h1, ENNReal.ofReal_one]

  have hTW := AutomorphicForm.integrable_archIdentGL_inv_mul_diagUnits2_mul_unipotentGL2_sigmaTensor_sub_mul_sigmaGL_mul_of_isArchTestFactor_of_isRegularSemisimple
    K L σ hgen hdeg lam θ κ hκ φa hφa ω hω a t hreg α β hδ
  have hTW1 := AutomorphicForm.integrable_archIdentGL_inv_mul_diagUnits2_mul_unipotentGL2_sigmaTensor_sub_mul_sigmaGL_mul_of_isArchTestFactor_of_isRegularSemisimple
    K L σ hgen hdeg lam θ κ hκ φa hφa (fun _ => (1 : ℝ)) continuous_const a t hreg α β hδ
  have hξ0i : Integrable ξ0 ((θ.prod θ).prod (lam.prod κ)) := by
    refine hTW1.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [hξ0, Complex.ofReal_one, mul_one]
  refine ⟨fun I' hI' => ?_, fun J' hJ' => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := hI'
    obtain ⟨-, heq⟩ := signed_master K L σ ρ lam ρE θ κ c₁ (ENNReal.ofReal c₂) hc₁t ENNReal.ofReal_ne_top
      (AutomorphicForm.archHaarL K L) hνeq hA1
      (fun x => φa (AutomorphicForm.archIdentGL K L (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x)))
      hΞm ξ0 hξ0m hξ0i hcompat0 s hs.2.1 hs.1 (hkill_of s hs)
    change ∫ x, φa (AutomorphicForm.archIdentGL K L (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x)) *
      (s x : ℂ) ∂(AutomorphicForm.archHaarL K L) = _
    rw [heq, integral_prod _ hξ0i]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hξ0i.prod_right_ae] with u hu
    rw [integral_prod _ hu]
  · obtain ⟨s, hs, rfl⟩ := hJ'
    have hWΨ : ∀ (a₁ a₂ : (L ⊗[K] InfiniteAdeleRing K)ˣ) (q : (L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L)),
        W (Psi K L ((a₁, a₂), q)) = ω q.1 := by
      intro a₁ a₂ q
      have hd : diagUnits2 a₁ a₂ = Matrix.GeneralLinearGroup.scalar (Fin 2) a₂ * diagUnits2 (a₁ * a₂⁻¹) 1 := by
        rw [scalar_mul_diagUnits2, mul_comm a₂ (a₁ * a₂⁻¹), inv_mul_cancel_right]
      simp only [Psi]
      rw [hd]
      exact hW a₂ (a₁ * a₂⁻¹) q.1 _ q.2.2
    have hΞWm : Measurable fun x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
        φa (AutomorphicForm.archIdentGL K L (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x)) * (W x : ℂ) :=
      hΞm.mul (Complex.measurable_ofReal.comp hWc.measurable)
    have hξWc : Continuous fun p : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) ×
        ((L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L)) => ξ0 p * ((ω p.2.1 : ℝ) : ℂ) :=
      hξ0c.mul (Complex.continuous_ofReal.comp (hω.comp (continuous_fst.comp continuous_snd)))
    have hξWi : Integrable (fun p : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) ×
        ((L ⊗[K] InfiniteAdeleRing K) × ↥(KcE K L)) => ξ0 p * ((ω p.2.1 : ℝ) : ℂ)) ((θ.prod θ).prod (lam.prod κ)) := by
      refine hTW.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [hξ0]
    obtain ⟨-, heq⟩ := signed_master K L σ ρ lam ρE θ κ c₁ (ENNReal.ofReal c₂) hc₁t ENNReal.ofReal_ne_top
      (AutomorphicForm.archHaarL K L) hνeq hA1
      (fun x => φa (AutomorphicForm.archIdentGL K L (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x)) * (W x : ℂ))
      hΞWm (fun p => ξ0 p * ((ω p.2.1 : ℝ) : ℂ)) hξWc.measurable hξWi
      (fun a₁ a₂ q v₁ v₂ h1 h2 => by
        show φa (AutomorphicForm.archIdentGL K L ((Psi K L ((a₁, a₂), q))⁻¹ * diagUnits2 α β *
            AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (Psi K L ((a₁, a₂), q)))) * (W (Psi K L ((a₁, a₂), q)) : ℂ) =
          ξ0 ((v₁, v₂), q) * ((ω q.1 : ℝ) : ℂ)
        rw [hcompat0 a₁ a₂ q v₁ v₂ h1 h2, hWΨ])
      s hs.2.1 hs.1 (fun x hx => hkill_of s hs x (left_ne_zero_of_mul hx))
    change ∫ x, φa (AutomorphicForm.archIdentGL K L (x⁻¹ * diagUnits2 α β * AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x)) *
      (W x : ℂ) * (s x : ℂ) ∂(AutomorphicForm.archHaarL K L) = _
    rw [heq, integral_prod _ hξWi]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hξWi.prod_right_ae] with u hu
    rw [integral_prod _ hu]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hξ0]
    exact integral_mul_const _ _

end S_AutomorphicForm_exists_pos_forall_twistedOrbital_archHaarL_diagUnits2_eq_mul_integral_ker_norm_integral_integral_and_twistedWeighted_eq_of_coupled
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_twistedOrbital_archHaarL_diagUnits2_eq_mul_integral_ker_norm_integral_integral_and_twistedWeighted_eq_of_coupled (solution)
