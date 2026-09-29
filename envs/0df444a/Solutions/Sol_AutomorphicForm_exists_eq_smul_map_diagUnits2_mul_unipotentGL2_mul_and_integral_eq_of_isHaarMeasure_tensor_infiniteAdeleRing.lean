-- Prove2me | solution 1 for AutomorphicForm.exists_eq_smul_map_diagUnits2_mul_unipotentGL2_mul_and_integral_eq_of_isHaarMeasure_tensor_infiniteAdeleRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5962273e-19bb-5f3e-8520-e728b5586e51

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_lintegral_tensor_infiniteAdeleRing_eq_mul_lintegral_diagUnits2_unipotentGL2_archIdentGL_rowIsometry
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_eq_smul_map_diagUnits2_mul_unipotentGL2_mul_and_integral_eq_of_isHaarMeasure_tensor_infiniteAdeleRing
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

noncomputable section

namespace IwBoch

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

section InstL
variable (L : Type) [Field L] [NumberField L]

scoped instance secondCountable_inf : SecondCountableTopology (InfiniteAdeleRing L) := by
  haveI : ∀ v : InfinitePlace L, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace L) → v.Completion))

end InstL

section InstE
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

theorem KcE_eq_comap :
    (⨅ w : InfinitePlace L,
      (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
        ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
        Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
    (⨅ w : InfinitePlace L,
      (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent L w) :
        Subgroup (GL (Fin 2) (InfiniteAdeleRing L))).comap (AutomorphicForm.archIdentGL K L) := by
  rw [Subgroup.comap_iInf]
  simp_rw [Subgroup.comap_comap]

scoped instance topRing_E : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.isTopologicalRing_tensor K L _
scoped instance topGroup_GE : IsTopologicalGroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := AutomorphicForm.isTopologicalGroup_tensorGL K L _
scoped instance t2_E : T2Space (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.t2Space_tensor K L _
scoped instance lc_E : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.locallyCompactSpace_tensor K L _
scoped instance sc_E : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K) := (AutomorphicForm.archIdentHomeomorph K L).secondCountableTopology
scoped instance sc_Eop : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
scoped instance sc_Eu : SecondCountableTopology (L ⊗[K] InfiniteAdeleRing K)ˣ := Units.isInducing_embedProduct.secondCountableTopology
scoped instance sc_M : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → (L ⊗[K] InfiniteAdeleRing K)))
scoped instance sc_Mop : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
scoped instance sc_GE : SecondCountableTopology (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := Units.isInducing_embedProduct.secondCountableTopology

theorem isCompact_KcE :
    IsCompact ((⨅ w : InfinitePlace L,
      (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
        ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
        Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := by
  rw [KcE_eq_comap K L, Subgroup.coe_comap]
  have hK := (NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup L).2
  have : (⇑(AutomorphicForm.archIdentGL K L) : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → GL (Fin 2) (InfiniteAdeleRing L)) =
      ⇑(AutomorphicForm.archIdentGLEquiv K L) := rfl
  rw [this]
  exact (AutomorphicForm.archIdentGLEquiv K L).toHomeomorph.isCompact_preimage.mpr hK

end InstE

end IwBoch
p2m_reactivate "P2MW.S_AutomorphicForm_exists_eq_smul_map_diagUnits2_mul_unipotentGL2_mul_and_integral_eq_of_isHaarMeasure_tensor_infiniteAdeleRing.IwBoch"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_eq_smul_map_diagUnits2_mul_unipotentGL2_mul_and_integral_eq_of_isHaarMeasure_tensor_infiniteAdeleRing.IwBoch"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 4000000 in
open IwBoch in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (ν : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) ν)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (ρ : Measure (L ⊗[K] InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    (κ : @Measure (↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ) :
    letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
      AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)
    letI : MeasurableSpace ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := borel _
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ν = c • Measure.map
        (fun p : ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) ×
            ((L ⊗[K] InfiniteAdeleRing K) × ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) =>
          diagUnits2 p.1.1 p.1.2 * AutomorphicForm.unipotentGL2 p.2.1 *
            (p.2.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))
        ((ρ.prod ρ).prod (lam.prod κ)) ∧
      ∀ f : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ, Measurable f →
        ∫ x, f x ∂ν =
          (c.toReal : ℂ) *
            ∫ p : ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) ×
                ((L ⊗[K] InfiniteAdeleRing K) × ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))),
              f (diagUnits2 p.1.1 p.1.2 * AutomorphicForm.unipotentGL2 p.2.1 *
                (p.2.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) ∂((ρ.prod ρ).prod (lam.prod κ)) := by
  letI mG : MeasurableSpace (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
    AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := AutomorphicForm.borelSpace_glBorelOf _
  letI mK : MeasurableSpace ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := borel _
  haveI hBK : BorelSpace ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := ⟨rfl⟩
  haveI hscK : SecondCountableTopology ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI hcK : CompactSpace ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := isCompact_iff_compactSpace.mp (isCompact_KcE K L)
  haveI : IsFiniteMeasure κ := CompactSpace.isFiniteMeasure
  haveI : SigmaFinite κ := IsFiniteMeasure.toSigmaFinite κ
  haveI : SFinite κ := inferInstance
  haveI : SFinite (lam.prod κ) := inferInstance

  have hP1 := AutomorphicForm.exists_lintegral_tensor_infiniteAdeleRing_eq_mul_lintegral_diagUnits2_unipotentGL2_archIdentGL_rowIsometry
    K L ν hν lam ρ
  rw [← KcE_eq_comap K L] at hP1
  obtain ⟨c, hc0, hct, h⟩ := hP1 κ hκ

  set Ψ : ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) ×
      ((L ⊗[K] InfiniteAdeleRing K) × ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) → GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) :=
    fun p => diagUnits2 p.1.1 p.1.2 * AutomorphicForm.unipotentGL2 p.2.1 *
      (p.2.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) with hΨ
  have hΨc : Continuous Ψ := by
    rw [hΨ]
    exact ((continuous_diagUnits2.comp continuous_fst).mul
      (continuous_unipotentGL2.comp (continuous_fst.comp continuous_snd))).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  have hΨm : Measurable Ψ := hΨc.measurable
  set π : Measure (((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) ×
      ((L ⊗[K] InfiniteAdeleRing K) × ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))) := (ρ.prod ρ).prod (lam.prod κ) with hπ
  have hmeas : ν = c • Measure.map Ψ π := by
    refine Measure.ext fun S hS => ?_
    have hmS : Measurable (S.indicator (1 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞)) :=
      measurable_one.indicator hS
    have hmSP : Measurable (fun p => S.indicator (1 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞) (Ψ p)) :=
      hmS.comp hΨm
    rw [Measure.smul_apply, Measure.map_apply hΨm hS, smul_eq_mul, ← lintegral_indicator_one hS, h _ hmS,
      ← lintegral_indicator_one (hS.preimage hΨm)]
    congr 1
    have hind : ∀ p, (Ψ ⁻¹' S).indicator (1 : (((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) ×
        ((L ⊗[K] InfiniteAdeleRing K) × ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))) → ℝ≥0∞) p =
        S.indicator (1 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞) (Ψ p) := by
      intro p
      by_cases hp : Ψ p ∈ S
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (Set.mem_preimage.mpr hp)]; rfl
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (fun h' => hp (Set.mem_preimage.mp h'))]
    simp_rw [hind]
    rw [hπ, lintegral_prod _ hmSP.aemeasurable]
    refine lintegral_congr fun a => ?_
    have h1 : Measurable (fun q : (L ⊗[K] InfiniteAdeleRing K) × ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =>
        S.indicator (1 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞) (Ψ (a, q))) :=
      hmSP.comp measurable_prodMk_left
    rw [lintegral_prod _ h1.aemeasurable]
  refine ⟨c, hc0, hct, hmeas, fun f hf => ?_⟩
  rw [hmeas, integral_smul_measure, integral_map hΨm.aemeasurable hf.aestronglyMeasurable, Complex.real_smul]

end S_AutomorphicForm_exists_eq_smul_map_diagUnits2_mul_unipotentGL2_mul_and_integral_eq_of_isHaarMeasure_tensor_infiniteAdeleRing
end P2MW
export P2MW.S_AutomorphicForm_exists_eq_smul_map_diagUnits2_mul_unipotentGL2_mul_and_integral_eq_of_isHaarMeasure_tensor_infiniteAdeleRing (solution)
