-- Prove2me | solution 1 for AutomorphicForm.exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d3a5dbc5-f786-5d1b-a790-215cba2c576d

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule
import Theorems.Thm_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
import Theorems.Thm_AutomorphicForm_finiteDimensional_span_translates_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_isCompact_rowIsometrySubgroup_detOne
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "IsDedekindDomain AutomorphicForm P2MW.S_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

open scoped Topology
open Filter

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchTypeFamily archCutSubmodule IsArchBiFinite IsArchBiFinite.of_factorization AdelicGL2 rightConv rightConv_apply rowIsometrySubgroup₀ adelicArchGLIncl glArch_adelicArchGLIncl glFin_adelicArchGLIncl archEntries IsArchTestFactor IsFactorizableTestFn exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule finiteDimensional_span_translates_of_mem_archCutSubmodule isCompact_rowIsometrySubgroup_detOne"
namespace EigenBifin
p2m_open "AutomorphicForm"

variable {F : Type} [Field F] [NumberField F]

private def iota (F : Type) [Field F] [NumberField F] :
    (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F) :=
  (Units.map (Matrix.piRingEquiv (β := fun w : InfinitePlace F => w.Completion) (n := Fin 2)).symm.toRingHom.toMonoidHom).comp
    ((MulEquiv.piUnits (M := fun w : InfinitePlace F => Matrix (Fin 2) (Fin 2) w.Completion)).symm.toMonoidHom.comp
      (MonoidHom.pi fun w : InfinitePlace F =>
        (rowIsometrySubgroup₀ w.Completion).subtype.comp
          (Pi.evalMonoidHom (fun w : InfinitePlace F => ↥(rowIsometrySubgroup₀ w.Completion)) w)))

private theorem archComponent_iota (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (w : InfinitePlace F) :
    archComponent F w (iota F κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) := by
  ext i j
  rfl

private theorem continuous_iota : Continuous (iota F) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => continuous_pi fun w => ?_
    show Continuous fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
      (((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
    exact (Units.continuous_val.matrix_elem i j).comp (continuous_subtype_val.comp (continuous_apply w))
  · refine continuous_matrix fun i j => continuous_pi fun w => ?_
    have : (fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
        (((iota F κ)⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w)
        = fun κ => ((((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)⁻¹ : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion) i j := by
      funext κ
      rw [← map_inv]
      rfl
    rw [this]
    exact (Units.continuous_coe_inv.matrix_elem i j).comp (continuous_subtype_val.comp (continuous_apply w))

private theorem eq_of_isMulLeftInvariant_of_isProbabilityMeasure {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ' μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] [μ'.IsMulLeftInvariant] [IsProbabilityMeasure μ'] : μ' = μ := by
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace μ' μ
  have hc : Measure.haarScalarFactor μ' μ = 1 := by
    have h1 := congrArg (fun ν : Measure G => ν Set.univ) h
    simp only [Measure.smul_apply, measure_univ] at h1
    rw [ENNReal.smul_def, smul_eq_mul, mul_one] at h1
    exact_mod_cast h1.symm
  rw [h, hc, one_smul]

private theorem continuous_adelicArchGLIncl' : Continuous (adelicArchGLIncl F) := by
  refine Units.continuous_iff.mpr ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · have : (fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
        ((adelicArchGLIncl F k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j)
        = fun k : GL (Fin 2) (InfiniteAdeleRing F) => (((k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
            (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F) := by
      funext k; rfl
    have hc : Continuous fun k : GL (Fin 2) (InfiniteAdeleRing F) => (((k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F) :=
      (Units.continuous_val.matrix_elem i j).prodMk continuous_const
    rw [← this] at hc
    exact hc
  · have : (fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
        (((adelicArchGLIncl F k)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j)
        = fun k : GL (Fin 2) (InfiniteAdeleRing F) => ((((k⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
            (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F) := by
      funext k; rw [← map_inv]; rfl
    have hc : Continuous fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
        ((((k⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
          (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F) :=
      (Units.continuous_coe_inv.matrix_elem i j).prodMk continuous_const
    rw [← this] at hc
    exact hc

private theorem continuous_finEmbed : Continuous (AdelicDock.finEmbed (𝓞 F) F) := by
  refine Units.continuous_iff.mpr ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => AdelicDock.finMat (𝓞 F) F g i j
    exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)
  · show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
      AdelicDock.finMat (𝓞 F) F ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix _ _ _) i j
    exact continuous_const.prodMk (Units.continuous_coe_inv.matrix_elem i j)

private theorem adelicArchGLIncl_glArch_mul_finEmbed_glFin (y : AdelicGL2 (𝓞 F) F) :
    adelicArchGLIncl F (glArch (𝓞 F) F y) * AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F y) = y := by
  apply Units.ext
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_
  · show ((glArch (𝓞 F) F (adelicArchGLIncl F (glArch (𝓞 F) F y) * AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F y)) :
        GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = ((glArch (𝓞 F) F y : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix _ _ _)
    rw [map_mul, glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one]
  · show ((glFin (𝓞 F) F (adelicArchGLIncl F (glArch (𝓞 F) F y) * AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F y)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) = ((glFin (𝓞 F) F y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix _ _ _)
    rw [map_mul, glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, one_mul]

open scoped Classical in
omit [NumberField F] in
private theorem continuous_archEntries [NumberField F] : Continuous (archEntries F) :=
  continuous_pi fun i => continuous_pi fun j =>
    (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F).comp (Units.continuous_val.matrix_elem i j)

open scoped Classical in
private theorem IsArchTestFactor.continuous' {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (h : IsArchTestFactor F fa) :
    Continuous fa := by
  obtain ⟨⟨Φ, hΦ, heq⟩, -⟩ := h
  have : fa = Φ ∘ archEntries F := funext heq
  rw [this]
  exact hΦ.continuous.comp continuous_archEntries

private theorem continuous_and_hasCompactSupport_of_isFactorizableTestFn {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsFactorizableTestFn F f) : Continuous f ∧ HasCompactSupport f := by
  obtain ⟨fa, ff, hfa, hff, hfeq⟩ := hf
  have hfeq' : f = fun g => fa (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g) := funext hfeq
  refine ⟨?_, ?_⟩
  · rw [hfeq']
    exact ((IsArchTestFactor.continuous' hfa).comp (continuous_glArch (𝓞 F) F)).mul
      (hff.1.continuous.comp (continuous_glFin (𝓞 F) F))
  · set Kc : Set (AdelicGL2 (𝓞 F) F) :=
      (fun q : GL (Fin 2) (InfiniteAdeleRing F) × GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
        adelicArchGLIncl F q.1 * AdelicDock.finEmbed (𝓞 F) F q.2) '' (tsupport fa ×ˢ tsupport ff) with hKc
    have hKcpt : IsCompact Kc :=
      (hfa.2.prod hff.2).image ((continuous_adelicArchGLIncl'.comp continuous_fst).mul (continuous_finEmbed.comp continuous_snd))
    refine HasCompactSupport.intro hKcpt fun g hg => ?_
    by_contra hne
    apply hg
    refine ⟨(glArch (𝓞 F) F g, glFin (𝓞 F) F g), ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩,
      adelicArchGLIncl_glArch_mul_finEmbed_glFin g⟩
    · intro h0; exact hne (by rw [hfeq g, h0, zero_mul])
    · intro h0; exact hne (by rw [hfeq g, h0, mul_zero])

section Sandwich

variable [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)] [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
  (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) [IsProbabilityMeasure μ]
  (J : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* AdelicGL2 (𝓞 F) F) (hJc : Continuous J)
  (e : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ) (he : Continuous e)
  (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ)
  (f : AdelicGL2 (𝓞 F) F → ℂ) (hfc : Continuous f) (hfK : HasCompactSupport f)
  (lam : ℂ)
  (heig : ∀ g : AdelicGL2 (𝓞 F) F, ∫ x, φ (g * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = lam * φ g)
  (hrep : ∀ z : AdelicGL2 (𝓞 F) F, ∫ κ, e κ * φ (z * J κ) ∂μ = φ z)

private theorem integral_subst (g : AdelicGL2 (𝓞 F) F)
    (p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) :
    ∫ x, φ (g * x) * f ((J p.1)⁻¹ * x * (J p.2)⁻¹) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = ∫ x, φ (g * J p.1 * x * J p.2) * f x ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
  haveI : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
  calc ∫ x, φ (g * x) * f ((J p.1)⁻¹ * x * (J p.2)⁻¹) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = ∫ x, φ (g * (J p.1 * x)) * f ((J p.1)⁻¹ * (J p.1 * x) * (J p.2)⁻¹) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
        (integral_mul_left_eq_self (fun x => φ (g * x) * f ((J p.1)⁻¹ * x * (J p.2)⁻¹)) (J p.1)).symm
    _ = ∫ x, φ (g * (J p.1 * (x * J p.2))) * f ((J p.1)⁻¹ * (J p.1 * (x * J p.2)) * (J p.2)⁻¹) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
        (integral_mul_right_eq_self (fun x => φ (g * (J p.1 * x)) * f ((J p.1)⁻¹ * (J p.1 * x) * (J p.2)⁻¹)) (J p.2)).symm
    _ = ∫ x, φ (g * J p.1 * x * J p.2) * f x ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        show φ (g * (J p.1 * (x * J p.2))) * f ((J p.1)⁻¹ * (J p.1 * (x * J p.2)) * (J p.2)⁻¹) = φ (g * J p.1 * x * J p.2) * f x
        rw [show (J p.1)⁻¹ * (J p.1 * (x * J p.2)) * (J p.2)⁻¹ = x by group,
          show g * (J p.1 * (x * J p.2)) = g * J p.1 * x * J p.2 by group]

include hJc he hφc hfc hfK heig hrep in
set_option maxHeartbeats 3200000 in

private theorem sandwich [SecondCountableTopology (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)] [CompactSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [SecondCountableTopology (AdelicGL2 (𝓞 F) F)] (g : AdelicGL2 (𝓞 F) F) :
    ∫ x, φ (g * x) * (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e p.1 * e p.2 * f ((J p.1)⁻¹ * x * (J p.2)⁻¹) ∂(μ.prod μ))
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = lam * φ g := by

  haveI : SigmaFinite μ := IsFiniteMeasure.toSigmaFinite μ
  haveI : SFinite μ := inferInstance
  haveI : IsFiniteMeasure (μ.prod μ) := inferInstance
  haveI : SigmaFinite (μ.prod μ) := IsFiniteMeasure.toSigmaFinite _
  haveI : SFinite (μ.prod μ) := inferInstance
  haveI hμμ : IsFiniteMeasureOnCompacts (μ.prod μ) := ⟨fun K _ => measure_lt_top _ K⟩
  haveI hμK : IsFiniteMeasureOnCompacts μ := ⟨fun K _ => measure_lt_top _ K⟩
  haveI : SigmaFinite (adelicGLHaar (Fin 2) (𝓞 F) F) := inferInstance
  haveI : IsFiniteMeasureOnCompacts (adelicGLHaar (Fin 2) (𝓞 F) F) := inferInstance
  haveI : IsFiniteMeasureOnCompacts ((adelicGLHaar (Fin 2) (𝓞 F) F).prod (μ.prod μ)) :=
    Measure.prod.instIsFiniteMeasureOnCompacts _ _
  haveI : IsFiniteMeasureOnCompacts ((μ.prod μ).prod (adelicGLHaar (Fin 2) (𝓞 F) F)) :=
    Measure.prod.instIsFiniteMeasureOnCompacts _ _
  haveI : IsFiniteMeasureOnCompacts ((adelicGLHaar (Fin 2) (𝓞 F) F).prod μ) :=
    Measure.prod.instIsFiniteMeasureOnCompacts _ _
  haveI : IsFiniteMeasureOnCompacts (μ.prod (adelicGLHaar (Fin 2) (𝓞 F) F)) :=
    Measure.prod.instIsFiniteMeasureOnCompacts _ _
  have hJinv : Continuous fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => (J κ)⁻¹ := hJc.inv

  set Ψ : AdelicGL2 (𝓞 F) F → (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ := fun x p =>
    φ (g * x) * (e p.1 * e p.2 * f ((J p.1)⁻¹ * x * (J p.2)⁻¹)) with hΨ
  have hΨc : Continuous (Function.uncurry Ψ) := by
    refine (hφc.comp (continuous_const.mul continuous_fst)).mul ?_
    refine ((he.comp (continuous_fst.comp continuous_snd)).mul (he.comp (continuous_snd.comp continuous_snd))).mul
      (hfc.comp ?_)
    exact ((hJinv.comp (continuous_fst.comp continuous_snd)).mul continuous_fst).mul
      (hJinv.comp (continuous_snd.comp continuous_snd))
  have hΨK : HasCompactSupport (Function.uncurry Ψ) := by
    set Kc : Set (AdelicGL2 (𝓞 F) F) := (fun t : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × AdelicGL2 (𝓞 F) F × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => J t.1 * t.2.1 * J t.2.2) ''
      (Set.univ ×ˢ (tsupport f ×ˢ Set.univ)) with hKc
    have hKcpt : IsCompact Kc :=
      (isCompact_univ.prod (hfK.prod isCompact_univ)).image
        (((hJc.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).mul
          (hJc.comp (continuous_snd.comp continuous_snd)))
    refine HasCompactSupport.intro (hKcpt.prod isCompact_univ) ?_
    rintro ⟨x, p⟩ hxp
    have hx : x ∉ Kc := fun h' => hxp ⟨h', Set.mem_univ _⟩
    have hzero : f ((J p.1)⁻¹ * x * (J p.2)⁻¹) = 0 := by
      by_contra hne
      apply hx
      refine ⟨(p.1, (J p.1)⁻¹ * x * (J p.2)⁻¹, p.2), ⟨Set.mem_univ _, subset_tsupport _ hne, Set.mem_univ _⟩, ?_⟩
      show J p.1 * ((J p.1)⁻¹ * x * (J p.2)⁻¹) * J p.2 = x
      group
    show φ (g * x) * (e p.1 * e p.2 * f ((J p.1)⁻¹ * x * (J p.2)⁻¹)) = 0
    rw [hzero, mul_zero, mul_zero]
  have hΨint : Integrable (Function.uncurry Ψ) ((adelicGLHaar (Fin 2) (𝓞 F) F).prod (μ.prod μ)) :=
    Continuous.integrable_of_hasCompactSupport hΨc hΨK

  set Ψ' : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → AdelicGL2 (𝓞 F) F → ℂ := fun p x =>
    e p.1 * e p.2 * (φ (g * J p.1 * x * J p.2) * f x) with hΨ'
  have hΨ'c : Continuous (Function.uncurry Ψ') := by
    refine ((he.comp (continuous_fst.comp continuous_fst)).mul (he.comp (continuous_snd.comp continuous_fst))).mul
      ((hφc.comp ?_).mul (hfc.comp continuous_snd))
    exact ((continuous_const.mul (hJc.comp (continuous_fst.comp continuous_fst))).mul continuous_snd).mul
      (hJc.comp (continuous_snd.comp continuous_fst))
  have hΨ'K : HasCompactSupport (Function.uncurry Ψ') := by
    refine HasCompactSupport.intro (isCompact_univ.prod hfK) ?_
    rintro ⟨p, x⟩ hpx
    have hx : x ∉ tsupport f := fun h' => hpx ⟨Set.mem_univ _, h'⟩
    show e p.1 * e p.2 * (φ (g * J p.1 * x * J p.2) * f x) = 0
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
  have hΨ'int : Integrable (Function.uncurry Ψ') ((μ.prod μ).prod (adelicGLHaar (Fin 2) (𝓞 F) F)) :=
    Continuous.integrable_of_hasCompactSupport hΨ'c hΨ'K

  set Θ : AdelicGL2 (𝓞 F) F → (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ := fun x κ => e κ * (φ (g * J κ * x) * f x) with hΘ
  have hΘc : Continuous (Function.uncurry Θ) := by
    refine (he.comp continuous_snd).mul ((hφc.comp ?_).mul (hfc.comp continuous_fst))
    exact (continuous_const.mul (hJc.comp continuous_snd)).mul continuous_fst
  have hΘK : HasCompactSupport (Function.uncurry Θ) := by
    refine HasCompactSupport.intro (hfK.prod isCompact_univ) ?_
    rintro ⟨x, κ⟩ hxκ
    have hx : x ∉ tsupport f := fun h' => hxκ ⟨h', Set.mem_univ _⟩
    show e κ * (φ (g * J κ * x) * f x) = 0
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
  have hΘint : Integrable (Function.uncurry Θ) ((adelicGLHaar (Fin 2) (𝓞 F) F).prod μ) :=
    Continuous.integrable_of_hasCompactSupport hΘc hΘK

  have hcollapse : ∀ x : AdelicGL2 (𝓞 F) F, ∫ p, Ψ' p x ∂(μ.prod μ) = ∫ κ, Θ x κ ∂μ := by
    intro x
    have hc : Continuous fun p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => Ψ' p x :=
      hΨ'c.comp (continuous_id.prodMk continuous_const)
    have hint : Integrable (fun p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => Ψ' p x) (μ.prod μ) :=
      hc.integrable_of_hasCompactSupport
        (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))
    rw [integral_prod _ hint]
    refine integral_congr_ae (ae_of_all _ fun κ₁ => ?_)
    show ∫ κ₂, e (κ₁, κ₂).1 * e (κ₁, κ₂).2 * (φ (g * J (κ₁, κ₂).1 * x * J (κ₁, κ₂).2) * f x) ∂μ
      = e κ₁ * (φ (g * J κ₁ * x) * f x)
    have h1 : ∀ κ₂ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e (κ₁, κ₂).1 * e (κ₁, κ₂).2 * (φ (g * J (κ₁, κ₂).1 * x * J (κ₁, κ₂).2) * f x)
        = e κ₁ * f x * (e κ₂ * φ ((g * J κ₁ * x) * J κ₂)) := by
      intro κ₂
      show e κ₁ * e κ₂ * (φ (g * J κ₁ * x * J κ₂) * f x) = e κ₁ * f x * (e κ₂ * φ (g * J κ₁ * x * J κ₂))
      ring
    simp_rw [h1]
    rw [integral_const_mul, hrep (g * J κ₁ * x)]
    ring

  calc ∫ x, φ (g * x) * (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e p.1 * e p.2 * f ((J p.1)⁻¹ * x * (J p.2)⁻¹) ∂(μ.prod μ))
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
      = ∫ x, ∫ p, Ψ x p ∂(μ.prod μ) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        exact (integral_const_mul _ _).symm
    _ = ∫ p, ∫ x, Ψ x p ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ∂(μ.prod μ) := integral_integral_swap hΨint
    _ = ∫ p, ∫ x, Ψ' p x ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ∂(μ.prod μ) := by
        refine integral_congr_ae (ae_of_all _ fun p => ?_)
        show ∫ x, Ψ x p ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = ∫ x, Ψ' p x ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
        have h1 : ∀ x, Ψ x p = e p.1 * e p.2 * (φ (g * x) * f ((J p.1)⁻¹ * x * (J p.2)⁻¹)) := by
          intro x; show φ (g * x) * (e p.1 * e p.2 * f ((J p.1)⁻¹ * x * (J p.2)⁻¹)) = _; ring
        simp_rw [h1]
        rw [integral_const_mul, integral_subst J φ f g p, ← integral_const_mul]
    _ = ∫ x, ∫ p, Ψ' p x ∂(μ.prod μ) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := integral_integral_swap hΨ'int
    _ = ∫ x, ∫ κ, Θ x κ ∂μ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        exact hcollapse x
    _ = ∫ κ, ∫ x, Θ x κ ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ∂μ := integral_integral_swap hΘint
    _ = ∫ κ, lam * (e κ * φ (g * J κ)) ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun κ => ?_)
        show ∫ x, e κ * (φ (g * J κ * x) * f x) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = lam * (e κ * φ (g * J κ))
        rw [integral_const_mul, heig (g * J κ)]
        ring
    _ = lam * φ g := by
        rw [integral_const_mul, hrep g]

end Sandwich

end AutomorphicForm.EigenBifin

end

open AutomorphicForm.EigenBifin in

theorem solution
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (hφt : φ ∈ archCutSubmodule F tys)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (lam : ℂ)
    (heig : rightConv F φ f = lam • φ) :
    ∃ f' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f' ∧ IsArchBiFinite F tys f' ∧
      rightConv F φ f' = lam • φ := by
  classical

  haveI : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  haveI : ∀ w : InfinitePlace F, CompactSpace ↥(rowIsometrySubgroup₀ w.Completion) := fun w =>
    isCompact_iff_compactSpace.mp (AutomorphicForm.isCompact_rowIsometrySubgroup_detOne F w)
  haveI : CompactSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := Pi.compactSpace
  haveI : ∀ v : InfinitePlace F, ProperSpace v.Completion := fun v => properSpace_completion v
  have hKsc : ∀ w : InfinitePlace F, SecondCountableTopology ↥(rowIsometrySubgroup₀ w.Completion) := by
    intro w
    haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) w.Completion) :=
      inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → w.Completion))
    haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) w.Completion)ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
    haveI : SecondCountableTopology (GL (Fin 2) w.Completion) := Units.isEmbedding_embedProduct.secondCountableTopology
    exact TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := by
    haveI := hKsc; infer_instance
  letI mK : MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := borel _
  haveI : BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := ⟨rfl⟩
  haveI : Nonempty (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := ⟨1⟩
  set μK : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) :=
    Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) with hμK
  haveI hKprob : IsProbabilityMeasure μK :=
    ⟨by rw [hμK, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩
  haveI hKright : μK.IsMulRightInvariant := by
    refine ⟨fun g => ?_⟩
    haveI : IsProbabilityMeasure (μK.map (· * g)) :=
      Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
    exact eq_of_isMulLeftInvariant_of_isProbabilityMeasure (μK.map (· * g)) μK
  set J : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* AdelicGL2 (𝓞 F) F := (adelicArchGLIncl F).comp (iota F) with hJdef
  have hJ : ∀ κ, adelicArchGLIncl F (iota F κ) = J κ := fun κ => rfl
  have hJc : Continuous J := continuous_adelicArchGLIncl'.comp continuous_iota

  obtain ⟨hEfd, hEc, hEt, hEK⟩ :=
    AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule F (iota F) archComponent_iota tys φ hφc hφt
  set E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
    fun g : AdelicGL2 (𝓞 F) F => φ (g * adelicArchGLIncl F (iota F κ))) with hE
  have hφE : φ ∈ E := by
    refine Submodule.subset_span ⟨1, ?_⟩
    funext g
    simp only [map_one, mul_one]
  obtain ⟨e, he, -, -, het, het', hrep⟩ :=
    AutomorphicForm.exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule
      F μK (iota F) archComponent_iota tys E hEfd hEc hEt hEK

  obtain ⟨hfc, hfK⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn hf
  obtain ⟨fa, ff, hfa, hff, hfeq⟩ := hf
  set fa' : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := fun y => ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
      e p.1 * e p.2 * fa ((iota F p.1)⁻¹ * y * (iota F p.2)⁻¹) ∂(μK.prod μK) with hfa'
  obtain ⟨hfa't, hfa'bf⟩ :=
    AutomorphicForm.isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
      F μK (iota F) archComponent_iota tys e e he he fa hfa
  set f' : AdelicGL2 (𝓞 F) F → ℂ := fun g => fa' (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g) with hf'
  refine ⟨f', ⟨fa', ff, hfa't, hff, fun g => rfl⟩, IsArchBiFinite.of_factorization F (fun g => rfl) (hfa'bf het het'), ?_⟩

  have hf'J : ∀ x : AdelicGL2 (𝓞 F) F,
      f' x = ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e p.1 * e p.2 * f ((J p.1)⁻¹ * x * (J p.2)⁻¹) ∂(μK.prod μK) := by
    intro x
    have h1 : ∀ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e p.1 * e p.2 * f ((J p.1)⁻¹ * x * (J p.2)⁻¹)
        = e p.1 * e p.2 * fa ((iota F p.1)⁻¹ * glArch (𝓞 F) F x * (iota F p.2)⁻¹) * ff (glFin (𝓞 F) F x) := by
      intro p
      rw [hfeq, ← hJ, ← hJ, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, map_inv,
        glArch_adelicArchGLIncl, glArch_adelicArchGLIncl, glFin_adelicArchGLIncl, glFin_adelicArchGLIncl,
        inv_one, one_mul, mul_one]
      ring
    show fa' (glArch (𝓞 F) F x) * ff (glFin (𝓞 F) F x) = _
    simp_rw [h1]
    rw [integral_mul_const]
  have heig' : ∀ g : AdelicGL2 (𝓞 F) F, ∫ x, φ (g * x) * f x ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = lam * φ g := by
    intro g
    have := congrFun heig g
    rw [rightConv_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this
  have hrep' : ∀ z : AdelicGL2 (𝓞 F) F, ∫ κ, e κ * φ (z * J κ) ∂μK = φ z := fun z => hrep φ hφE z
  funext g
  rw [Pi.smul_apply, smul_eq_mul, rightConv_apply]
  show ∫ x, φ (g * x) * f' x ∂(adelicGLHaar (Fin 2) (𝓞 F) F) = lam * φ g
  simp_rw [hf'J]
  exact sandwich μK J hJc e he φ hφc f hfc hfK lam heig' hrep' g

#print axioms solution

end S_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul
end P2MW
export P2MW.S_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul (solution)
