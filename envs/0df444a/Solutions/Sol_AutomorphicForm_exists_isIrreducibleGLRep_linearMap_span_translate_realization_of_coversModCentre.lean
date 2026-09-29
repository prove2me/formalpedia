-- Prove2me | solution 1 for AutomorphicForm.exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a2677c32-8728-580a-8982-2054570b4fbd

import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_ConductorDatum
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite
import Theorems.Thm_AutomorphicForm_IsIsotypicCuspFormAt_of_le_of_subset
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite
import Theorems.Thm_AutomorphicForm_eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
import Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent
import Theorems.Thm_LanglandsTunnell_exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule
import Theorems.Thm_LocalNewvector_exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep
import Theorems.Thm_LocalNewvector_exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top
import Theorems.Thm_NumberField_AdelicHaar_exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.SimpleModule.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"
set_option Elab.async false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm"
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.toFn_mk AdelicFnCarrier.mk_toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_zero AdelicFnCarrier.toFn_add AdelicFnCarrier.toFn_csmul AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def IsIrreducibleGLRep exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace TrivialLine
p2m_open "LocalNewvector"

private def trivialAction (q : ℕ) [Fact q.Prime] : DistribMulAction (GL (Fin 2) ℚ_[q]) ℂ where
  smul _ v := v
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

private theorem trivialAction_smulCommClass (q : ℕ) [Fact q.Prime] :
    letI := trivialAction q
    SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ ℂ :=
  letI := trivialAction q
  ⟨fun _ _ _ => rfl⟩

private theorem isIrreducibleGLRep_trivialAction (q : ℕ) [Fact q.Prime] :
    letI := trivialAction q
    IsIrreducibleGLRep q ℂ := by
  letI := trivialAction q
  exact ⟨⟨1, one_ne_zero⟩, fun W _ => eq_bot_or_eq_top W⟩
end LocalNewvector.TrivialLine

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.toFn_mk AdelicFnCarrier.mk_toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_zero AdelicFnCarrier.toFn_add AdelicFnCarrier.toFn_csmul AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def IsIrreducibleGLRep exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace NearClassEmbedding
p2m_open "LocalNewvector"

private noncomputable abbrev windowPins (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) :=
  productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)

private abbrev genSet (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (Θ : HeckeEigensystem ℚ ℂ) :
    Set (LocalNewvector.AdelicFnCarrier ℚ) :=
  {χ | ∃ (g : AdelicGL2 (𝓞 ℚ) ℚ) (Θ' : HeckeEigensystem ℚ ℂ) (_ : Θ'.AgreesAwayFromFinite Θ)
      (R' : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ')
      (_ : IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ' R'),
      χ = g • LocalNewvector.AdelicFnCarrier.mk R'.toFun}

private abbrev genSpan (q : ℕ) [Fact q.Prime] (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    Submodule ℂ (LocalNewvector.AdelicFnCarrier ℚ) :=
  Submodule.span ℂ {χ | ∃ x : GL (Fin 2) ℚ_[q], χ = x • LocalNewvector.AdelicFnCarrier.mk φ}

end LocalNewvector.NearClassEmbedding

section

open NumberField

private theorem continuous_archEntries : Continuous (AutomorphicForm.archEntries ℚ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (AdelicBox.continuous_ringEquiv_mixedSpace ℚ).comp (Units.continuous_val.matrix_elem i j)

private theorem continuous_of_isArchTestFactor {fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchTestFactor ℚ fa) : Continuous fa := by
  classical
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, -⟩ := hfa
  have h : fa = Φ ∘ AutomorphicForm.archEntries ℚ := funext hfaΦ
  rw [h]
  exact hΦ.continuous.comp continuous_archEntries

private theorem hasCompactSupport_of_isArchTestFactor
    {fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ} (hfa : AutomorphicForm.IsArchTestFactor ℚ fa) :
    HasCompactSupport fa :=
  hfa.2

private theorem adelicArchGLIncl_entry (a : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) (i j : Fin 2) :
    ((AutomorphicForm.adelicArchGLIncl ℚ a : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j =
      (((a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j,
        ((1 : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) :
          Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ) := by
  have h₁ := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) =>
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j) (AutomorphicForm.glArch_adelicArchGLIncl ℚ a)
  have h₂ := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) =>
    (g : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) i j)
    (AutomorphicForm.glFin_adelicArchGLIncl ℚ a)
  simp only [AdelicLevel.glArch, AdelicLevel.glFin, Matrix.GeneralLinearGroup.map_apply, AdelicLevel.adeleArch_apply,
    AdelicLevel.adeleFin_apply] at h₁ h₂
  exact Prod.ext h₁ h₂

private theorem continuous_adelicArchGLIncl : Continuous (AutomorphicForm.adelicArchGLIncl ℚ) := by
  obtain ⟨hval, hinv⟩ := Units.continuous_iff.mp
    (continuous_id : Continuous fun a : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) => a)
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    exact ((hval.matrix_elem i j).prodMk continuous_const).congr fun a => (adelicArchGLIncl_entry a i j).symm
  · refine continuous_matrix fun i j => ?_
    have e : ∀ a : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ),
        (((a⁻¹ : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) :
            Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j,
          ((1 : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) :
            Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) =
          (((AutomorphicForm.adelicArchGLIncl ℚ a)⁻¹ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j := by
      intro a
      rw [← map_inv]
      exact (adelicArchGLIncl_entry a⁻¹ i j).symm
    exact ((hinv.matrix_elem i j).prodMk continuous_const).congr e

end

section

p2m_open "NumberField AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm"

private theorem padicToAdelic_mul_comm_of_finComponent_eq_one (q : ℕ) [Fact q.Prime]
    (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (hq : AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ h) = 1)
    (x : GL (Fin 2) ℚ_[q]) :
    (AdelicDock.padicToAdelic q x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) * h =
      h * AdelicDock.padicToAdelic q x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ
  ·
    rw [map_mul, map_mul]
    have harch : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        ((AdelicDock.padicToAdelic q x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
      calc (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
            ((AdelicDock.padicToAdelic q x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))
            = ((AdelicLevel.glArch (𝓞 ℚ) ℚ (AdelicDock.padicToAdelic q x) : GL (Fin 2) (InfiniteAdeleRing ℚ)) :
                Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) := rfl
        _ = 1 := by rw [AdelicDock.glArch_padicToAdelic]; exact Units.val_one
    rw [harch, one_mul, mul_one]
  ·
    rw [map_mul, map_mul]
    apply AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ
    intro w
    rw [map_mul, map_mul]
    by_cases hw : w = AdelicDock.padicPlace q
    ·
      subst hw
      have hh : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)).mapMatrix
          ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) = 1 := by
        calc (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)).mapMatrix
              ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))
              = ((AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ h) :
                    GL (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ)) :
                  Matrix (Fin 2) (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ)) := rfl
          _ = 1 := by rw [hq]; exact Units.val_one
      rw [hh, one_mul, mul_one]
    ·
      have hx : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
          ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
            ((AdelicDock.padicToAdelic q x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) = 1 := by
        calc (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
              ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
                ((AdelicDock.padicToAdelic q x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
                  Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)))
              = ((AdelicLevel.finComponent (𝓞 ℚ) ℚ w
                    (AdelicLevel.glFin (𝓞 ℚ) ℚ (AdelicDock.padicToAdelic q x)) :
                    GL (Fin 2) (w.adicCompletion ℚ)) :
                  Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) := rfl
          _ = 1 := by
            rw [AdelicDock.glFin_padicToAdelic, AdelicDock.finComponent_padicToFinAdelic_of_ne q x hw]
            exact Units.val_one
      rw [hx, one_mul, mul_one]

private theorem comp_mul_mem_archCutSubmodule_of_commute {tys : ArchTypeFamily ℚ}
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ archCutSubmodule ℚ tys) (g : AdelicGL2 (𝓞 ℚ) ℚ)
    (hg : ∀ (w : InfinitePlace ℚ) (k : rowIsometrySubgroup₀ w.Completion), Commute g (rowIsometryInclAt₀ ℚ w k)) :
    (fun x => f (x * g)) ∈ archCutSubmodule ℚ tys := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  refine Submodule.iSup_induction _
    (motive := fun f => (fun x => f (x * g)) ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt ℚ w (tys.rep w i))
    (hf w) ?_ ?_ ?_
  · intro i f hfi
    exact le_iSup (fun j => archTypeSubmoduleAt ℚ w (tys.rep w j)) i
      (comp_mul_mem_typeSubmodule_of_commute hfi g (hg w))
  · exact Submodule.zero_mem _
  · exact fun _ _ hu hv => Submodule.add_mem _ hu hv

private theorem commute_padicToAdelic_rowIsometryInclAt₀ (q : ℕ) [Fact q.Prime] (x : GL (Fin 2) ℚ_[q])
    (w : InfinitePlace ℚ) (k : rowIsometrySubgroup₀ w.Completion) :
    Commute (AdelicDock.padicToAdelic q x : AdelicGL2 (𝓞 ℚ) ℚ) (rowIsometryInclAt₀ ℚ w k) :=
  padicToAdelic_mul_comm_of_finComponent_eq_one q (rowIsometryInclAt₀ ℚ w k)
    (by rw [glFin_rowIsometryInclAt₀, map_one]) x

private theorem comp_mul_padicToAdelic_mem_archCutSubmodule {tys : ArchTypeFamily ℚ}
    {f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ archCutSubmodule ℚ tys) (q : ℕ) [Fact q.Prime]
    (x : GL (Fin 2) ℚ_[q]) :
    (fun y => f (y * AdelicDock.padicToAdelic q x)) ∈ archCutSubmodule ℚ tys :=
  comp_mul_mem_archCutSubmodule_of_commute hf _ (commute_padicToAdelic_rowIsometryInclAt₀ q x)

end

section

open NumberField IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm AutomorphicForm.CuspidalConstituent"

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.toFn_mk AdelicFnCarrier.mk_toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_zero AdelicFnCarrier.toFn_add AdelicFnCarrier.toFn_csmul AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def IsIrreducibleGLRep exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace Members
p2m_open "LocalNewvector"

private theorem padicToAdelic_mem_finiteAdelicGL2Subgroup (q : ℕ) [Fact q.Prime] (x : GL (Fin 2) ℚ_[q]) :
    AdelicDock.padicToAdelic q x ∈ finiteAdelicGL2Subgroup ℚ :=
  (mem_finiteAdelicGL2Subgroup_iff ℚ _).mpr (AdelicDock.glArch_padicToAdelic q x)

private theorem toFn_padic_smul (q : ℕ) [Fact q.Prime] (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ) :
    (x • ψ).toFn = rightTranslate ℚ (AdelicDock.padicToAdelic q x) ψ.toFn :=
  funext fun y => by rw [AdelicFnCarrier.padic_smul_def, AdelicFnCarrier.toFn_smul, rightTranslate_apply]

private theorem toFn_smul_mem_of_isCuspSubrep (pins : CarrierPins ℚ) (ξ : pins.Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (hV : IsCuspSubrep ℚ pins ξ V) (q : ℕ) [Fact q.Prime]
    (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ) (hψ : ψ.toFn ∈ V) : (x • ψ).toFn ∈ V := by
  rw [toFn_padic_smul]
  exact hV.rightTranslate_fin_mem _ (padicToAdelic_mem_finiteAdelicGL2Subgroup q x) _ hψ

private theorem toFn_smul_mem_of_isCuspConstituent (pins : CarrierPins ℚ) (ξ : pins.Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (hV : IsCuspConstituent ℚ pins ξ V) (q : ℕ) [Fact q.Prime]
    (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ) (hψ : ψ.toFn ∈ V) : (x • ψ).toFn ∈ V :=
  toFn_smul_mem_of_isCuspSubrep pins ξ V hV.1 q x ψ hψ

end LocalNewvector.Members

end

section

namespace SubsingletonSup

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

private theorem exists_mem_eq_iSup_of_ne_zero_of_mem_iSup (P : Submodule R M → Prop)
    (huniq : ∀ V₁ V₂ : Submodule R M, P V₁ → P V₂ → V₁ = V₂) {m : M} (hm : m ≠ 0)
    (h : m ∈ ⨆ (V : Submodule R M) (_ : P V), V) :
    ∃ V₀ : Submodule R M, P V₀ ∧ m ∈ V₀ ∧ (⨆ (V : Submodule R M) (_ : P V), V) = V₀ := by
  by_cases hex : ∃ V₀ : Submodule R M, P V₀
  · obtain ⟨V₀, hV₀⟩ := hex
    have hle : (⨆ (V : Submodule R M) (_ : P V), V) ≤ V₀ :=
      iSup_le fun V => iSup_le fun hV => (huniq V V₀ hV hV₀).le
    have hge : V₀ ≤ ⨆ (V : Submodule R M) (_ : P V), V := le_iSup₂ (f := fun (V : Submodule R M) (_ : P V) => V) V₀ hV₀
    exact ⟨V₀, hV₀, hle h, le_antisymm hle hge⟩
  · have hbot : (⨆ (V : Submodule R M) (_ : P V), V) = ⊥ :=
      le_bot_iff.mp (iSup_le fun V => iSup_le fun hV => (hex ⟨V, hV⟩).elim)
    rw [hbot, Submodule.mem_bot] at h
    exact (hm h).elim

private theorem iSup_le_of_mem (P : Submodule R M → Prop)
    (huniq : ∀ V₁ V₂ : Submodule R M, P V₁ → P V₂ → V₁ = V₂) {V₀ : Submodule R M} (hV₀ : P V₀) :
    (⨆ (V : Submodule R M) (_ : P V), V) ≤ V₀ :=
  iSup_le fun V => iSup_le fun hV => (huniq V V₀ hV hV₀).le

end SubsingletonSup

end

section

open IsDedekindDomain NumberField

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀ normSq_firstRowℂ_of_mem archWeightOneℝ archWeightCharℝ archMatrixUpdate archMatrixUpdate_apply_self archMatrixUpdate_apply_of_ne archComponent_archGLIncl_self adelicArchGLIncl glArch_adelicArchGLIncl glFin_adelicArchGLIncl CarrierPins productionPinsOf AdelicGL2 rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal HeckeEigensystem.toRawCentral_ofRawCentral HeckeEigensystem.AgreesAwayFromFinite.of_toRawCentral SmoothCuspRealizationAt finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff HeckeEigensystem HeckeEigensystem.AgreesAwayFromFinite CuspidalConstituent.IsCuspConstituent CuspidalConstituent.CuspConstituentMeets CuspidalConstituent.levelInvariantSubmodule IsIsotypicCuspFormAt typeSubmodule comp_mul_mem_typeSubmodule_of_commute charRep apply_mul_eq_of_mem_typeSubmodule_charRep_dual ArchRepAt ArchRepAt.ofChar rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily ArchTypeFamily.ofChar archCutSubmodule mem_archCutSubmodule_iff IsArchBiFinite archRowIsometryInclAt₀ glFin_rowIsometryInclAt₀ archFactorDualTypeSubmoduleAt IsArchFactorBiFinite IsArchBiFinite.of_factorization IsGenuineCuspRealizationAt rightConv rightConv_apply archEntries IsArchTestFactor IsFinTestFactor IsFactorizableTestFn glBorelOf borelSpace_glBorelOf archHaarK CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite IsIsotypicCuspFormAt.of_le_of_subset SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent"
p2m_open "AutomorphicForm"
namespace RawRescalingTransport

variable {F : Type} [Field F] [NumberField F]

private theorem toRawCentral_ofRawCentral_b (Θ : HeckeEigensystem F ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    Θ.ofRawCentral.toRawCentral.b v = Θ.b v := by
  rw [HeckeEigensystem.toRawCentral_ofRawCentral]

private noncomputable def reindex {pins : CarrierPins F} {Θ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F pins Θ) :
    SmoothCuspRealizationAt F pins Θ.ofRawCentral.toRawCentral where
  toFun := R.toFun
  exists_ne_zero := R.exists_ne_zero
  centralChar := R.centralChar
  smoothCusp := R.smoothCusp
  level_invariant := R.level_invariant
  exceptionalSet := R.exceptionalSet
  hecke_eigen := R.hecke_eigen
  central_eigen v hv g := by
    rw [toRawCentral_ofRawCentral_b]
    exact R.central_eigen v hv g

private theorem reindex_toFun {pins : CarrierPins F} {Θ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F pins Θ) : (reindex R).toFun = R.toFun := rfl

private theorem reindex_centralChar {pins : CarrierPins F} {Θ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F pins Θ) : (reindex R).centralChar = R.centralChar := rfl

private theorem reindex_exceptionalSet {pins : CarrierPins F} {Θ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F pins Θ) : (reindex R).exceptionalSet = R.exceptionalSet := rfl

private theorem exists_realization_toRawCentral {pins : CarrierPins F} {Θ : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F pins Θ) :
    ∃ (Φ : HeckeEigensystem F ℂ) (R' : SmoothCuspRealizationAt F pins Φ.toRawCentral),
      R'.toFun = R.toFun ∧ R'.centralChar = R.centralChar ∧ R'.exceptionalSet = R.exceptionalSet ∧
        Φ.level = Θ.level :=
  ⟨Θ.ofRawCentral, reindex R, rfl, rfl, rfl, rfl⟩

end RawRescalingTransport
end AutomorphicForm

end

section

open IsDedekindDomain NumberField

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀ normSq_firstRowℂ_of_mem archWeightOneℝ archWeightCharℝ archMatrixUpdate archMatrixUpdate_apply_self archMatrixUpdate_apply_of_ne archComponent_archGLIncl_self adelicArchGLIncl glArch_adelicArchGLIncl glFin_adelicArchGLIncl CarrierPins productionPinsOf AdelicGL2 rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal HeckeEigensystem.toRawCentral_ofRawCentral HeckeEigensystem.AgreesAwayFromFinite.of_toRawCentral SmoothCuspRealizationAt finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff HeckeEigensystem HeckeEigensystem.AgreesAwayFromFinite CuspidalConstituent.IsCuspConstituent CuspidalConstituent.CuspConstituentMeets CuspidalConstituent.levelInvariantSubmodule IsIsotypicCuspFormAt typeSubmodule comp_mul_mem_typeSubmodule_of_commute charRep apply_mul_eq_of_mem_typeSubmodule_charRep_dual ArchRepAt ArchRepAt.ofChar rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily ArchTypeFamily.ofChar archCutSubmodule mem_archCutSubmodule_iff IsArchBiFinite archRowIsometryInclAt₀ glFin_rowIsometryInclAt₀ archFactorDualTypeSubmoduleAt IsArchFactorBiFinite IsArchBiFinite.of_factorization IsGenuineCuspRealizationAt rightConv rightConv_apply archEntries IsArchTestFactor IsFinTestFactor IsFactorizableTestFn glBorelOf borelSpace_glBorelOf archHaarK CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite IsIsotypicCuspFormAt.of_le_of_subset SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent"
p2m_open "AutomorphicForm"
namespace DatumTransport

variable {F : Type} [Field F] [NumberField F]

private theorem isIsotypicCuspFormAt_of_forall_eq {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 F)} {S S' : Finset (HeightOneSpectrum (𝓞 F))} {Ψ Ψ' : HeckeEigensystem F ℂ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : IsIsotypicCuspFormAt F pins ξ N S Ψ φ) (hS : S ⊆ S')
    (ha : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' → Ψ'.a v = Ψ.a v)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' → Ψ'.toRawCentral.b v = Ψ.toRawCentral.b v) :
    IsIsotypicCuspFormAt F pins ξ N S' Ψ' φ where
  smoothCusp := h.smoothCusp
  continuous := h.continuous
  level_invariant := h.level_invariant
  hecke_eigen v hv := by
    rw [ha v hv]
    exact h.hecke_eigen v (fun hvS => hv (hS hvS))
  central_eigen v hv g := by
    rw [hb v hv]
    exact h.central_eigen v (fun hvS => hv (hS hvS)) g

open scoped Classical in

private theorem exists_finset_isIsotypicCuspFormAt_of_agreesAwayFromFinite {pins : CarrierPins F}
    {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))}
    {Ψ Ψ' : HeckeEigensystem F ℂ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsIsotypicCuspFormAt F pins ξ N S Ψ φ) (hag : Ψ'.AgreesAwayFromFinite Ψ) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), IsIsotypicCuspFormAt F pins ξ N (S ∪ S₀) Ψ' φ := by
  obtain ⟨S₀, hS₀⟩ := hag.toRawCentral
  refine ⟨S₀, isIsotypicCuspFormAt_of_forall_eq h Finset.subset_union_left ?_ ?_⟩
  · intro v hv
    exact (hS₀ v (fun hv₀ => hv (Finset.mem_union_right S hv₀))).1
  · intro v hv
    exact (hS₀ v (fun hv₀ => hv (Finset.mem_union_right S hv₀))).2

private theorem agrees_symm {Ψ Ψ' : HeckeEigensystem F ℂ} (h : Ψ.AgreesAwayFromFinite Ψ') :
    Ψ'.AgreesAwayFromFinite Ψ := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun v hv => ⟨(hS v hv).1.symm, (hS v hv).2.symm⟩⟩

open scoped Classical in

private theorem agrees_trans {Ψ₁ Ψ₂ Ψ₃ : HeckeEigensystem F ℂ} (h₁ : Ψ₁.AgreesAwayFromFinite Ψ₂)
    (h₂ : Ψ₂.AgreesAwayFromFinite Ψ₃) : Ψ₁.AgreesAwayFromFinite Ψ₃ := by
  obtain ⟨S, hS⟩ := h₁
  obtain ⟨S', hS'⟩ := h₂
  refine ⟨S ∪ S', fun v hv => ?_⟩
  have hv₁ : v ∉ S := fun h => hv (Finset.mem_union_left S' h)
  have hv₂ : v ∉ S' := fun h => hv (Finset.mem_union_right S h)
  exact ⟨(hS v hv₁).1.trans (hS' v hv₂).1, (hS v hv₁).2.trans (hS' v hv₂).2⟩

open scoped Classical in

private theorem exists_common_datum {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    (hmono : ∀ {N N' : Ideal (𝓞 F)}, N' ≤ N → N' ≠ ⊥ → ∀ {S S' : Finset (HeightOneSpectrum (𝓞 F))},
      S ⊆ S' → (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' → ¬ v.asIdeal ∣ N') →
      ∀ (Ψ : HeckeEigensystem F ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ},
        IsIsotypicCuspFormAt F pins ξ N S Ψ φ → IsIsotypicCuspFormAt F pins ξ N' S' Ψ φ)
    {N₁ N₂ : Ideal (𝓞 F)} (h₁ : N₁ ≠ ⊥) (h₂ : N₂ ≠ ⊥) {S₁ S₂ : Finset (HeightOneSpectrum (𝓞 F))}
    {Ψ₁ Ψ₂ : HeckeEigensystem F ℂ} (hag : Ψ₂.AgreesAwayFromFinite Ψ₁)
    {V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (m₁ : CuspidalConstituent.CuspConstituentMeets F pins ξ N₁ S₁ Ψ₁ V₁)
    (m₂ : CuspidalConstituent.CuspConstituentMeets F pins ξ N₂ S₂ Ψ₂ V₂) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), N₁ * N₂ ≠ ⊥ ∧
      CuspidalConstituent.CuspConstituentMeets F pins ξ (N₁ * N₂) S Ψ₁ V₁ ∧
      CuspidalConstituent.CuspConstituentMeets F pins ξ (N₁ * N₂) S Ψ₁ V₂ := by
  have hN : N₁ * N₂ ≠ ⊥ := fun h => (Ideal.mul_eq_bot.1 h).elim h₁ h₂
  obtain ⟨φ₁, hφ₁V, hφ₁0, hφ₁⟩ := m₁
  obtain ⟨φ₂, hφ₂V, hφ₂0, hφ₂⟩ := m₂
  obtain ⟨S₀, hφ₂'⟩ := exists_finset_isIsotypicCuspFormAt_of_agreesAwayFromFinite hφ₂ (agrees_symm hag)
  set P : Finset (HeightOneSpectrum (𝓞 F)) := (Ideal.finite_factors hN).toFinset with hP
  refine ⟨S₁ ∪ (S₂ ∪ S₀) ∪ P, hN, ⟨φ₁, hφ₁V, hφ₁0, ?_⟩, ⟨φ₂, hφ₂V, hφ₂0, ?_⟩⟩
  · refine hmono (Ideal.mul_le_inf.trans inf_le_left) hN ?_ ?_ Ψ₁ hφ₁
    · exact Finset.subset_union_left.trans Finset.subset_union_left
    · intro v hv hdvd
      exact hv (Finset.mem_union_right _ ((Ideal.finite_factors hN).mem_toFinset.2 hdvd))
  · refine hmono (Ideal.mul_le_inf.trans inf_le_right) hN ?_ ?_ Ψ₁ hφ₂'
    · exact Finset.subset_union_right.trans Finset.subset_union_left
    · intro v hv hdvd
      exact hv (Finset.mem_union_right _ ((Ideal.finite_factors hN).mem_toFinset.2 hdvd))

end DatumTransport
end AutomorphicForm

end

section

p2m_open "NumberField AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm"

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.toFn_mk AdelicFnCarrier.mk_toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_zero AdelicFnCarrier.toFn_add AdelicFnCarrier.toFn_csmul AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def IsIrreducibleGLRep exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace AwayCarrier
p2m_open "LocalNewvector"

private def carrierToFn : AdelicFnCarrier ℚ →ₗ[ℂ] (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) where
  toFun := AdelicFnCarrier.toFn
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable abbrev stableAction (q : ℕ) [Fact q.Prime] (Z : Submodule ℂ (AdelicFnCarrier ℚ))
    (hZst : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ ψ ∈ Z, x • ψ ∈ Z) : DistribMulAction (GL (Fin 2) ℚ_[q]) ↥Z where
  smul x z := ⟨x • z.1, hZst x z.1 z.2⟩
  one_smul z := Subtype.ext (one_smul _ z.1)
  mul_smul x y z := Subtype.ext (mul_smul x y z.1)
  smul_zero x := Subtype.ext (smul_zero x)
  smul_add x a b := Subtype.ext (smul_add x a.1 b.1)

private theorem stableAction_coe_smul (q : ℕ) [Fact q.Prime] (Z : Submodule ℂ (AdelicFnCarrier ℚ))
    (hZst : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ ψ ∈ Z, x • ψ ∈ Z) (x : GL (Fin 2) ℚ_[q]) (z : ↥Z) :
    letI := stableAction q Z hZst
    ((x • z : ↥Z) : AdelicFnCarrier ℚ) = x • (z : AdelicFnCarrier ℚ) := by
  letI := stableAction q Z hZst
  rfl

private theorem stableAction_smulCommClass (q : ℕ) [Fact q.Prime] (Z : Submodule ℂ (AdelicFnCarrier ℚ))
    (hZst : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ ψ ∈ Z, x • ψ ∈ Z) :
    letI := stableAction q Z hZst
    SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ ↥Z :=
  letI := stableAction q Z hZst
  ⟨fun x c z => Subtype.ext (smul_comm x c z.1)⟩

private theorem span_padic_stable (q : ℕ) [Fact q.Prime] (A : Set (AdelicFnCarrier ℚ))
    (hA : ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ), ∀ χ ∈ A, g • χ ∈ A) (x : GL (Fin 2) ℚ_[q]) :
    ∀ ψ ∈ Submodule.span ℂ A, x • ψ ∈ Submodule.span ℂ A := by
  intro ψ hψ
  rw [AdelicFnCarrier.padic_smul_def]
  generalize (AdelicDock.padicToAdelic q x : AdelicGL2 (𝓞 ℚ) ℚ) = g
  refine Submodule.span_induction (p := fun φ _ => g • φ ∈ Submodule.span ℂ A) ?_ ?_ ?_ ?_ hψ
  · intro χ hχ
    exact Submodule.subset_span (hA g χ hχ)
  · show g • (0 : AdelicFnCarrier ℚ) ∈ Submodule.span ℂ A
    rw [smul_zero]
    exact Submodule.zero_mem _
  · intro φ₁ φ₂ _ _ h₁ h₂
    show g • (φ₁ + φ₂) ∈ Submodule.span ℂ A
    rw [smul_add]
    exact Submodule.add_mem _ h₁ h₂
  · intro c φ _ h
    show g • (c • φ) ∈ Submodule.span ℂ A
    rw [smul_comm]
    exact Submodule.smul_mem _ c h

private theorem codRestrict_smul (q : ℕ) [Fact q.Prime] (Z : Submodule ℂ (AdelicFnCarrier ℚ))
    (hZst : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ ψ ∈ Z, x • ψ ∈ Z) {W : Type} [AddCommGroup W] [Module ℂ W]
    [DistribMulAction (GL (Fin 2) ℚ_[q]) W] (f : W →ₗ[ℂ] AdelicFnCarrier ℚ)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (w : W), f (x • w) = x • f w) (hrange : ∀ w, f w ∈ Z)
    (x : GL (Fin 2) ℚ_[q]) (w : W) :
    letI := stableAction q Z hZst
    f.codRestrict Z hrange (x • w) = x • f.codRestrict Z hrange w := by
  letI := stableAction q Z hZst
  apply Subtype.ext
  show f (x • w) = x • f w
  exact hf x w

private theorem codRestrict_coe (Z : Submodule ℂ (AdelicFnCarrier ℚ)) {W : Type} [AddCommGroup W]
    [Module ℂ W] (f : W →ₗ[ℂ] AdelicFnCarrier ℚ) (hrange : ∀ w, f w ∈ Z) (w : W) :
    ((f.codRestrict Z hrange w : ↥Z) : AdelicFnCarrier ℚ) = f w := rfl

end LocalNewvector.AwayCarrier

end

section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀ normSq_firstRowℂ_of_mem archWeightOneℝ archWeightCharℝ archMatrixUpdate archMatrixUpdate_apply_self archMatrixUpdate_apply_of_ne archComponent_archGLIncl_self adelicArchGLIncl glArch_adelicArchGLIncl glFin_adelicArchGLIncl CarrierPins productionPinsOf AdelicGL2 rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal HeckeEigensystem.toRawCentral_ofRawCentral HeckeEigensystem.AgreesAwayFromFinite.of_toRawCentral SmoothCuspRealizationAt finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff HeckeEigensystem HeckeEigensystem.AgreesAwayFromFinite CuspidalConstituent.IsCuspConstituent CuspidalConstituent.CuspConstituentMeets CuspidalConstituent.levelInvariantSubmodule IsIsotypicCuspFormAt typeSubmodule comp_mul_mem_typeSubmodule_of_commute charRep apply_mul_eq_of_mem_typeSubmodule_charRep_dual ArchRepAt ArchRepAt.ofChar rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily ArchTypeFamily.ofChar archCutSubmodule mem_archCutSubmodule_iff IsArchBiFinite archRowIsometryInclAt₀ glFin_rowIsometryInclAt₀ archFactorDualTypeSubmoduleAt IsArchFactorBiFinite IsArchBiFinite.of_factorization IsGenuineCuspRealizationAt rightConv rightConv_apply archEntries IsArchTestFactor IsFinTestFactor IsFactorizableTestFn glBorelOf borelSpace_glBorelOf archHaarK CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite IsIsotypicCuspFormAt.of_le_of_subset SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent"
namespace SOTwoFourier
p2m_open "AutomorphicForm"

private scoped instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

private theorem norm_archWeightOne (k : AutomorphicForm.rowIsometrySubgroup₀ ℝ) :
    ‖(AutomorphicForm.archWeightOneℝ k : ℂ)‖ = 1 := by
  have h : Complex.normSq (AutomorphicForm.archWeightOneℝ k : ℂ) = 1 :=
    AutomorphicForm.normSq_firstRowℂ_of_mem k.2
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (AutomorphicForm.archWeightOneℝ k : ℂ)]

private noncomputable def toCircleHom : AutomorphicForm.rowIsometrySubgroup₀ ℝ →* Circle where
  toFun k := ⟨(AutomorphicForm.archWeightOneℝ k : ℂ), mem_sphere_zero_iff_norm.mpr (norm_archWeightOne k)⟩
  map_one' := by ext; simp
  map_mul' k k' := by ext; simp

private theorem coe_toCircleHom (k : AutomorphicForm.rowIsometrySubgroup₀ ℝ) :
    ((toCircleHom k : Circle) : ℂ) = (AutomorphicForm.archWeightOneℝ k : ℂ) := rfl

private theorem re_toCircleHom (k : AutomorphicForm.rowIsometrySubgroup₀ ℝ) :
    ((toCircleHom k : Circle) : ℂ).re =
      ((k : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := rfl

private theorem im_toCircleHom (k : AutomorphicForm.rowIsometrySubgroup₀ ℝ) :
    ((toCircleHom k : Circle) : ℂ).im =
      ((k : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := rfl

private theorem toCircleHom_injective : Function.Injective toCircleHom := by
  intro k k' h
  obtain ⟨h10, h11, -⟩ := AutomorphicForm.entries_of_mem_rowIsometrySubgroup₀ k.2
  obtain ⟨h10', h11', -⟩ := AutomorphicForm.entries_of_mem_rowIsometrySubgroup₀ k'.2
  have hre := congrArg (fun z : Circle => (z : ℂ).re) h
  have him := congrArg (fun z : Circle => (z : ℂ).im) h
  simp only [re_toCircleHom, im_toCircleHom] at hre him
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact hre
  · exact him
  · show ((k : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 =
      ((k' : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0
    rw [h10, h10', him]
  · show ((k : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 =
      ((k' : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1
    rw [h11, h11', hre]

private noncomputable def rotMat (z : Circle) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(z : ℂ).re, (z : ℂ).im; -(z : ℂ).im, (z : ℂ).re]

private theorem re_sq_add_im_sq (z : Circle) : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
  have h : Complex.normSq (z : ℂ) = 1 := by rw [Complex.normSq_eq_norm_sq, Circle.norm_coe, one_pow]
  rw [Complex.normSq_apply] at h
  nlinarith [h]

private theorem det_rotMat (z : Circle) : (rotMat z).det = 1 := by
  rw [rotMat, Matrix.det_fin_two_of]
  nlinarith [re_sq_add_im_sq z]

private noncomputable def rotGL (z : Circle) : Matrix.GeneralLinearGroup (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotMat z) (by rw [det_rotMat]; exact one_ne_zero)

private theorem coe_rotGL (z : Circle) :
    ((rotGL z : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotMat z := rfl

private theorem rotGL_mem (z : Circle) : rotGL z ∈ AutomorphicForm.rowIsometrySubgroup₀ ℝ := by
  rw [AutomorphicForm.mem_rowIsometrySubgroup₀_iff]
  refine ⟨by rw [coe_rotGL, det_rotMat], by rw [coe_rotGL, det_rotMat, norm_one], fun x y => ?_⟩
  rw [coe_rotGL]
  simp only [rotMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Real.norm_eq_abs,
    sq_abs]
  nlinarith [re_sq_add_im_sq z]

private theorem toCircleHom_rotGL (z : Circle) : toCircleHom ⟨rotGL z, rotGL_mem z⟩ = z := by
  ext
  apply Complex.ext
  · rw [re_toCircleHom, coe_rotGL]; simp [rotMat]
  · rw [im_toCircleHom, coe_rotGL]; simp [rotMat]

private theorem toCircleHom_surjective : Function.Surjective toCircleHom := fun z =>
  ⟨⟨rotGL z, rotGL_mem z⟩, toCircleHom_rotGL z⟩

private noncomputable def circleEquiv : AutomorphicForm.rowIsometrySubgroup₀ ℝ ≃* Circle :=
  MulEquiv.ofBijective toCircleHom ⟨toCircleHom_injective, toCircleHom_surjective⟩

private theorem circleEquiv_apply (k : AutomorphicForm.rowIsometrySubgroup₀ ℝ) :
    circleEquiv k = toCircleHom k := rfl

private theorem circleEquiv_symm_apply (z : Circle) : circleEquiv.symm z = ⟨rotGL z, rotGL_mem z⟩ := by
  apply circleEquiv.injective
  rw [MulEquiv.apply_symm_apply, circleEquiv_apply, toCircleHom_rotGL]

private theorem mul_comm' (k k' : AutomorphicForm.rowIsometrySubgroup₀ ℝ) : k * k' = k' * k :=
  circleEquiv.injective (by rw [map_mul, map_mul, mul_comm])

private theorem continuous_entries : Continuous fun k : AutomorphicForm.rowIsometrySubgroup₀ ℝ =>
    ((k : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) :=
  Units.continuous_val.comp continuous_subtype_val

private theorem continuous_coe_toCircleHom :
    Continuous fun k : AutomorphicForm.rowIsometrySubgroup₀ ℝ => ((toCircleHom k : Circle) : ℂ) := by
  have h : (fun k : AutomorphicForm.rowIsometrySubgroup₀ ℝ => ((toCircleHom k : Circle) : ℂ)) =
      fun k : AutomorphicForm.rowIsometrySubgroup₀ ℝ =>
      ((((k : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) +
        ((((k : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ) * Complex.I := by
    funext k
    rw [coe_toCircleHom]
    exact Complex.mk_eq_add_mul_I _ _
  rw [h]
  exact (Complex.continuous_ofReal.comp (continuous_entries.matrix_elem 0 0)).add
    ((Complex.continuous_ofReal.comp (continuous_entries.matrix_elem 0 1)).mul continuous_const)

private theorem continuous_toCircleHom : Continuous toCircleHom :=
  continuous_induced_rng.2 continuous_coe_toCircleHom

private theorem continuous_rotMat : Continuous rotMat := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [rotMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> fun_prop

private theorem coe_rotGL_inv (z : Circle) :
    (((rotGL z)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotMat z⁻¹ := by
  have h : ((⟨rotGL z, rotGL_mem z⟩ : AutomorphicForm.rowIsometrySubgroup₀ ℝ)⁻¹ :
      AutomorphicForm.rowIsometrySubgroup₀ ℝ) = ⟨rotGL z⁻¹, rotGL_mem z⁻¹⟩ := by
    rw [← circleEquiv_symm_apply z, ← circleEquiv_symm_apply z⁻¹, map_inv]
  exact congrArg (fun k : AutomorphicForm.rowIsometrySubgroup₀ ℝ =>
    ((k : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) h

private theorem continuous_circleEquiv_symm : Continuous circleEquiv.symm := by
  have hfun : ⇑circleEquiv.symm =
      fun z : Circle => (⟨rotGL z, rotGL_mem z⟩ : AutomorphicForm.rowIsometrySubgroup₀ ℝ) :=
    funext circleEquiv_symm_apply
  rw [hfun]
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · exact continuous_rotMat.congr fun _ => rfl
  · exact (continuous_rotMat.comp continuous_inv).congr fun z => (coe_rotGL_inv z).symm

private noncomputable def param : AddCircle (2 * Real.pi) → AutomorphicForm.rowIsometrySubgroup₀ ℝ := fun t =>
  circleEquiv.symm (AddCircle.homeomorphCircle' t)

private theorem continuous_param : Continuous param :=
  continuous_circleEquiv_symm.comp AddCircle.homeomorphCircle'.continuous

private theorem param_add (s t : AddCircle (2 * Real.pi)) : param (s + t) = param s * param t := by
  simp only [param, AddCircle.homeomorphCircle'_apply]
  exact (congrArg circleEquiv.symm (Real.Angle.toCircle_add s t)).trans (map_mul _ _ _)

private theorem param_surjective : Function.Surjective param := fun k =>
  ⟨AddCircle.homeomorphCircle'.symm (circleEquiv k), by
    simp only [param, Homeomorph.apply_symm_apply, MulEquiv.symm_apply_apply]⟩

private theorem archWeightOne_param (t : AddCircle (2 * Real.pi)) :
    (AutomorphicForm.archWeightOneℝ (param t) : ℂ) = ((AddCircle.homeomorphCircle' t : Circle) : ℂ) := by
  have h : circleEquiv (param t) = AddCircle.homeomorphCircle' t := by
    simp only [param, MulEquiv.apply_symm_apply]
  rw [← h, circleEquiv_apply, coe_toCircleHom]

private theorem fourier_eq_zpow (m : ℤ) (t : AddCircle (2 * Real.pi)) :
    (fourier m t : ℂ) = ((AddCircle.homeomorphCircle' t : Circle) : ℂ) ^ m := by
  induction t using QuotientAddGroup.induction_on with
  | H x =>
    rw [fourier_coe_apply, AddCircle.homeomorphCircle'_apply_mk, Circle.coe_exp,
      ← Complex.exp_int_mul]
    congr 1
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp

private theorem weightChar_inv_param (n : ℤ) (t : AddCircle (2 * Real.pi)) :
    (((AutomorphicForm.archWeightCharℝ n (param t))⁻¹ : ℂˣ) : ℂ) = fourier (-n) t := by
  rw [fourier_eq_zpow, ← archWeightOne_param, AutomorphicForm.archWeightCharℝ, MonoidHom.comp_apply,
    zpowGroupHom_apply, ← zpow_neg, Units.val_zpow_eq_zpow_val]

private theorem continuous_weightChar_inv (n : ℤ) :
    Continuous fun k : AutomorphicForm.rowIsometrySubgroup₀ ℝ =>
      (((AutomorphicForm.archWeightCharℝ n k)⁻¹ : ℂˣ) : ℂ) := by
  have h : (fun k : AutomorphicForm.rowIsometrySubgroup₀ ℝ => (((AutomorphicForm.archWeightCharℝ n k)⁻¹ : ℂˣ) : ℂ))
      = fun k => ((toCircleHom k : Circle) : ℂ) ^ (-n) := by
    funext k
    rw [coe_toCircleHom, AutomorphicForm.archWeightCharℝ, MonoidHom.comp_apply, zpowGroupHom_apply, ← zpow_neg,
      Units.val_zpow_eq_zpow_val]
  rw [h]
  exact continuous_coe_toCircleHom.zpow₀ (-n) fun k => Or.inl (Circle.coe_ne_zero _)

private noncomputable scoped instance : MeasurableSpace (AutomorphicForm.rowIsometrySubgroup₀ ℝ) := borel _

private scoped instance : BorelSpace (AutomorphicForm.rowIsometrySubgroup₀ ℝ) := ⟨rfl⟩

private theorem measurable_param : Measurable param := continuous_param.measurable

private noncomputable def haarSO2 : MeasureTheory.Measure (AutomorphicForm.rowIsometrySubgroup₀ ℝ) :=
  MeasureTheory.Measure.map param AddCircle.haarAddCircle

private scoped instance : MeasureTheory.IsProbabilityMeasure haarSO2 :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_param.aemeasurable

private scoped instance : haarSO2.IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨s, rfl⟩ := param_surjective g
  rw [haarSO2, MeasureTheory.Measure.map_map (measurable_const_mul _) measurable_param]
  have h : ((param s * ·) ∘ param) = param ∘ (s + ·) := by
    funext t
    simp only [Function.comp_apply, param_add]
  rw [h, ← MeasureTheory.Measure.map_map measurable_param (measurable_const_add s),
    MeasureTheory.map_add_left_eq_self]

private scoped instance : haarSO2.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h : (· * g) = (g * ·) := funext fun k => mul_comm' k g
  rw [h]
  exact MeasureTheory.map_mul_left_eq_self haarSO2 g

private theorem exists_integral_weightChar_inv_mul_ne_zero (F : AutomorphicForm.rowIsometrySubgroup₀ ℝ → ℂ)
    (hF : Continuous F) (hne : F ≠ 0) :
    ∃ n : ℤ, ∫ k, (((AutomorphicForm.archWeightCharℝ n k)⁻¹ : ℂˣ) : ℂ) * F k ∂haarSO2 ≠ 0 := by
  by_contra hall
  push_neg at hall
  let f : C(AddCircle (2 * Real.pi), ℂ) := ⟨fun t => F (param t), hF.comp continuous_param⟩
  have hcoeff : ∀ n : ℤ, fourierCoeff (f : AddCircle (2 * Real.pi) → ℂ) n = 0 := by
    intro n
    have h := hall n
    rw [haarSO2, MeasureTheory.integral_map measurable_param.aemeasurable ?_] at h
    · rw [fourierCoeff, ← h]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only [ContinuousMap.coe_mk, smul_eq_mul, weightChar_inv_param, f]
    · exact ((continuous_weightChar_inv n).mul hF).aestronglyMeasurable
  have hLp : (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ f) = 0 := by
    apply fourierBasis.repr.injective
    ext n
    simp only [fourierBasis_repr, fourierCoeff_toLp, hcoeff, map_zero, lp.coeFn_zero, Pi.zero_apply]
  have hf : f = 0 := (ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle)
    (by rw [hLp, map_zero])
  apply hne
  funext k
  obtain ⟨t, rfl⟩ := param_surjective k
  have ht := congrArg (fun g : C(AddCircle (2 * Real.pi), ℂ) => g t) hf
  simpa [f] using ht

end AutomorphicForm.SOTwoFourier
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

section

namespace ModularTrivial

open scoped Pointwise

private theorem map_mul_right_eq_modular_smul {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G)
    [μ.IsHaarMeasure] [μ.Regular] (g : G) :
    MeasureTheory.Measure.map (· * g) μ = MeasureTheory.Measure.modularCharacterFun g • μ := by
  haveI : (MeasureTheory.Measure.map (· * g) μ).Regular := by
    have h := MeasureTheory.Measure.Regular.map (μ := μ) (Homeomorph.mulRight g)
    rwa [Homeomorph.coe_mulRight] at h
  rw [MeasureTheory.Measure.modularCharacterFun_eq_haarScalarFactor μ g]
  exact MeasureTheory.Measure.isMulLeftInvariant_eq_smul_of_regular _ μ

private theorem modularCharacterFun_le_one {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (g : G) (S : Set G) (hS : IsCompact S) (hinv : ∀ n : ℕ, g⁻¹ ^ n ∈ S) :
    MeasureTheory.Measure.modularCharacterFun g ≤ 1 := by
  borelize G
  by_contra hlt
  set μ : MeasureTheory.Measure G := MeasureTheory.Measure.haar
  obtain ⟨D, hD1, -, hDc⟩ := LocallyCompactSpace.local_compact_nhds (1 : G) Set.univ Filter.univ_mem

  have hU : IsOpen (interior D) := isOpen_interior
  have hDpos : 0 < μ (interior D) := hU.measure_pos μ ⟨1, mem_interior_iff_mem_nhds.mpr hD1⟩
  have hDfin : μ (interior D) < ⊤ := lt_of_le_of_lt (MeasureTheory.measure_mono interior_subset) hDc.measure_lt_top
  have hM : μ (D * S) < ⊤ := (hDc.mul hS).measure_lt_top
  set c : NNReal := MeasureTheory.Measure.modularCharacterFun g
  have hlt' : 1 < c := not_le.mp hlt
  have hbound : ∀ n : ℕ, ((c ^ n : NNReal) : ENNReal) * μ (interior D) ≤ μ (D * S) := by
    intro n
    have hmap := map_mul_right_eq_modular_smul μ (g ^ n)
    have hcn : MeasureTheory.Measure.modularCharacterFun (g ^ n) = c ^ n :=
      map_pow MeasureTheory.Measure.modularCharacter g n
    rw [hcn] at hmap
    have hpre : (fun x : G => x * g ^ n) ⁻¹' interior D ⊆ D * S := by
      intro x hx
      have hx' : x * g ^ n ∈ D := interior_subset hx
      refine ⟨x * g ^ n, hx', g⁻¹ ^ n, hinv n, ?_⟩
      show x * g ^ n * g⁻¹ ^ n = x
      rw [inv_pow, mul_assoc, mul_inv_cancel, mul_one]
    have h1 : (MeasureTheory.Measure.map (· * g ^ n) μ) (interior D) = μ ((fun x : G => x * g ^ n) ⁻¹' interior D) :=
      MeasureTheory.Measure.map_apply (measurable_mul_const (g ^ n)) hU.measurableSet
    rw [hmap, MeasureTheory.Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    calc ((c ^ n : NNReal) : ENNReal) * μ (interior D) = μ ((fun x : G => x * g ^ n) ⁻¹' interior D) := h1
      _ ≤ μ (D * S) := MeasureTheory.measure_mono hpre
  have hB : ∀ n : ℕ, c ^ n ≤ (μ (D * S) / μ (interior D)).toNNReal := by
    intro n
    have h := (ENNReal.le_div_iff_mul_le (Or.inl hDpos.ne') (Or.inl hDfin.ne)).mpr (hbound n)
    have hfin : μ (D * S) / μ (interior D) ≠ ⊤ := (ENNReal.div_lt_top hM.ne hDpos.ne').ne
    have h' := ENNReal.toNNReal_mono hfin h
    rwa [ENNReal.toNNReal_coe] at h'
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (μ (D * S) / μ (interior D)).toNNReal hlt'
  exact (not_lt.mpr (hB n)) hn

private theorem modularCharacterFun_eq_one {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] (g : G) (S : Set G) (hS : IsCompact S) (hpow : ∀ n : ℕ, g ^ n ∈ S)
    (hinv : ∀ n : ℕ, g⁻¹ ^ n ∈ S) : MeasureTheory.Measure.modularCharacterFun g = 1 := by
  refine le_antisymm (modularCharacterFun_le_one g S hS hinv) ?_
  have hle : MeasureTheory.Measure.modularCharacterFun g⁻¹ ≤ 1 :=
    modularCharacterFun_le_one g⁻¹ S hS (by simpa only [inv_inv] using hpow)
  have hmul : MeasureTheory.Measure.modularCharacterFun g * MeasureTheory.Measure.modularCharacterFun g⁻¹ = 1 := by
    rw [← MeasureTheory.Measure.modularCharacterFun_map_mul, mul_inv_cancel,
      MeasureTheory.Measure.modularCharacterFun_map_one]
  calc (1 : NNReal) = MeasureTheory.Measure.modularCharacterFun g * MeasureTheory.Measure.modularCharacterFun g⁻¹ :=
        hmul.symm
    _ ≤ MeasureTheory.Measure.modularCharacterFun g * 1 := mul_le_mul_right hle _
    _ = MeasureTheory.Measure.modularCharacterFun g := mul_one _

private theorem _root_.ModularTrivial.map_mul_right_eq_self {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G)
    [μ.IsHaarMeasure] [μ.Regular] (g : G) (S : Set G) (hS : IsCompact S) (hpow : ∀ n : ℕ, g ^ n ∈ S)
    (hinv : ∀ n : ℕ, g⁻¹ ^ n ∈ S) : MeasureTheory.Measure.map (· * g) μ = μ := by
  rw [map_mul_right_eq_modular_smul μ g, modularCharacterFun_eq_one g S hS hpow hinv, one_smul]

p2m_export "ModularTrivial" "map_mul_right_eq_self"

private theorem integral_mul_right_eq_self {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G)
    [μ.IsHaarMeasure] [μ.Regular] (g : G) (S : Set G) (hS : IsCompact S) (hpow : ∀ n : ℕ, g ^ n ∈ S)
    (hinv : ∀ n : ℕ, g⁻¹ ^ n ∈ S) (f : G → ℂ) : ∫ x, f (x * g) ∂μ = ∫ x, f x ∂μ := by
  have h := MeasureTheory.integral_map_equiv (μ := μ) (MeasurableEquiv.mulRight g) f
  rw [MeasurableEquiv.coe_mulRight] at h
  rw [map_mul_right_eq_self μ g S hS hpow hinv] at h
  exact h.symm

private theorem integral_mul_right_eq_self_of_range {G H : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [CompactSpace H] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (j : H →* G) (hj : Continuous j) (k : H) (f : G → ℂ) : ∫ x, f (x * j k) ∂μ = ∫ x, f x ∂μ :=
  integral_mul_right_eq_self μ (j k) (Set.range j) (isCompact_range hj)
    (fun n => ⟨k ^ n, map_pow j k n⟩) (fun n => ⟨k⁻¹ ^ n, by rw [map_pow, map_inv]⟩) f

end ModularTrivial
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀ normSq_firstRowℂ_of_mem archWeightOneℝ archWeightCharℝ archMatrixUpdate archMatrixUpdate_apply_self archMatrixUpdate_apply_of_ne archComponent_archGLIncl_self adelicArchGLIncl glArch_adelicArchGLIncl glFin_adelicArchGLIncl CarrierPins productionPinsOf AdelicGL2 rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal HeckeEigensystem.toRawCentral_ofRawCentral HeckeEigensystem.AgreesAwayFromFinite.of_toRawCentral SmoothCuspRealizationAt finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff HeckeEigensystem HeckeEigensystem.AgreesAwayFromFinite CuspidalConstituent.IsCuspConstituent CuspidalConstituent.CuspConstituentMeets CuspidalConstituent.levelInvariantSubmodule IsIsotypicCuspFormAt typeSubmodule comp_mul_mem_typeSubmodule_of_commute charRep apply_mul_eq_of_mem_typeSubmodule_charRep_dual ArchRepAt ArchRepAt.ofChar rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily ArchTypeFamily.ofChar archCutSubmodule mem_archCutSubmodule_iff IsArchBiFinite archRowIsometryInclAt₀ glFin_rowIsometryInclAt₀ archFactorDualTypeSubmoduleAt IsArchFactorBiFinite IsArchBiFinite.of_factorization IsGenuineCuspRealizationAt rightConv rightConv_apply archEntries IsArchTestFactor IsFinTestFactor IsFactorizableTestFn glBorelOf borelSpace_glBorelOf archHaarK CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite IsIsotypicCuspFormAt.of_le_of_subset SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent"
namespace SOTwoFourier
p2m_open "AutomorphicForm"

private theorem infinitePlace_subsingleton : Subsingleton (NumberField.InfinitePlace ℚ) :=
  ⟨fun w w' => by
    have h := congrArg NumberField.InfinitePlace.mk
      (Subsingleton.elim (NumberField.InfinitePlace.embedding w) (NumberField.InfinitePlace.embedding w'))
    rwa [NumberField.InfinitePlace.mk_embedding, NumberField.InfinitePlace.mk_embedding] at h⟩

private theorem isReal_place (w : NumberField.InfinitePlace ℚ) : w.IsReal := NumberField.IsTotallyReal.isReal w

private noncomputable abbrev realEquiv (w : NumberField.InfinitePlace ℚ) : w.Completion ≃+* ℝ :=
  NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_place w)

private theorem norm_realEquiv (w : NumberField.InfinitePlace ℚ) (x : w.Completion) : ‖realEquiv w x‖ = ‖x‖ :=
  AutomorphicForm.norm_ringEquivRealOfIsReal (isReal_place w) x

private theorem norm_realEquiv_symm (w : NumberField.InfinitePlace ℚ) (x : ℝ) : ‖(realEquiv w).symm x‖ = ‖x‖ := by
  have h := norm_realEquiv w ((realEquiv w).symm x)
  rw [RingEquiv.apply_symm_apply] at h
  exact h.symm

private theorem continuous_realEquiv (w : NumberField.InfinitePlace ℚ) : Continuous (realEquiv w) :=
  (AddMonoidHomClass.isometry_of_norm _ (norm_realEquiv w)).continuous

private theorem continuous_realEquiv_symm (w : NumberField.InfinitePlace ℚ) : Continuous (realEquiv w).symm :=
  (AddMonoidHomClass.isometry_of_norm _ (norm_realEquiv_symm w)).continuous

private noncomputable abbrev toPlace (w : NumberField.InfinitePlace ℚ) :
    AutomorphicForm.rowIsometrySubgroup₀ ℝ →* AutomorphicForm.rowIsometrySubgroup₀ w.Completion :=
  AutomorphicForm.rowIsometrySubgroup₀Map (realEquiv w).symm (norm_realEquiv_symm w)

private noncomputable abbrev ofPlace (w : NumberField.InfinitePlace ℚ) :
    AutomorphicForm.rowIsometrySubgroup₀ w.Completion →* AutomorphicForm.rowIsometrySubgroup₀ ℝ :=
  AutomorphicForm.rowIsometrySubgroup₀Map (realEquiv w) (norm_realEquiv w)

private theorem toPlace_ofPlace (w : NumberField.InfinitePlace ℚ)
    (k : AutomorphicForm.rowIsometrySubgroup₀ w.Completion) :
    toPlace w (ofPlace w k) = k := by
  apply Subtype.ext
  apply Units.ext
  ext i j : 1
  exact (realEquiv w).symm_apply_apply _

private theorem ofPlace_toPlace (w : NumberField.InfinitePlace ℚ) (k : AutomorphicForm.rowIsometrySubgroup₀ ℝ) :
    ofPlace w (toPlace w k) = k := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact (realEquiv w).apply_symm_apply _

private theorem continuous_rowIsometrySubgroup₀Map {K L : Type} [NormedField K] [NormedField L] (e : K ≃+* L)
    (he : ∀ x : K, ‖e x‖ = ‖x‖) (hec : Continuous e) : Continuous (AutomorphicForm.rowIsometrySubgroup₀Map e he) := by
  have hent : Continuous fun k : AutomorphicForm.rowIsometrySubgroup₀ K =>
      ((k : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
    Units.continuous_val.comp continuous_subtype_val
  apply continuous_induced_rng.2
  rw [Units.continuous_iff]
  constructor
  · refine continuous_matrix fun i j => ?_
    exact hec.comp (hent.matrix_elem i j)
  · refine continuous_matrix fun i j => ?_
    refine (hec.comp ((hent.comp continuous_inv).matrix_elem i j)).congr fun k => ?_
    dsimp only [Function.comp_def]
    rw [← Subgroup.coe_inv, ← map_inv]
    rfl

private theorem continuous_toPlace (w : NumberField.InfinitePlace ℚ) : Continuous (toPlace w) :=
  continuous_rowIsometrySubgroup₀Map _ _ (continuous_realEquiv_symm w)

private theorem continuous_ofPlace (w : NumberField.InfinitePlace ℚ) : Continuous (ofPlace w) :=
  continuous_rowIsometrySubgroup₀Map _ _ (continuous_realEquiv w)

private abbrev PlaceGroups : Type :=
  ∀ w : NumberField.InfinitePlace ℚ, AutomorphicForm.rowIsometrySubgroup₀ w.Completion

private noncomputable def diag : AutomorphicForm.rowIsometrySubgroup₀ ℝ →* PlaceGroups where
  toFun k w := toPlace w k
  map_one' := funext fun w => map_one (toPlace w)
  map_mul' a b := funext fun w => map_mul (toPlace w) a b

private theorem diag_apply (k : AutomorphicForm.rowIsometrySubgroup₀ ℝ) (w : NumberField.InfinitePlace ℚ) :
    diag k w = toPlace w k := rfl

private theorem continuous_diag : Continuous diag := continuous_pi fun w => continuous_toPlace w

private noncomputable def somePlace : NumberField.InfinitePlace ℚ := Classical.arbitrary _

private theorem diag_surjective : Function.Surjective diag := by
  intro κ
  refine ⟨ofPlace somePlace (κ somePlace), funext fun w => ?_⟩
  haveI := infinitePlace_subsingleton
  have hw : w = somePlace := Subsingleton.elim _ _
  subst hw
  rw [diag_apply, toPlace_ofPlace]

private theorem rotation_compactSpace : CompactSpace (AutomorphicForm.rowIsometrySubgroup₀ ℝ) := by
  refine ⟨?_⟩
  have h := isCompact_range continuous_circleEquiv_symm
  rwa [circleEquiv.symm.surjective.range_eq] at h

private theorem placeGroups_compactSpace : CompactSpace PlaceGroups := by
  haveI := rotation_compactSpace
  refine ⟨?_⟩
  have h := isCompact_range continuous_diag
  rwa [diag_surjective.range_eq] at h

private noncomputable abbrev weightChar (n : ℤ) (w : NumberField.InfinitePlace ℚ) :
    AutomorphicForm.rowIsometrySubgroup₀ w.Completion →* ℂˣ :=
  (AutomorphicForm.archWeightCharℝ n).comp (ofPlace w)

private theorem continuous_coe_weightCharℝ (n : ℤ) :
    Continuous fun k : AutomorphicForm.rowIsometrySubgroup₀ ℝ => ((AutomorphicForm.archWeightCharℝ n k : ℂˣ) : ℂ) := by
  have h : (fun k : AutomorphicForm.rowIsometrySubgroup₀ ℝ => ((AutomorphicForm.archWeightCharℝ n k : ℂˣ) : ℂ)) =
      fun k => ((toCircleHom k : Circle) : ℂ) ^ n := by
    funext k
    rw [coe_toCircleHom, AutomorphicForm.archWeightCharℝ, MonoidHom.comp_apply, zpowGroupHom_apply,
      Units.val_zpow_eq_zpow_val]
  rw [h]
  exact continuous_coe_toCircleHom.zpow₀ n fun k => Or.inl (Circle.coe_ne_zero _)

private theorem continuous_coe_weightChar (n : ℤ) (w : NumberField.InfinitePlace ℚ) :
    Continuous fun k : AutomorphicForm.rowIsometrySubgroup₀ w.Completion => ((weightChar n w k : ℂˣ) : ℂ) :=
  (continuous_coe_weightCharℝ n).comp (continuous_ofPlace w)

private noncomputable def placeIncl : PlaceGroups →* Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) :=
  (AutomorphicForm.archRowIsometryInclAt₀ ℚ somePlace).comp
    (Pi.evalMonoidHom (fun w : NumberField.InfinitePlace ℚ => AutomorphicForm.rowIsometrySubgroup₀ w.Completion)
      somePlace)

private theorem archComponent_placeIncl (κ : PlaceGroups) (w : NumberField.InfinitePlace ℚ) :
    NumberField.AdelicLevel.archComponent ℚ w (placeIncl κ) =
      ((κ w : AutomorphicForm.rowIsometrySubgroup₀ w.Completion) :
        Matrix.GeneralLinearGroup (Fin 2) w.Completion) := by
  haveI := infinitePlace_subsingleton
  have hw : w = somePlace := Subsingleton.elim _ _
  subst hw
  exact AutomorphicForm.archComponent_archGLIncl_self ℚ somePlace _

private theorem continuous_archMatrixUpdate (w : NumberField.InfinitePlace ℚ) :
    Continuous (AutomorphicForm.archMatrixUpdate ℚ w) := by
  refine continuous_matrix fun i j => continuous_pi fun v => ?_
  by_cases hv : v = w
  · subst hv
    exact (continuous_id.matrix_elem i j).congr fun m => (AutomorphicForm.archMatrixUpdate_apply_self ℚ v m i j).symm
  · exact continuous_const.congr fun m => (AutomorphicForm.archMatrixUpdate_apply_of_ne ℚ w m i j hv).symm

private theorem continuous_archRowIsometryInclAt₀ (w : NumberField.InfinitePlace ℚ) :
    Continuous (AutomorphicForm.archRowIsometryInclAt₀ ℚ w) := by
  have hent : Continuous fun k : AutomorphicForm.rowIsometrySubgroup₀ w.Completion =>
      ((k : Matrix.GeneralLinearGroup (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) :=
    Units.continuous_val.comp continuous_subtype_val
  rw [Units.continuous_iff]
  constructor
  · exact (continuous_archMatrixUpdate w).comp hent
  · refine ((continuous_archMatrixUpdate w).comp (hent.comp continuous_inv)).congr fun k => ?_
    rw [← map_inv]
    rfl

private theorem continuous_placeIncl : Continuous placeIncl :=
  (continuous_archRowIsometryInclAt₀ somePlace).comp (continuous_apply somePlace)

section Frame

private noncomputable def placeGroupsBorel : MeasurableSpace PlaceGroups := borel PlaceGroups

attribute [local instance] placeGroupsBorel

private theorem placeGroupsBorelSpace : BorelSpace PlaceGroups := ⟨rfl⟩

attribute [local instance] placeGroupsBorelSpace

private theorem measurable_diag : Measurable diag := continuous_diag.measurable

private noncomputable def placeMeasure : MeasureTheory.Measure PlaceGroups := MeasureTheory.Measure.map diag haarSO2

private theorem placeMeasure_isProbabilityMeasure : MeasureTheory.IsProbabilityMeasure placeMeasure :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_diag.aemeasurable

private theorem placeMeasure_isMulLeftInvariant : placeMeasure.IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨s, rfl⟩ := diag_surjective g
  rw [placeMeasure, MeasureTheory.Measure.map_map (measurable_const_mul _) measurable_diag]
  have h : ((diag s * ·) ∘ diag) = diag ∘ (s * ·) := by
    funext t
    simp only [Function.comp_apply, map_mul]
  rw [h, ← MeasureTheory.Measure.map_map measurable_diag (measurable_const_mul s),
    MeasureTheory.map_mul_left_eq_self]

private theorem placeMeasure_isMulRightInvariant : placeMeasure.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  obtain ⟨s, rfl⟩ := diag_surjective g
  rw [placeMeasure, MeasureTheory.Measure.map_map (measurable_mul_const _) measurable_diag]
  have h : ((· * diag s) ∘ diag) = diag ∘ (· * s) := by
    funext t
    simp only [Function.comp_apply, map_mul]
  rw [h, ← MeasureTheory.Measure.map_map measurable_diag (measurable_mul_const s),
    MeasureTheory.map_mul_right_eq_self]

private noncomputable def weightProj (n : ℤ) (φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) : ℂ :=
  ∫ κ, (∏ w, ((weightChar n w (κ w)⁻¹ : ℂˣ) : ℂ)) * φ (x * AutomorphicForm.adelicArchGLIncl ℚ (placeIncl κ))
    ∂placeMeasure

private theorem prod_weightChar_inv_diag (n : ℤ) (k : AutomorphicForm.rowIsometrySubgroup₀ ℝ) :
    (∏ w, ((weightChar n w (diag k w)⁻¹ : ℂˣ) : ℂ)) = (((AutomorphicForm.archWeightCharℝ n k)⁻¹ : ℂˣ) : ℂ) := by
  haveI := infinitePlace_subsingleton
  rw [Fintype.prod_subsingleton _ somePlace, diag_apply, map_inv, MonoidHom.comp_apply, ofPlace_toPlace]

private theorem exists_weightProj_ne_zero (φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : Continuous φ)
    (hne : φ ≠ 0) : ∃ n : ℤ, weightProj n φ ≠ 0 := by
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hne
  have hx₀' : φ x₀ ≠ 0 := hx₀
  set F : AutomorphicForm.rowIsometrySubgroup₀ ℝ → ℂ :=
    fun k => φ (x₀ * AutomorphicForm.adelicArchGLIncl ℚ (placeIncl (diag k))) with hF
  have hFc : Continuous F :=
    hφ.comp (continuous_const.mul (continuous_adelicArchGLIncl.comp (continuous_placeIncl.comp continuous_diag)))
  have hF1 : F 1 = φ x₀ := by
    simp only [hF, map_one, mul_one]
  have hFne : F ≠ 0 := fun h => hx₀' (by rw [← hF1, h, Pi.zero_apply])
  obtain ⟨n, hn⟩ := exists_integral_weightChar_inv_mul_ne_zero F hFc hFne
  refine ⟨n, fun h0 => hn ?_⟩
  have hx := congrFun h0 x₀
  rw [Pi.zero_apply, weightProj, placeMeasure, MeasureTheory.integral_map measurable_diag.aemeasurable] at hx
  · rw [← hx]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hF, prod_weightChar_inv_diag]
  · refine Continuous.aestronglyMeasurable ?_
    refine Continuous.mul (continuous_finset_prod _ fun w _ => ?_) ?_
    · exact (continuous_coe_weightChar n w).comp (continuous_inv.comp (continuous_apply w))
    · exact hφ.comp (continuous_const.mul (continuous_adelicArchGLIncl.comp continuous_placeIncl))

open AutomorphicForm.CuspidalConstituent in

private theorem continuous_weightProj_and_mem_archCutSubmodule (n : ℤ) (φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : Continuous φ) :
    Continuous (weightProj n φ) ∧
      weightProj n φ ∈
        AutomorphicForm.archCutSubmodule ℚ (AutomorphicForm.ArchTypeFamily.ofChar ℚ (weightChar n)) := by
  haveI := placeMeasure_isProbabilityMeasure
  haveI := placeMeasure_isMulLeftInvariant
  haveI := placeMeasure_isMulRightInvariant
  have h := continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl ℚ (weightChar n)
    (continuous_coe_weightChar n) placeMeasure placeIncl archComponent_placeIncl (weightProj n) (fun _ _ => rfl) φ hφ
  exact ⟨h.1, h.2.1⟩

end Frame
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end AutomorphicForm.SOTwoFourier
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀ normSq_firstRowℂ_of_mem archWeightOneℝ archWeightCharℝ archMatrixUpdate archMatrixUpdate_apply_self archMatrixUpdate_apply_of_ne archComponent_archGLIncl_self adelicArchGLIncl glArch_adelicArchGLIncl glFin_adelicArchGLIncl CarrierPins productionPinsOf AdelicGL2 rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal HeckeEigensystem.toRawCentral_ofRawCentral HeckeEigensystem.AgreesAwayFromFinite.of_toRawCentral SmoothCuspRealizationAt finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff HeckeEigensystem HeckeEigensystem.AgreesAwayFromFinite CuspidalConstituent.IsCuspConstituent CuspidalConstituent.CuspConstituentMeets CuspidalConstituent.levelInvariantSubmodule IsIsotypicCuspFormAt typeSubmodule comp_mul_mem_typeSubmodule_of_commute charRep apply_mul_eq_of_mem_typeSubmodule_charRep_dual ArchRepAt ArchRepAt.ofChar rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily ArchTypeFamily.ofChar archCutSubmodule mem_archCutSubmodule_iff IsArchBiFinite archRowIsometryInclAt₀ glFin_rowIsometryInclAt₀ archFactorDualTypeSubmoduleAt IsArchFactorBiFinite IsArchBiFinite.of_factorization IsGenuineCuspRealizationAt rightConv rightConv_apply archEntries IsArchTestFactor IsFinTestFactor IsFactorizableTestFn glBorelOf borelSpace_glBorelOf archHaarK CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite IsIsotypicCuspFormAt.of_le_of_subset SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent"
namespace SOTwoFourier
p2m_open "AutomorphicForm"

section ArchMeasure

attribute [local instance] AutomorphicForm.glBorelOf

private theorem archGL_borelSpace : BorelSpace (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) :=
  AutomorphicForm.borelSpace_glBorelOf (InfiniteAdeleRing ℚ)

attribute [local instance] archGL_borelSpace

private theorem archGL_locallyCompactSpace :
    LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing ℚ))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing ℚ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

attribute [local instance] archGL_locallyCompactSpace

private theorem archHaarK_isHaarMeasure : (AutomorphicForm.archHaarK ℚ).IsHaarMeasure := by
  unfold AutomorphicForm.archHaarK
  infer_instance

private theorem archHaarK_regular : (AutomorphicForm.archHaarK ℚ).Regular := by
  unfold AutomorphicForm.archHaarK
  infer_instance

attribute [local instance] archHaarK_isHaarMeasure archHaarK_regular

private theorem rotation_secondCountable : SecondCountableTopology (AutomorphicForm.rowIsometrySubgroup₀ ℝ) :=
  Homeomorph.secondCountableTopology
    { toEquiv := circleEquiv.toEquiv
      continuous_toFun := continuous_toCircleHom.congr fun k => (circleEquiv_apply k).symm
      continuous_invFun := continuous_circleEquiv_symm }

private noncomputable def rotIncl :
    AutomorphicForm.rowIsometrySubgroup₀ ℝ →* Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) :=
  placeIncl.comp diag

private theorem continuous_rotIncl : Continuous rotIncl := continuous_placeIncl.comp continuous_diag

private theorem rotIncl_apply (k : AutomorphicForm.rowIsometrySubgroup₀ ℝ) : rotIncl k = placeIncl (diag k) := rfl

private theorem weightProj_eq_integral_rotation (n : ℤ) (m : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hm : Continuous m)
    (x : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    weightProj n m x = ∫ k, (((AutomorphicForm.archWeightCharℝ n k)⁻¹ : ℂˣ) : ℂ) *
      m (x * AutomorphicForm.adelicArchGLIncl ℚ (rotIncl k)) ∂haarSO2 := by
  letI := placeGroupsBorel
  haveI := placeGroupsBorelSpace
  rw [weightProj, placeMeasure, MeasureTheory.integral_map measurable_diag.aemeasurable]
  · refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [prod_weightChar_inv_diag, rotIncl_apply]
  · refine Continuous.aestronglyMeasurable ?_
    refine Continuous.mul (continuous_finset_prod _ fun w _ => ?_) ?_
    · exact (continuous_coe_weightChar n w).comp (continuous_inv.comp (continuous_apply w))
    · exact hm.comp (continuous_const.mul (continuous_adelicArchGLIncl.comp continuous_placeIncl))

private theorem isArchFactorBiFinite_apply_mul_rotIncl (n : ℤ)
    {fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchFactorBiFinite ℚ (AutomorphicForm.ArchTypeFamily.ofChar ℚ (weightChar n)) fa)
    (k : AutomorphicForm.rowIsometrySubgroup₀ ℝ) (y : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) :
    fa (y * rotIncl k) = (((AutomorphicForm.archWeightCharℝ n k)⁻¹ : ℂˣ) : ℂ) * fa y := by
  have h0 : fa ∈ ⨅ w : NumberField.InfinitePlace ℚ, ⨆ _ : Fin 1,
      AutomorphicForm.archFactorDualTypeSubmoduleAt ℚ w (AutomorphicForm.ArchRepAt.ofChar ℚ (weightChar n w)) := hfa.2
  have h1 := (Submodule.mem_iInf _).mp h0 somePlace
  rw [iSup_const] at h1
  have h2 : fa ∈ AutomorphicForm.typeSubmodule (AutomorphicForm.archRowIsometryInclAt₀ ℚ somePlace)
      (AutomorphicForm.charRep (weightChar n somePlace)).dual := h1
  have h3 := AutomorphicForm.apply_mul_eq_of_mem_typeSubmodule_charRep_dual h2 (toPlace somePlace k) y
  rw [map_inv, MonoidHom.comp_apply, ofPlace_toPlace] at h3
  exact h3

private theorem rotIncl_mul_rotIncl_inv (k : AutomorphicForm.rowIsometrySubgroup₀ ℝ)
    (y : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) : y * rotIncl k * rotIncl k⁻¹ = y := by
  rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

private theorem integral_translate_mul_eq (n : ℤ) {fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchFactorBiFinite ℚ (AutomorphicForm.ArchTypeFamily.ofChar ℚ (weightChar n)) fa)
    (m : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (k : AutomorphicForm.rowIsometrySubgroup₀ ℝ) :
    ∫ y, m (g * AutomorphicForm.adelicArchGLIncl ℚ (y * rotIncl k)) * fa y ∂(AutomorphicForm.archHaarK ℚ) =
      ((AutomorphicForm.archWeightCharℝ n k : ℂˣ) : ℂ) *
        ∫ y, m (g * AutomorphicForm.adelicArchGLIncl ℚ y) * fa y ∂(AutomorphicForm.archHaarK ℚ) := by
  haveI := rotation_compactSpace
  have hsub := ModularTrivial.integral_mul_right_eq_self_of_range (AutomorphicForm.archHaarK ℚ) rotIncl
    continuous_rotIncl k fun z => m (g * AutomorphicForm.adelicArchGLIncl ℚ z) * fa (z * rotIncl k⁻¹)
  simp only [rotIncl_mul_rotIncl_inv] at hsub
  rw [hsub, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  rw [isArchFactorBiFinite_apply_mul_rotIncl n hfa k⁻¹ z, map_inv, inv_inv]
  ring

section Swap

private theorem integrable_double (n : ℤ) {fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchTestFactor ℚ fa) (m : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hm : Continuous m)
    (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    MeasureTheory.Integrable
      (Function.uncurry fun (y : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ))
        (k : AutomorphicForm.rowIsometrySubgroup₀ ℝ) => (((AutomorphicForm.archWeightCharℝ n k)⁻¹ : ℂˣ) : ℂ) *
          (m (g * AutomorphicForm.adelicArchGLIncl ℚ y * AutomorphicForm.adelicArchGLIncl ℚ (rotIncl k)) * fa y))
      (((AutomorphicForm.archHaarK ℚ).restrict (tsupport fa)).prod haarSO2) := by
  haveI := rotation_secondCountable
  haveI := rotation_compactSpace
  have hK : IsCompact (tsupport fa) := hasCompactSupport_of_isArchTestFactor hfa
  haveI : MeasureTheory.IsFiniteMeasure ((AutomorphicForm.archHaarK ℚ).restrict (tsupport fa)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing ℚ))
  rw [Function.uncurry_def]
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · refine Continuous.mul ((continuous_weightChar_inv n).comp continuous_snd) (Continuous.mul ?_ ?_)
    · refine hm.comp (Continuous.mul (continuous_const.mul (continuous_adelicArchGLIncl.comp continuous_fst)) ?_)
      exact continuous_adelicArchGLIncl.comp (continuous_rotIncl.comp continuous_snd)
    · exact (continuous_of_isArchTestFactor hfa).comp continuous_fst
  · refine HasCompactSupport.intro (hK.prod isCompact_univ) fun p hp => ?_
    have hp1 : p.1 ∉ tsupport fa := fun h => hp (Set.mem_prod.mpr ⟨h, Set.mem_univ _⟩)
    simp only [image_eq_zero_of_notMem_tsupport hp1, mul_zero]

private theorem integral_weightProj_mul_eq (n : ℤ) {fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchTestFactor ℚ fa)
    (hfa' : AutomorphicForm.IsArchFactorBiFinite ℚ (AutomorphicForm.ArchTypeFamily.ofChar ℚ (weightChar n)) fa)
    (m : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hm : Continuous m) (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    ∫ y, weightProj n m (g * AutomorphicForm.adelicArchGLIncl ℚ y) * fa y ∂(AutomorphicForm.archHaarK ℚ) =
      ∫ y, m (g * AutomorphicForm.adelicArchGLIncl ℚ y) * fa y ∂(AutomorphicForm.archHaarK ℚ) := by
  have hzero : ∀ y, y ∉ tsupport fa → fa y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy

  have hL : ∀ y, weightProj n m (g * AutomorphicForm.adelicArchGLIncl ℚ y) * fa y =
      ∫ k, (((AutomorphicForm.archWeightCharℝ n k)⁻¹ : ℂˣ) : ℂ) *
        (m (g * AutomorphicForm.adelicArchGLIncl ℚ y * AutomorphicForm.adelicArchGLIncl ℚ (rotIncl k)) * fa y)
        ∂haarSO2 := by
    intro y
    rw [weightProj_eq_integral_rotation n m hm, ← MeasureTheory.integral_mul_const]
    simp only [mul_assoc]
  simp only [hL]
  have hK : IsCompact (tsupport fa) := hasCompactSupport_of_isArchTestFactor hfa
  haveI : MeasureTheory.IsFiniteMeasure ((AutomorphicForm.archHaarK ℚ).restrict (tsupport fa)) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne

  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := tsupport fa) _,
    MeasureTheory.integral_integral_swap (integrable_double n hfa m hm g)]
  ·
    have hinner : ∀ k : AutomorphicForm.rowIsometrySubgroup₀ ℝ,
        ∫ y in tsupport fa, (((AutomorphicForm.archWeightCharℝ n k)⁻¹ : ℂˣ) : ℂ) *
            (m (g * AutomorphicForm.adelicArchGLIncl ℚ y * AutomorphicForm.adelicArchGLIncl ℚ (rotIncl k)) * fa y)
            ∂(AutomorphicForm.archHaarK ℚ) =
          ∫ y, m (g * AutomorphicForm.adelicArchGLIncl ℚ y) * fa y ∂(AutomorphicForm.archHaarK ℚ) := by
      intro k
      rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero _, MeasureTheory.integral_const_mul]
      · have h := integral_translate_mul_eq n hfa' m g k
        simp only [map_mul, mul_assoc] at h ⊢
        rw [h, ← mul_assoc, Units.inv_mul, one_mul]
      · intro y hy
        simp only [hzero y hy, mul_zero]
    simp only [hinner, MeasureTheory.integral_const, MeasureTheory.measureReal_def, MeasureTheory.measure_univ,
      ENNReal.toReal_one, one_smul]
  · intro y hy
    simp only [hzero y hy, mul_zero, MeasureTheory.integral_zero]

end Swap
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

private theorem exists_isArchTestFactor_isArchFactorBiFinite_integral_ne_zero
    (m : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hm : Continuous m) (hne : m ≠ 0) :
    ∃ (tys : AutomorphicForm.ArchTypeFamily ℚ) (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ),
      AutomorphicForm.IsArchTestFactor ℚ fa ∧ AutomorphicForm.IsArchFactorBiFinite ℚ tys fa ∧
        ∃ g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ,
          (letI := AutomorphicForm.glBorelOf (InfiniteAdeleRing ℚ)
            ∫ y, m (g * AutomorphicForm.adelicArchGLIncl ℚ y) * fa y ∂(AutomorphicForm.archHaarK ℚ)) ≠ 0 := by
  obtain ⟨n, hn⟩ := exists_weightProj_ne_zero m hm hne
  obtain ⟨hPc, hPmem⟩ := continuous_weightProj_and_mem_archCutSubmodule n m hm
  obtain ⟨fa, hfa, hlim⟩ :=
    AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule ℚ
      (AutomorphicForm.ArchTypeFamily.ofChar ℚ (weightChar n)) (weightProj n m) hPc hPmem
  obtain ⟨g, hg⟩ := Function.ne_iff.mp hn
  have hg' : weightProj n m g ≠ 0 := hg
  obtain ⟨j, hj⟩ := ((hlim g).eventually_ne hg').exists
  refine ⟨AutomorphicForm.ArchTypeFamily.ofChar ℚ (weightChar n), fa j, (hfa j).1, (hfa j).2, g, ?_⟩
  rw [← integral_weightProj_mul_eq n (hfa j).1 (hfa j).2 m hm g]
  exact hj

end ArchMeasure
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end AutomorphicForm.SOTwoFourier
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff entries_of_mem_rowIsometrySubgroup₀ normSq_firstRowℂ_of_mem archWeightOneℝ archWeightCharℝ archMatrixUpdate archMatrixUpdate_apply_self archMatrixUpdate_apply_of_ne archComponent_archGLIncl_self adelicArchGLIncl glArch_adelicArchGLIncl glFin_adelicArchGLIncl CarrierPins productionPinsOf AdelicGL2 rowIsometrySubgroup₀Map norm_ringEquivRealOfIsReal HeckeEigensystem.toRawCentral_ofRawCentral HeckeEigensystem.AgreesAwayFromFinite.of_toRawCentral SmoothCuspRealizationAt finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff HeckeEigensystem HeckeEigensystem.AgreesAwayFromFinite CuspidalConstituent.IsCuspConstituent CuspidalConstituent.CuspConstituentMeets CuspidalConstituent.levelInvariantSubmodule IsIsotypicCuspFormAt typeSubmodule comp_mul_mem_typeSubmodule_of_commute charRep apply_mul_eq_of_mem_typeSubmodule_charRep_dual ArchRepAt ArchRepAt.ofChar rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily ArchTypeFamily.ofChar archCutSubmodule mem_archCutSubmodule_iff IsArchBiFinite archRowIsometryInclAt₀ glFin_rowIsometryInclAt₀ archFactorDualTypeSubmoduleAt IsArchFactorBiFinite IsArchBiFinite.of_factorization IsGenuineCuspRealizationAt rightConv rightConv_apply archEntries IsArchTestFactor IsFinTestFactor IsFactorizableTestFn glBorelOf borelSpace_glBorelOf archHaarK CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite IsIsotypicCuspFormAt.of_le_of_subset SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent"
namespace ArchOp
p2m_open "AutomorphicForm"

private noncomputable def archOp (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ)
    (m : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) : ℂ :=
  (letI := AutomorphicForm.glBorelOf (InfiniteAdeleRing ℚ)
    ∫ y, m (g * AutomorphicForm.adelicArchGLIncl ℚ y) * fa y ∂(AutomorphicForm.archHaarK ℚ))

section Core

attribute [local instance] AutomorphicForm.glBorelOf

private theorem archGL_borelSpace : BorelSpace (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) :=
  AutomorphicForm.borelSpace_glBorelOf (InfiniteAdeleRing ℚ)

attribute [local instance] archGL_borelSpace

private theorem archMatrix_t2 : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing ℚ))

attribute [local instance] archMatrix_t2

private theorem archGL_locallyCompactSpace :
    LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing ℚ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

attribute [local instance] archGL_locallyCompactSpace

private theorem archHaarK_isHaarMeasure : (AutomorphicForm.archHaarK ℚ).IsHaarMeasure := by
  unfold AutomorphicForm.archHaarK
  infer_instance

private theorem archHaarK_regular : (AutomorphicForm.archHaarK ℚ).Regular := by
  unfold AutomorphicForm.archHaarK
  infer_instance

attribute [local instance] archHaarK_isHaarMeasure archHaarK_regular

private theorem archOp_apply (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ)
    (m : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    archOp fa m g = ∫ y, m (g * AutomorphicForm.adelicArchGLIncl ℚ y) * fa y ∂(AutomorphicForm.archHaarK ℚ) := rfl

private theorem integrable_archOp_integrand {fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchTestFactor ℚ fa) {m : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hm : Continuous m)
    (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    MeasureTheory.Integrable (fun y => m (g * AutomorphicForm.adelicArchGLIncl ℚ y) * fa y)
      (AutomorphicForm.archHaarK ℚ) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (hm.comp (continuous_const.mul continuous_adelicArchGLIncl)).mul (continuous_of_isArchTestFactor hfa)
  · refine HasCompactSupport.intro (hasCompactSupport_of_isArchTestFactor hfa) fun y hy => ?_
    simp only [image_eq_zero_of_notMem_tsupport hy, mul_zero]

private theorem archOp_add {fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ}
    (hfa : AutomorphicForm.IsArchTestFactor ℚ fa) {m₁ m₂ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hm₁ : Continuous m₁) (hm₂ : Continuous m₂) : archOp fa (m₁ + m₂) = archOp fa m₁ + archOp fa m₂ := by
  funext g
  simp only [archOp_apply, Pi.add_apply, add_mul]
  exact MeasureTheory.integral_add (integrable_archOp_integrand hfa hm₁ g) (integrable_archOp_integrand hfa hm₂ g)

private theorem archOp_smul (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ) (c : ℂ)
    (m : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : archOp fa (c • m) = c • archOp fa m := by
  funext g
  simp only [archOp_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact MeasureTheory.integral_const_mul c _

private theorem archOp_zero (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ) : archOp fa 0 = 0 := by
  funext g
  simp only [archOp_apply, Pi.zero_apply, zero_mul, MeasureTheory.integral_zero]

private theorem archOp_comp_mul_padicToAdelic (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ)
    (m : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (q : ℕ) [Fact q.Prime] (x : Matrix.GeneralLinearGroup (Fin 2) ℚ_[q]) :
    archOp fa (fun g => m (g * AdelicDock.padicToAdelic q x)) =
      fun g => archOp fa m (g * AdelicDock.padicToAdelic q x) := by
  funext g
  simp only [archOp_apply]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hcomm := padicToAdelic_mul_comm_of_finComponent_eq_one q (AutomorphicForm.adelicArchGLIncl ℚ y)
    (by rw [AutomorphicForm.glFin_adelicArchGLIncl, map_one]) x
  simp only [mul_assoc, hcomm]

end Core
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

section Identity

p2m_open "NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"

private noncomputable def finLevelIndicator (N : Ideal (𝓞 ℚ)) :
    Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) → ℂ :=
  Set.indicator
    (finiteLevelOne (𝓞 ℚ) ℚ N : Set (Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)))
    fun _ => 1

private noncomputable def levelTestFn (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ)
    (N : Ideal (𝓞 ℚ)) (x : AdelicGL2 (𝓞 ℚ) ℚ) : ℂ :=
  fa (glArch (𝓞 ℚ) ℚ x) * finLevelIndicator N (glFin (𝓞 ℚ) ℚ x)

private theorem finLevelIndicator_of_notMem {N : Ideal (𝓞 ℚ)}
    {b : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hb : b ∉ finiteLevelOne (𝓞 ℚ) ℚ N) :
    finLevelIndicator N b = 0 :=
  Set.indicator_of_notMem hb _

private theorem mem_of_finLevelIndicator_ne_zero {N : Ideal (𝓞 ℚ)}
    {b : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hb : finLevelIndicator N b ≠ 0) :
    b ∈ finiteLevelOne (𝓞 ℚ) ℚ N :=
  by_contra fun h => hb (finLevelIndicator_of_notMem h)

private theorem isFinTestFactor_finLevelIndicator {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) :
    IsFinTestFactor ℚ (finLevelIndicator N) := by
  have hUo := isOpen_finiteLevelOne (R := 𝓞 ℚ) (K := ℚ) hN
  refine ⟨?_, ?_⟩
  · exact (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ))
      ⟨isClosed_finiteLevelOne (R := 𝓞 ℚ) (K := ℚ) (N := N), hUo⟩).isLocallyConstant
  · exact HasCompactSupport.intro (isCompact_finiteLevelOne (R := 𝓞 ℚ) (K := ℚ) (N := N))
      fun b hb => finLevelIndicator_of_notMem hb

private theorem isFactorizableTestFn_levelTestFn {fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ}
    (hfa : IsArchTestFactor ℚ fa) {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) : IsFactorizableTestFn ℚ (levelTestFn fa N) :=
  ⟨fa, finLevelIndicator N, hfa, isFinTestFactor_finLevelIndicator hN, fun _ => rfl⟩

private theorem isArchBiFinite_levelTestFn {tys : ArchTypeFamily ℚ}
    {fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ} (hfa : IsArchFactorBiFinite ℚ tys fa)
    (N : Ideal (𝓞 ℚ)) : IsArchBiFinite ℚ tys (levelTestFn fa N) :=
  IsArchBiFinite.of_factorization ℚ (ff := finLevelIndicator N) (fun _ => rfl) hfa

private theorem levelTestFn_support (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ)
    (N : Ideal (𝓞 ℚ)) (x : AdelicGL2 (𝓞 ℚ) ℚ) (hx : levelTestFn fa N x ≠ 0) :
    ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ a = 1 ∧
      k ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k := by
  have hb : glFin (𝓞 ℚ) ℚ x ∈ finiteLevelOne (𝓞 ℚ) ℚ N :=
    mem_of_finLevelIndicator_ne_zero (right_ne_zero_of_mul hx)
  refine ⟨adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ x), (adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ x))⁻¹ * x,
    glFin_adelicArchGLIncl ℚ _, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, (mul_inv_cancel_left _ _).symm⟩
  · show glFin (𝓞 ℚ) ℚ _ ∈ finiteLevelOne (𝓞 ℚ) ℚ N
    rwa [map_mul, map_inv, glFin_adelicArchGLIncl, inv_one, one_mul]
  · show glArch (𝓞 ℚ) ℚ _ = 1
    rw [map_mul, map_inv, glArch_adelicArchGLIncl, inv_mul_cancel]

private theorem mul_levelTestFn_eq {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {N : Ideal (𝓞 ℚ)}
    (hφ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ u ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ, φ (g * u) = φ g)
    (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ) (g x : AdelicGL2 (𝓞 ℚ) ℚ) :
    φ (g * x) * levelTestFn fa N x =
      (φ (g * adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ x)) * fa (glArch (𝓞 ℚ) ℚ x)) *
        finLevelIndicator N (glFin (𝓞 ℚ) ℚ x) := by
  by_cases hx : levelTestFn fa N x = 0
  · have h0 : fa (glArch (𝓞 ℚ) ℚ x) * finLevelIndicator N (glFin (𝓞 ℚ) ℚ x) = 0 := hx
    rw [hx, mul_zero, mul_assoc, h0, mul_zero]
  · have hb : glFin (𝓞 ℚ) ℚ x ∈ finiteLevelOne (𝓞 ℚ) ℚ N :=
      mem_of_finLevelIndicator_ne_zero (right_ne_zero_of_mul hx)
    have hk' : φ (g * x) = φ (g * adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ x)) := by
      have : φ (g * adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ x) * ((adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ x))⁻¹ * x)) =
          φ (g * adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ x)) := by
        refine hφ _ _ (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
        · show glFin (𝓞 ℚ) ℚ _ ∈ finiteLevelOne (𝓞 ℚ) ℚ N
          rwa [map_mul, map_inv, glFin_adelicArchGLIncl, inv_one, one_mul]
        · show glArch (𝓞 ℚ) ℚ _ = 1
          rw [map_mul, map_inv, glArch_adelicArchGLIncl, inv_mul_cancel]
      rwa [mul_assoc, mul_inv_cancel_left] at this
    rw [hk', levelTestFn, mul_assoc]

private noncomputable def finGLBorel :
    MeasurableSpace (Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  borel _

attribute [local instance] glBorelOf finGLBorel

private theorem archGL_borelSpace' : BorelSpace (Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ)) :=
  borelSpace_glBorelOf (InfiniteAdeleRing ℚ)

private theorem finGL_borelSpace :
    BorelSpace (Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  ⟨rfl⟩

attribute [local instance] archGL_borelSpace' finGL_borelSpace archGL_locallyCompactSpace archHaarK_isHaarMeasure
  archHaarK_regular

private theorem finGL_locallyCompactSpace :
    LocallyCompactSpace (Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

attribute [local instance] finGL_locallyCompactSpace

private noncomputable def finHaar :
    MeasureTheory.Measure (Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  MeasureTheory.Measure.haar

private theorem finHaar_isHaarMeasure : finHaar.IsHaarMeasure := by
  unfold finHaar
  infer_instance

private theorem finHaar_regular : finHaar.Regular := by
  unfold finHaar
  infer_instance

attribute [local instance] finHaar_isHaarMeasure finHaar_regular

private theorem integral_finLevelIndicator_ne_zero {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) :
    ∫ b, finLevelIndicator N b ∂finHaar ≠ 0 := by
  have hUo := isOpen_finiteLevelOne (R := 𝓞 ℚ) (K := ℚ) hN
  have hUc := isCompact_finiteLevelOne (R := 𝓞 ℚ) (K := ℚ) (N := N)
  rw [finLevelIndicator, MeasureTheory.integral_indicator_const (1 : ℂ) hUo.measurableSet, Complex.real_smul, mul_one,
    MeasureTheory.measureReal_def]
  exact_mod_cast ENNReal.toReal_ne_zero.mpr
    ⟨(hUo.measure_pos finHaar ⟨1, (finiteLevelOne (𝓞 ℚ) ℚ N).one_mem⟩).ne', hUc.measure_lt_top.ne⟩

private theorem exists_archOp_eq_smul_rightConv {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) :
    ∃ s : ℂ, s ≠ 0 ∧ ∀ (fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ)
      (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ u ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ, φ (g * u) = φ g) →
        archOp fa φ = s • rightConv ℚ φ (levelTestFn fa N) := by
  obtain ⟨c, hc, hsplit⟩ :=
    NumberField.AdelicHaar.exists_integral_glArch_mul_glFin_eq_mul_integral_mul_integral ℚ (archHaarK ℚ) finHaar
  have hvol := integral_finLevelIndicator_ne_zero hN
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  refine ⟨((c : ℂ) * ∫ b, finLevelIndicator N b ∂finHaar)⁻¹, inv_ne_zero (mul_ne_zero hc' hvol), ?_⟩
  intro fa φ hφ
  funext g
  have hfun : (fun x => φ (g * x) * levelTestFn fa N x) = fun x =>
      (φ (g * adelicArchGLIncl ℚ (glArch (𝓞 ℚ) ℚ x)) * fa (glArch (𝓞 ℚ) ℚ x)) *
        finLevelIndicator N (glFin (𝓞 ℚ) ℚ x) :=
    funext fun x => mul_levelTestFn_eq hφ fa g x
  rw [Pi.smul_apply, rightConv_apply, hfun,
    hsplit (fun y => φ (g * adelicArchGLIncl ℚ y) * fa y) (finLevelIndicator N), smul_eq_mul, archOp_apply]
  refine ((inv_mul_cancel_left₀ (mul_ne_zero hc' hvol) _).symm.trans ?_)
  ring

end Identity
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

section Wrappers

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

private theorem isIsotypicCuspFormAt_rightConv_levelTestFn (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      Φ.toRawCentral)
    (hR : Continuous R.toFun) {fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ}
    (hfa : IsArchTestFactor ℚ fa) (hN : Φ.level ≠ ⊥) :
    IsIsotypicCuspFormAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      R.centralChar Φ.level R.exceptionalSet Φ (rightConv ℚ R.toFun (levelTestFn fa Φ.level)) :=
  AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
    c u d₁ d₂ T hd hcov Φ R hR _ (isFactorizableTestFn_levelTestFn hfa hN) (levelTestFn_support fa Φ.level)

private theorem rightConv_levelTestFn_mem_archCutSubmodule (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) {N : Ideal (𝓞 ℚ)}
    (hN : N ≠ ⊥) {tys : ArchTypeFamily ℚ} {fa : Matrix.GeneralLinearGroup (Fin 2) (InfiniteAdeleRing ℚ) → ℂ}
    (hfa : IsArchTestFactor ℚ fa) (hbf : IsArchFactorBiFinite ℚ tys fa) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφc : Continuous φ)
    (hφU : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ∀ u ∈ levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ, φ (g * u) = φ g) :
    rightConv ℚ φ (levelTestFn fa N) ∈ archCutSubmodule ℚ tys :=
  (AutomorphicForm.CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite ℚ D
    N tys _ (isFactorizableTestFn_levelTestFn hfa hN) (isArchBiFinite_levelTestFn hbf N)
    (fun x hx => levelTestFn_support fa N x hx) φ hφc (fun g u hu => hφU g u hu)).2

end Wrappers
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end AutomorphicForm.ArchOp
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

section

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.toFn_mk AdelicFnCarrier.mk_toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_zero AdelicFnCarrier.toFn_add AdelicFnCarrier.toFn_csmul AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def IsIrreducibleGLRep exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace FixedPullback
p2m_open "LocalNewvector"

variable {G : Type*} [Monoid G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V]
variable {W : Type*} [AddCommGroup W] [Module ℂ W] [DistribMulAction G W] [SMulCommClass G ℂ W]

variable (V) in

private def fixedBy (H : Set G) : Submodule ℂ V where
  carrier := {v | ∀ h ∈ H, h • v = v}
  add_mem' {a b} ha hb := fun h hh => by rw [smul_add, ha h hh, hb h hh]
  zero_mem' := fun h _ => smul_zero h
  smul_mem' c {v} hv := fun h hh => by rw [smul_comm, hv h hh]

private theorem mem_fixedBy {H : Set G} {v : V} : v ∈ fixedBy V H ↔ ∀ h ∈ H, h • v = v := Iff.rfl

private theorem map_mem_fixedBy {H : Set G} (f : W →ₗ[ℂ] V) (hf : ∀ (x : G) (w : W), f (x • w) = x • f w)
    {w : W} (hw : w ∈ fixedBy W H) : f w ∈ fixedBy V H :=
  fun h hh => by rw [← hf, hw h hh]

private theorem finiteDimensional_fixedBy_of_injective {H : Set G} (f : W →ₗ[ℂ] V)
    (hf : ∀ (x : G) (w : W), f (x • w) = x • f w) (hinj : Function.Injective f)
    [FiniteDimensional ℂ (fixedBy V H)] : FiniteDimensional ℂ (fixedBy W H) := by
  refine FiniteDimensional.of_injective (f.restrict fun w hw => map_mem_fixedBy f hf hw) ?_
  intro a b hab
  apply Subtype.ext
  apply hinj
  simpa only [LinearMap.restrict_apply, Subtype.mk.injEq] using congrArg Subtype.val hab

private theorem injective_of_forall_submodule_eq (f : W →ₗ[ℂ] V)
    (hf : ∀ (x : G) (w : W), f (x • w) = x • f w)
    (hirr : ∀ U : Submodule ℂ W, (∀ x : G, ∀ w ∈ U, x • w ∈ U) → U = ⊥ ∨ U = ⊤) (hne : f ≠ 0) :
    Function.Injective f := by
  have hker : ∀ x : G, ∀ w ∈ LinearMap.ker f, x • w ∈ LinearMap.ker f := by
    intro x w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [hf, hw, smul_zero]
  rcases hirr (LinearMap.ker f) hker with h | h
  · exact LinearMap.ker_eq_bot.mp h
  · exact absurd (LinearMap.ker_eq_top.mp h) hne

end LocalNewvector.FixedPullback
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

section

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.toFn_mk AdelicFnCarrier.mk_toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_zero AdelicFnCarrier.toFn_add AdelicFnCarrier.toFn_csmul AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def IsIrreducibleGLRep exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace OrbitSpan
p2m_open "LocalNewvector"

variable {G : Type*} [Monoid G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W] [DistribMulAction G W] [SMulCommClass G ℂ W]
variable {Q : Type*} [AddCommGroup Q] [Module ℂ Q] [DistribMulAction G Q] [SMulCommClass G ℂ Q]
variable {P : Type*} [AddCommGroup P] [Module ℂ P] [DistribMulAction G P] [SMulCommClass G ℂ P]

private theorem map_span_orbit (δ : Q →ₗ[ℂ] P) (hδ : ∀ (x : G) (u : Q), δ (x • u) = x • δ u) (w : Q) :
    Submodule.map δ (Submodule.span ℂ (Set.range fun x : G => x • w)) =
      Submodule.span ℂ (Set.range fun x : G => x • δ w) := by
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext x
  exact hδ x w

private theorem orbitSpan_push {κ : Type*} (δ : Q →ₗ[ℂ] P) (hδ : ∀ (x : G) (u : Q), δ (x • u) = x • δ u) (w : Q)
    (f : κ → (W →ₗ[ℂ] Q)) (hf : ∀ (k : κ) (x : G) (v : W), f k (x • v) = x • f k v)
    (hle : ∀ k, LinearMap.range (f k) ≤ Submodule.span ℂ (Set.range fun x : G => x • w))
    (hge : Submodule.span ℂ (Set.range fun x : G => x • w) ≤ ⨆ k, LinearMap.range (f k)) :
    (∀ (k : κ) (x : G) (v : W), (δ ∘ₗ f k) (x • v) = x • (δ ∘ₗ f k) v) ∧
      (∀ k, LinearMap.range (δ ∘ₗ f k) ≤ Submodule.span ℂ (Set.range fun x : G => x • δ w)) ∧
        Submodule.span ℂ (Set.range fun x : G => x • δ w) ≤ ⨆ k, LinearMap.range (δ ∘ₗ f k) := by
  refine ⟨fun k x v => ?_, fun k => ?_, ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply, hf, hδ]
  · rw [LinearMap.range_comp, ← map_span_orbit δ hδ w]
    exact Submodule.map_mono (hle k)
  · rw [← map_span_orbit δ hδ w]
    refine (Submodule.map_mono hge).trans ?_
    rw [Submodule.map_iSup]
    exact iSup_mono fun k => (LinearMap.range_comp (f k) δ).symm.le

end LocalNewvector.OrbitSpan
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

section

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.toFn_mk AdelicFnCarrier.mk_toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_zero AdelicFnCarrier.toFn_add AdelicFnCarrier.toFn_csmul AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def IsIrreducibleGLRep exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace CoordCover
p2m_open "LocalNewvector"

section

variable {Q : Type*} [AddCommGroup Q] [Module ℂ Q]

private noncomputable def subAction (q : ℕ) [Fact q.Prime] [DistribMulAction (GL (Fin 2) ℚ_[q]) Q] (S : Submodule ℂ Q)
    (hS : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ s ∈ S, x • s ∈ S) : DistribMulAction (GL (Fin 2) ℚ_[q]) ↥S where
  smul x s := ⟨x • (s : Q), hS x s s.2⟩
  one_smul s := Subtype.ext (one_smul (GL (Fin 2) ℚ_[q]) (s : Q))
  mul_smul x y s := Subtype.ext (mul_smul x y (s : Q))
  smul_zero x := Subtype.ext (smul_zero x)
  smul_add x s t := Subtype.ext (smul_add x (s : Q) (t : Q))

private theorem subAction_smulCommClass (q : ℕ) [Fact q.Prime] [DistribMulAction (GL (Fin 2) ℚ_[q]) Q]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ Q] (S : Submodule ℂ Q) (hS : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ s ∈ S, x • s ∈ S) :
    letI := subAction q S hS
    SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ ↥S :=
  letI := subAction q S hS
  ⟨fun x c s => Subtype.ext (smul_comm x c (s : Q))⟩

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

private theorem exists_cover_of_coordMap (q : ℕ) [Fact q.Prime]
    {M' : Type} [AddCommGroup M'] [Module ℂ M'] [DistribMulAction (GL (Fin 2) ℚ_[q]) M']
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ M']
    {W : Type} [AddCommGroup W] [Module ℂ W] [DistribMulAction (GL (Fin 2) ℚ_[q]) W]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ W] (hW : LocalNewvector.IsIrreducibleGLRep q W)
    {CI : Type} (C : M' →ₗ[ℂ] (CI → W)) (hC : Function.Injective C)
    (hCx : ∀ (x : GL (Fin 2) ℚ_[q]) (m : M'), C (x • m) = x • C m)
    (m₀ : M') (hgen : Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • m₀) = ⊤)
    (E : Submodule ℂ W) [FiniteDimensional ℂ ↥E] (hE : ∀ ci, C m₀ ci ∈ E) :
    ∃ (κ : Type) (F : κ → (W →ₗ[ℂ] M')),
      (∀ (k : κ) (x : GL (Fin 2) ℚ_[q]) (v : W), F k (x • v) = x • F k v) ∧ ⨆ k, LinearMap.range (F k) = ⊤ := by
  classical
  let b := Module.finBasis ℂ ↥E

  obtain ⟨δ, hδx, hδw⟩ : ∃ δ : (Fin (Module.finrank ℂ ↥E) → W) →ₗ[ℂ] (CI → W),
      (∀ (x : GL (Fin 2) ℚ_[q]) (u : Fin (Module.finrank ℂ ↥E) → W), δ (x • u) = x • δ u) ∧
        δ (fun j => (b j : W)) = C m₀ := by
    refine ⟨{ toFun := fun u ci => ∑ j, b.repr ⟨C m₀ ci, hE ci⟩ j • u j, map_add' := ?_, map_smul' := ?_ },
      ?_, ?_⟩
    · intro u v
      funext ci
      show ∑ j, b.repr ⟨C m₀ ci, hE ci⟩ j • (u + v) j =
        ∑ j, b.repr ⟨C m₀ ci, hE ci⟩ j • u j + ∑ j, b.repr ⟨C m₀ ci, hE ci⟩ j • v j
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [Pi.add_apply, smul_add]
    · intro a u
      funext ci
      show ∑ j, b.repr ⟨C m₀ ci, hE ci⟩ j • (a • u) j = a • ∑ j, b.repr ⟨C m₀ ci, hE ci⟩ j • u j
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [Pi.smul_apply]; exact smul_comm _ a (u j)
    · intro x u
      funext ci
      show ∑ j, b.repr ⟨C m₀ ci, hE ci⟩ j • (x • u) j = x • ∑ j, b.repr ⟨C m₀ ci, hE ci⟩ j • u j
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [Pi.smul_apply]; exact (smul_comm x _ (u j)).symm
    · funext ci
      show ∑ j, b.repr ⟨C m₀ ci, hE ci⟩ j • (b j : W) = C m₀ ci
      have h := congrArg Subtype.val (b.sum_repr ⟨C m₀ ci, hE ci⟩)
      rw [Submodule.coe_sum] at h
      simpa only [Submodule.coe_smul] using h

  let N : Submodule ℂ (Fin (Module.finrank ℂ ↥E) → W) :=
    Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • fun j => (b j : W))
  have hN : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ n ∈ N, x • n ∈ N := by
    intro x n hn
    refine Submodule.span_induction (p := fun n _ => x • n ∈ N) ?_ ?_ ?_ ?_ hn
    · rintro _ ⟨y, rfl⟩
      exact Submodule.subset_span ⟨x * y, mul_smul x y _⟩
    · show x • (0 : Fin (Module.finrank ℂ ↥E) → W) ∈ N
      rw [smul_zero]
      exact N.zero_mem
    · intro n₁ n₂ _ _ h₁ h₂
      rw [smul_add]
      exact N.add_mem h₁ h₂
    · intro c n _ h
      rw [smul_comm]
      exact N.smul_mem c h
  letI := subAction q N hN
  haveI := subAction_smulCommClass q N hN
  let L : ↥N →ₗ[ℂ] (Fin (Module.finrank ℂ ↥E) →₀ W) :=
    (Finsupp.linearEquivFunOnFinite ℂ W (Fin (Module.finrank ℂ ↥E))).symm.toLinearMap ∘ₗ N.subtype
  have hL : Function.Injective L :=
    (Finsupp.linearEquivFunOnFinite ℂ W (Fin (Module.finrank ℂ ↥E))).symm.injective.comp N.injective_subtype
  have hLx : ∀ (x : GL (Fin 2) ℚ_[q]) (n : ↥N), L (x • n) = x • L n := by
    intro x n
    apply Finsupp.ext
    intro j
    rfl
  obtain ⟨κ, g, hg, hgtop⟩ :=
    LocalNewvector.exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep q W ↥N hW
      (Fin (Module.finrank ℂ ↥E)) L hL hLx
  have hf : ∀ (k : κ) (x : GL (Fin 2) ℚ_[q]) (v : W), (N.subtype ∘ₗ g k) (x • v) = x • (N.subtype ∘ₗ g k) v := by
    intro k x v
    show ((g k (x • v) : ↥N) : Fin (Module.finrank ℂ ↥E) → W) =
      x • ((g k v : ↥N) : Fin (Module.finrank ℂ ↥E) → W)
    rw [hg k x v]
    rfl
  have hle : ∀ k, LinearMap.range (N.subtype ∘ₗ g k) ≤ N := fun k => by
    rw [LinearMap.range_comp]
    exact Submodule.map_subtype_le N _
  have hge : N ≤ ⨆ k, LinearMap.range (N.subtype ∘ₗ g k) := by
    have h1 : (⨆ k, LinearMap.range (N.subtype ∘ₗ g k)) =
        Submodule.map N.subtype (⨆ k, LinearMap.range (g k)) := by
      rw [Submodule.map_iSup]
      exact iSup_congr fun k => LinearMap.range_comp _ _
    rw [h1, hgtop, Submodule.map_subtype_top]

  obtain ⟨hF1, hF2, hF3⟩ := LocalNewvector.OrbitSpan.orbitSpan_push (G := GL (Fin 2) ℚ_[q]) δ hδx (fun j => (b j : W))
    (fun k => N.subtype ∘ₗ g k) hf hle hge
  rw [hδw] at hF2 hF3

  have hrange : LinearMap.range C = Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • C m₀) := by
    rw [LinearMap.range_eq_map, ← hgen]
    exact LocalNewvector.OrbitSpan.map_span_orbit C hCx m₀
  have hF2' : ∀ k, LinearMap.range (δ ∘ₗ (N.subtype ∘ₗ g k)) ≤ LinearMap.range C := fun k => by
    rw [hrange]
    exact hF2 k

  let e := LinearEquiv.ofInjective C hC
  let F : κ → (W →ₗ[ℂ] M') := fun k =>
    e.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range C) (δ ∘ₗ (N.subtype ∘ₗ g k))
      fun v => hF2' k (LinearMap.mem_range_self _ v)
  have hCF : ∀ k v, C (F k v) = (δ ∘ₗ (N.subtype ∘ₗ g k)) v := fun k v =>
    LinearEquiv.ofInjective_symm_apply C (h := hC)
      (LinearMap.codRestrict (LinearMap.range C) (δ ∘ₗ (N.subtype ∘ₗ g k))
        (fun v => hF2' k (LinearMap.mem_range_self _ v)) v)
  refine ⟨κ, F, fun k x v => hC ?_, ?_⟩
  · rw [hCF, hCx, hCF]
    exact hF1 k x v
  · apply Submodule.map_injective_of_injective hC
    rw [Submodule.map_iSup, Submodule.map_top]
    have h2 : ∀ k, Submodule.map C (LinearMap.range (F k)) = LinearMap.range (δ ∘ₗ (N.subtype ∘ₗ g k)) :=
      fun k => by rw [← LinearMap.range_comp]; exact congrArg LinearMap.range (LinearMap.ext (hCF k))
    rw [iSup_congr h2]
    refine le_antisymm (iSup_le hF2') ?_
    rw [hrange]
    exact hF3

end LocalNewvector.CoordCover
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

section

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.toFn_mk AdelicFnCarrier.mk_toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_zero AdelicFnCarrier.toFn_add AdelicFnCarrier.toFn_csmul AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def IsIrreducibleGLRep exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace NearClassEmbedding
p2m_open "LocalNewvector"

private theorem exists_constituent_of_genuine (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    {Θ' : HeckeEigensystem ℚ ℂ} (R' : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ')
    (hR' : Continuous R'.toFun) :
    ∃ V₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      CuspidalConstituent.IsCuspConstituent ℚ (windowPins c u d₁ d₂ T) R'.centralChar V₀ ∧
      (∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)), R'.exceptionalSet ⊆ S ∧
        CuspidalConstituent.CuspConstituentMeets ℚ (windowPins c u d₁ d₂ T) R'.centralChar Θ'.level S
          Θ'.ofRawCentral V₀) ∧
      (∀ (w : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (tys : ArchTypeFamily ℚ),
        IsIsotypicCuspFormAt ℚ (windowPins c u d₁ d₂ T) R'.centralChar Θ'.level R'.exceptionalSet
          Θ'.ofRawCentral w →
        w ∈ archCutSubmodule ℚ tys → w ∈ V₀) ∧
      ∃ (N₀ : Ideal (𝓞 ℚ)) (_ : N₀ ≠ ⊥) (tys₀ : ArchTypeFamily ℚ),
        V₀ ⊓ CuspidalConstituent.levelInvariantSubmodule ℚ (windowPins c u d₁ d₂ T) N₀ ⊓
          archCutSubmodule ℚ tys₀ ≠ ⊥ := by

  have hwit := LanglandsTunnell.exists_rightConv_ne_zero_mem_isotypicCuspSubmodule_mem_archCutSubmodule
    c u d₁ d₂ T hd hcov Θ'.ofRawCentral (RawRescalingTransport.reindex R') hR'
  obtain ⟨S, tys₀, f, hS, -, -, hne, hiso, hcut⟩ := hwit

  have hmem := isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent ℚ c u d₁ d₂ T hd hcov
    R'.centralChar Θ'.level S tys₀ Θ'.ofRawCentral (Submodule.mem_inf.2 ⟨hiso, hcut⟩)
  have huniq : ∀ V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      (CuspidalConstituent.IsCuspConstituent ℚ (windowPins c u d₁ d₂ T) R'.centralChar V₁ ∧
        CuspidalConstituent.CuspConstituentMeets ℚ (windowPins c u d₁ d₂ T) R'.centralChar Θ'.level S
          Θ'.ofRawCentral V₁ ∧ V₁ ⊓ archCutSubmodule ℚ tys₀ ≠ ⊥) →
      (CuspidalConstituent.IsCuspConstituent ℚ (windowPins c u d₁ d₂ T) R'.centralChar V₂ ∧
        CuspidalConstituent.CuspConstituentMeets ℚ (windowPins c u d₁ d₂ T) R'.centralChar Θ'.level S
          Θ'.ofRawCentral V₂ ∧ V₂ ⊓ archCutSubmodule ℚ tys₀ ≠ ⊥) → V₁ = V₂ :=
    fun V₁ V₂ h₁ h₂ =>
      eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre ℚ c u d₁ d₂ T hd hcov R'.centralChar
        Θ'.level S Θ'.ofRawCentral V₁ V₂ h₁.1 h₂.1 h₁.2.1 h₂.2.1
  obtain ⟨V₀, ⟨hV₀, hmeet, -⟩, hvV₀, -⟩ :=
    SubsingletonSup.exists_mem_eq_iSup_of_ne_zero_of_mem_iSup _ huniq hne hmem
  refine ⟨V₀, hV₀, ⟨S, hS, hmeet⟩, ?_, ?_⟩
  swap
  ·
    refine ⟨Θ'.ofRawCentral.level, Θ'.ofRawCentral.level_ne_bot, tys₀, (Submodule.ne_bot_iff _).2 ⟨_, ?_, hne⟩⟩
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hvV₀, ?_⟩, hcut⟩
    refine (Submodule.span_le.2 ?_ :
      _ ≤ CuspidalConstituent.levelInvariantSubmodule ℚ (windowPins c u d₁ d₂ T) Θ'.ofRawCentral.level) hiso
    intro φ (hφ : IsIsotypicCuspFormAt ℚ _ _ _ _ _ φ)
    exact hφ.level_invariant

  intro w tys hw hwcut
  have hw' := isotypicCuspSubmodule_inf_archCutSubmodule_le_iSup_isCuspConstituent ℚ c u d₁ d₂ T hd hcov
    R'.centralChar Θ'.level R'.exceptionalSet tys Θ'.ofRawCentral
    (Submodule.mem_inf.2 ⟨hw.mem_isotypicCuspSubmodule, hwcut⟩)
  refine (iSup_le fun V => iSup_le fun hV => ?_ : _ ≤ V₀) hw'

  have hVS : CuspidalConstituent.CuspConstituentMeets ℚ (windowPins c u d₁ d₂ T) R'.centralChar Θ'.level S
      Θ'.ofRawCentral V := by
    obtain ⟨φ, hφV, hφ0, hφ⟩ := hV.2.1
    exact ⟨φ, hφV, hφ0,
      DatumTransport.isIsotypicCuspFormAt_of_forall_eq hφ hS (fun _ _ => rfl) (fun _ _ => rfl)⟩
  exact (eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre ℚ c u d₁ d₂ T hd hcov R'.centralChar
    Θ'.level S Θ'.ofRawCentral V V₀ hV.1 hV₀ hVS hmeet).le

end LocalNewvector.NearClassEmbedding
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

section

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.toFn_mk AdelicFnCarrier.mk_toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_zero AdelicFnCarrier.toFn_add AdelicFnCarrier.toFn_csmul AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def IsIrreducibleGLRep exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace NearClassEmbedding
p2m_open "LocalNewvector"

private theorem constituent_eq_of_agreesAwayFromFinite (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (hmono : ∀ (ξ : (windowPins c u d₁ d₂ T).Z →* ℂˣ) {N N' : Ideal (𝓞 ℚ)}, N' ≤ N → N' ≠ ⊥ →
      ∀ {S S' : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))}, S ⊆ S' →
      (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), v ∉ S' → ¬ v.asIdeal ∣ N') →
      ∀ (Ψ : HeckeEigensystem ℚ ℂ) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ},
        IsIsotypicCuspFormAt ℚ (windowPins c u d₁ d₂ T) ξ N S Ψ φ →
        IsIsotypicCuspFormAt ℚ (windowPins c u d₁ d₂ T) ξ N' S' Ψ φ)
    {Θ Θ₁ Θ₂ : HeckeEigensystem ℚ ℂ} (h₁ : Θ₁.AgreesAwayFromFinite Θ) (h₂ : Θ₂.AgreesAwayFromFinite Θ)
    (R₁ : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ₁)
    (hg₁ : IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ₁ R₁)
    (R₂ : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ₂)
    (hg₂ : IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ₂ R₂)
    {V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)}
    (hV₁ : CuspidalConstituent.IsCuspConstituent ℚ (windowPins c u d₁ d₂ T) R₁.centralChar V₁)
    {S₁ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))}
    (m₁ : CuspidalConstituent.CuspConstituentMeets ℚ (windowPins c u d₁ d₂ T) R₁.centralChar Θ₁.level S₁
      Θ₁.ofRawCentral V₁)
    (hV₂ : CuspidalConstituent.IsCuspConstituent ℚ (windowPins c u d₁ d₂ T) R₂.centralChar V₂)
    {S₂ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))}
    (m₂ : CuspidalConstituent.CuspConstituentMeets ℚ (windowPins c u d₁ d₂ T) R₂.centralChar Θ₂.level S₂
      Θ₂.ofRawCentral V₂) :
    V₁ = V₂ := by

  have hag : Θ₁.AgreesAwayFromFinite Θ₂ := DatumTransport.agrees_trans h₁ (DatumTransport.agrees_symm h₂)
  have hagRaw : Θ₁.ofRawCentral.AgreesAwayFromFinite Θ₂.ofRawCentral := by
    apply HeckeEigensystem.AgreesAwayFromFinite.of_toRawCentral
    simpa only [HeckeEigensystem.toRawCentral_ofRawCentral] using hag

  have hξ : R₁.centralChar = R₂.centralChar :=
    SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite ℚ _ Θ₁.ofRawCentral Θ₂.ofRawCentral hagRaw
      (RawRescalingTransport.reindex R₁) hg₁ (RawRescalingTransport.reindex R₂) hg₂
  rw [← hξ] at hV₂ m₂

  obtain ⟨S, -, c₁, c₂⟩ :=
    DatumTransport.exists_common_datum (hmono R₁.centralChar) Θ₁.level_ne_bot Θ₂.level_ne_bot
      (DatumTransport.agrees_symm hagRaw) m₁ m₂
  exact eq_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre ℚ c u d₁ d₂ T hd hcov R₁.centralChar
    (Θ₁.level * Θ₂.level) S Θ₁.ofRawCentral V₁ V₂ hV₁ hV₂ c₁ c₂

private theorem hmono_of_window (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (ξ : (windowPins c u d₁ d₂ T).Z →* ℂˣ) {N N' : Ideal (𝓞 ℚ)} (hN : N' ≤ N) (hN'0 : N' ≠ ⊥)
    {S S' : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))} (hSS' : S ⊆ S')
    (hS' : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), v ∉ S' → ¬ v.asIdeal ∣ N')
    (Ψ : HeckeEigensystem ℚ ℂ) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : IsIsotypicCuspFormAt ℚ (windowPins c u d₁ d₂ T) ξ N S Ψ φ) :
    IsIsotypicCuspFormAt ℚ (windowPins c u d₁ d₂ T) ξ N' S' Ψ φ :=
  IsIsotypicCuspFormAt.of_le_of_subset ℚ _ ξ hN hN'0 hSS' hS' Ψ hφ

end LocalNewvector.NearClassEmbedding
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

section

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.toFn_mk AdelicFnCarrier.mk_toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_zero AdelicFnCarrier.toFn_add AdelicFnCarrier.toFn_csmul AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def IsIrreducibleGLRep exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace AwayTranslation
p2m_open "LocalNewvector"

section Padic

variable (q : ℕ) [Fact q.Prime]

private noncomputable def padicGLInv :
    Matrix.GeneralLinearGroup (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ) →*
      Matrix.GeneralLinearGroup (Fin 2) ℚ_[q] :=
  Matrix.GeneralLinearGroup.map (AdelicDock.padicRingEquiv q).symm.toRingHom

private theorem padicGL_padicGLInv
    (y : Matrix.GeneralLinearGroup (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ)) :
    AdelicDock.padicGL q (padicGLInv q y) = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicDock.padicGL_apply, padicGLInv, Matrix.GeneralLinearGroup.map_apply]
  exact (AdelicDock.padicRingEquiv q).apply_symm_apply _

private def IsAwayFromQ (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) : Prop :=
  AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ h) = 1

private theorem exists_eq_mul_padicToAdelic_isAwayFromQ (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) (x : Matrix.GeneralLinearGroup (Fin 2) ℚ_[q]),
      g = h * AdelicDock.padicToAdelic q x ∧ IsAwayFromQ q h ∧
        (g ∈ AutomorphicForm.finiteAdelicGL2Subgroup ℚ → h ∈ AutomorphicForm.finiteAdelicGL2Subgroup ℚ) := by
  refine ⟨g * (AdelicDock.padicToAdelic q (padicGLInv q (AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
    (AdelicLevel.glFin (𝓞 ℚ) ℚ g))))⁻¹, padicGLInv q (AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
    (AdelicLevel.glFin (𝓞 ℚ) ℚ g)), (inv_mul_cancel_right _ _).symm, ?_, ?_⟩
  · unfold IsAwayFromQ
    rw [map_mul, map_inv, map_mul, map_inv, AdelicDock.glFin_padicToAdelic,
      AdelicDock.finComponent_padicToFinAdelic_self, padicGL_padicGLInv, mul_inv_cancel]
  · intro hg
    rw [AutomorphicForm.mem_finiteAdelicGL2Subgroup_iff] at hg ⊢
    rw [map_mul, map_inv, AdelicDock.glArch_padicToAdelic, inv_one, mul_one, hg]

private noncomputable def awayMap (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ :=
  DistribSMul.toLinearMap ℂ (LocalNewvector.AdelicFnCarrier ℚ) h

private theorem awayMap_apply (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) (ψ : LocalNewvector.AdelicFnCarrier ℚ) :
    awayMap h ψ = h • ψ := rfl

private theorem awayMap_smul (h g₀ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) (ψ : LocalNewvector.AdelicFnCarrier ℚ) :
    awayMap h (g₀ • ψ) = (h * g₀) • ψ := by
  rw [awayMap_apply, mul_smul]

private theorem awayMap_padic_smul (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (x : Matrix.GeneralLinearGroup (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ) :
    awayMap h (x • ψ) = (h * AdelicDock.padicToAdelic q x) • ψ := by
  rw [LocalNewvector.AdelicFnCarrier.padic_smul_def, awayMap_smul]

private theorem padic_smul_awayMap {h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ} (hh : IsAwayFromQ q h)
    (x : Matrix.GeneralLinearGroup (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ) :
    awayMap h (x • ψ) = x • awayMap h ψ := by
  rw [awayMap_apply, awayMap_apply, LocalNewvector.AdelicFnCarrier.padic_smul_def,
    LocalNewvector.AdelicFnCarrier.padic_smul_def, ← mul_smul, ← mul_smul,
    padicToAdelic_mul_comm_of_finComponent_eq_one q h hh x]

private theorem exists_isAwayFromQ_smul_eq_awayMap_padic_smul (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) (x : Matrix.GeneralLinearGroup (Fin 2) ℚ_[q]), IsAwayFromQ q h ∧
      ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, g • ψ = awayMap h (x • ψ) := by
  obtain ⟨h, x, rfl, hh, -⟩ := exists_eq_mul_padicToAdelic_isAwayFromQ q g
  exact ⟨h, x, hh, fun ψ => (awayMap_padic_smul q h x ψ).symm⟩

end Padic
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end LocalNewvector.AwayTranslation
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

section

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.toFn_mk AdelicFnCarrier.mk_toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_zero AdelicFnCarrier.toFn_add AdelicFnCarrier.toFn_csmul AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def IsIrreducibleGLRep exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace NearClassEmbedding
p2m_open "LocalNewvector"

private theorem genSpan_eq (q : ℕ) [Fact q.Prime] (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    genSpan q φ = Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicFnCarrier.mk φ) := by
  unfold genSpan
  congr 1
  ext χ
  constructor <;> rintro ⟨x, hx⟩ <;> exact ⟨x, hx.symm⟩

private theorem genSet_smul_mem (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (Θ : HeckeEigensystem ℚ ℂ)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) : ∀ χ ∈ genSet c u d₁ d₂ T Θ, g • χ ∈ genSet c u d₁ d₂ T Θ := by
  rintro χ ⟨g₀, Θ', hΘ', R', hR', rfl⟩
  exact ⟨g * g₀, Θ', hΘ', R', hR', (mul_smul g g₀ _).symm⟩

private theorem exists_cover_of_mem_genSet (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (Θ : HeckeEigensystem ℚ ℂ) (q : ℕ) [Fact q.Prime]
    (W : Type) [AddCommGroup W] [Module ℂ W] [DistribMulAction (GL (Fin 2) ℚ_[q]) W]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ W]
    (hgen : ∀ (Θ' : HeckeEigensystem ℚ ℂ) (_ : Θ'.AgreesAwayFromFinite Θ)
        (R' : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ')
        (_ : IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ' R'),
        ∃ (κ : Type) (f : κ → (W →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ)),
          (∀ (k : κ) (x : GL (Fin 2) ℚ_[q]) (v : W), f k (x • v) = x • f k v) ∧
          (∀ k, LinearMap.range (f k) ≤ genSpan q R'.toFun) ∧
          genSpan q R'.toFun ≤ ⨆ k, LinearMap.range (f k)) :
    ∀ χ ∈ genSet c u d₁ d₂ T Θ, ∃ (κ : Type) (f : κ → (W →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ)),
      (∀ (k : κ) (x : GL (Fin 2) ℚ_[q]) (v : W), f k (x • v) = x • f k v) ∧
      (∀ k, LinearMap.range (f k) ≤ Submodule.span ℂ (genSet c u d₁ d₂ T Θ)) ∧
      χ ∈ ⨆ k, LinearMap.range (f k) := by
  rintro χ ⟨g, Θ', hΘ', R', hR', rfl⟩
  obtain ⟨h, x, hh, heq⟩ := LocalNewvector.AwayTranslation.exists_isAwayFromQ_smul_eq_awayMap_padic_smul q g
  obtain ⟨κ, f, hf, hle, hge⟩ := hgen Θ' hΘ' R' hR'
  rw [genSpan_eq] at hle hge
  obtain ⟨hf', hle', hge'⟩ := LocalNewvector.OrbitSpan.orbitSpan_push (LocalNewvector.AwayTranslation.awayMap h)
    (fun y v => LocalNewvector.AwayTranslation.padic_smul_awayMap q hh y v)
    (LocalNewvector.AdelicFnCarrier.mk R'.toFun) f hf hle hge
  refine ⟨κ, fun k => LocalNewvector.AwayTranslation.awayMap h ∘ₗ f k, hf', fun k => (hle' k).trans ?_, ?_⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨y, rfl⟩
    refine ⟨AdelicDock.padicToAdelic q y * h, Θ', hΘ', R', hR', ?_⟩
    simp only [LocalNewvector.AwayTranslation.awayMap_apply]
    rw [LocalNewvector.AdelicFnCarrier.padic_smul_def, mul_smul]
  · refine hge' (Submodule.subset_span ⟨x, ?_⟩)
    rw [heq, LocalNewvector.AwayTranslation.padic_smul_awayMap q hh]

end LocalNewvector.NearClassEmbedding
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

section

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.toFn_mk AdelicFnCarrier.mk_toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_zero AdelicFnCarrier.toFn_add AdelicFnCarrier.toFn_csmul AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def IsIrreducibleGLRep exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace NearClassEmbedding
p2m_open "LocalNewvector"

private theorem continuous_toFn_of_mem_genSpan (q : ℕ) [Fact q.Prime] {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : Continuous φ) : ∀ m ∈ genSpan q φ, Continuous m.toFn := by
  intro m hm
  refine Submodule.span_induction (p := fun m _ => Continuous m.toFn) ?_ ?_ ?_ ?_ hm
  · rintro χ ⟨x, rfl⟩
    rw [LocalNewvector.Members.toFn_padic_smul, LocalNewvector.AdelicFnCarrier.toFn_mk]
    exact hφ.comp (continuous_id.mul continuous_const)
  · show Continuous (0 : LocalNewvector.AdelicFnCarrier ℚ).toFn
    rw [LocalNewvector.AdelicFnCarrier.toFn_zero]
    exact continuous_zero
  · intro a b _ _ ha hb
    rw [LocalNewvector.AdelicFnCarrier.toFn_add]
    exact ha.add hb
  · intro a b _ hb
    rw [LocalNewvector.AdelicFnCarrier.toFn_csmul]
    exact hb.const_smul a

private theorem genSpan_padic_stable (q : ℕ) [Fact q.Prime] (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (x : GL (Fin 2) ℚ_[q]) :
    ∀ m ∈ genSpan q φ, x • m ∈ genSpan q φ := by
  intro m hm
  refine Submodule.span_induction (p := fun m _ => x • m ∈ genSpan q φ) ?_ ?_ ?_ ?_ hm
  · rintro χ ⟨y, rfl⟩
    exact Submodule.subset_span ⟨x * y, (mul_smul x y _).symm⟩
  · show x • (0 : LocalNewvector.AdelicFnCarrier ℚ) ∈ genSpan q φ
    rw [smul_zero]
    exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [smul_add]
    exact Submodule.add_mem _ ha hb
  · intro a b _ hb
    rw [smul_comm]
    exact Submodule.smul_mem _ a hb

private theorem archOp_toFn_padic_smul (q : ℕ) [Fact q.Prime] (fa : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ)
    (m : LocalNewvector.AdelicFnCarrier ℚ) (x : GL (Fin 2) ℚ_[q]) :
    AutomorphicForm.ArchOp.archOp fa (x • m).toFn =
      (x • LocalNewvector.AdelicFnCarrier.mk (AutomorphicForm.ArchOp.archOp fa m.toFn)).toFn := by
  rw [LocalNewvector.Members.toFn_padic_smul, LocalNewvector.Members.toFn_padic_smul,
    LocalNewvector.AdelicFnCarrier.toFn_mk]
  exact AutomorphicForm.ArchOp.archOp_comp_mul_padicToAdelic fa m.toFn q x

private theorem archOp_toFn_smul (fa : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ) (a : ℂ)
    (m : LocalNewvector.AdelicFnCarrier ℚ) :
    AutomorphicForm.ArchOp.archOp fa (a • m).toFn = a • AutomorphicForm.ArchOp.archOp fa m.toFn := by
  rw [LocalNewvector.AdelicFnCarrier.toFn_csmul]
  exact AutomorphicForm.ArchOp.archOp_smul fa a m.toFn

private theorem archOp_toFn_add_of_mem_genSpan (q : ℕ) [Fact q.Prime] {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : Continuous φ) {fa : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ} (hfa : IsArchTestFactor ℚ fa) :
    ∀ m₁ ∈ genSpan q φ, ∀ m₂ ∈ genSpan q φ,
      AutomorphicForm.ArchOp.archOp fa (m₁ + m₂).toFn =
        AutomorphicForm.ArchOp.archOp fa m₁.toFn + AutomorphicForm.ArchOp.archOp fa m₂.toFn := by
  intro m₁ h₁ m₂ h₂
  rw [LocalNewvector.AdelicFnCarrier.toFn_add]
  exact AutomorphicForm.ArchOp.archOp_add hfa (continuous_toFn_of_mem_genSpan q hφ m₁ h₁)
    (continuous_toFn_of_mem_genSpan q hφ m₂ h₂)

private theorem archOp_toFn_mem_of_mem_genSpan (q : ℕ) [Fact q.Prime] (V₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hst : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ V₀ → (x • ψ).toFn ∈ V₀)
    {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hφ : Continuous φ) {fa : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ}
    (hfa : IsArchTestFactor ℚ fa) (hφV : AutomorphicForm.ArchOp.archOp fa φ ∈ V₀) :
    ∀ m ∈ genSpan q φ, AutomorphicForm.ArchOp.archOp fa m.toFn ∈ V₀ := by
  intro m hm
  refine Submodule.span_induction (p := fun m _ => AutomorphicForm.ArchOp.archOp fa m.toFn ∈ V₀) ?_ ?_ ?_ ?_ hm
  · rintro χ ⟨x, rfl⟩
    rw [archOp_toFn_padic_smul]
    exact hst x _ hφV
  · show AutomorphicForm.ArchOp.archOp fa (0 : LocalNewvector.AdelicFnCarrier ℚ).toFn ∈ V₀
    rw [LocalNewvector.AdelicFnCarrier.toFn_zero, AutomorphicForm.ArchOp.archOp_zero]
    exact V₀.zero_mem
  · intro a b ha hb hA hB
    rw [archOp_toFn_add_of_mem_genSpan q hφ hfa a ha b hb]
    exact V₀.add_mem hA hB
  · intro a b _ hB
    rw [archOp_toFn_smul]
    exact V₀.smul_mem a hB

private theorem exists_archOp_toFn_ne_zero_of_mem_genSpan (q : ℕ) [Fact q.Prime] {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hφ : Continuous φ) :
    ∀ m ∈ genSpan q φ, m ≠ 0 → ∃ (tys : ArchTypeFamily ℚ) (fa : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ),
      IsArchTestFactor ℚ fa ∧ IsArchFactorBiFinite ℚ tys fa ∧ AutomorphicForm.ArchOp.archOp fa m.toFn ≠ 0 := by
  intro m hm hne
  obtain ⟨tys, fa, hfa, hbf, g, hg⟩ :=
    AutomorphicForm.SOTwoFourier.exists_isArchTestFactor_isArchFactorBiFinite_integral_ne_zero m.toFn
      (continuous_toFn_of_mem_genSpan q hφ m hm) (fun h => hne h)
  exact ⟨tys, fa, hfa, hbf, fun h => hg (congrFun h g)⟩

private theorem archOp_toFun_mem (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (V₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (Θ' : HeckeEigensystem ℚ ℂ)
    (R' : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ')
    (hR' : IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ' R')
    (hcl :
      ∀ (w : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (tys : ArchTypeFamily ℚ),
        IsIsotypicCuspFormAt ℚ (windowPins c u d₁ d₂ T) R'.centralChar Θ'.level R'.exceptionalSet
          Θ'.ofRawCentral w →
        w ∈ archCutSubmodule ℚ tys → w ∈ V₀)
    {tys : ArchTypeFamily ℚ} {fa : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ} (hfa : IsArchTestFactor ℚ fa)
    (hbf : IsArchFactorBiFinite ℚ tys fa) : AutomorphicForm.ArchOp.archOp fa R'.toFun ∈ V₀ := by
  obtain ⟨s, -, hs⟩ := AutomorphicForm.ArchOp.exists_archOp_eq_smul_rightConv Θ'.level_ne_bot
  have hiso : IsIsotypicCuspFormAt ℚ (windowPins c u d₁ d₂ T) R'.centralChar Θ'.level R'.exceptionalSet
      Θ'.ofRawCentral (rightConv ℚ R'.toFun (AutomorphicForm.ArchOp.levelTestFn fa Θ'.level)) :=
    AutomorphicForm.ArchOp.isIsotypicCuspFormAt_rightConv_levelTestFn c u d₁ d₂ T hd hcov Θ'.ofRawCentral
      (AutomorphicForm.RawRescalingTransport.reindex R') hR' hfa Θ'.ofRawCentral.level_ne_bot
  have hcut : rightConv ℚ R'.toFun (AutomorphicForm.ArchOp.levelTestFn fa Θ'.level) ∈ archCutSubmodule ℚ tys :=
    AutomorphicForm.ArchOp.rightConv_levelTestFn_mem_archCutSubmodule
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Θ'.level_ne_bot hfa hbf hR'
      (fun g v hv => R'.level_invariant g v hv)
  rw [hs fa R'.toFun (fun g v hv => R'.level_invariant g v hv)]
  exact V₀.smul_mem s (hcl _ tys hiso hcut)

private theorem archOp_toFn_mem_of_mem_genSpan_toFun (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (q : ℕ) [Fact q.Prime] (V₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hst : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ V₀ → (x • ψ).toFn ∈ V₀)
    (Θ' : HeckeEigensystem ℚ ℂ) (R' : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ')
    (hR' : IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ' R')
    (hcl :
      ∀ (w : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (tys : ArchTypeFamily ℚ),
        IsIsotypicCuspFormAt ℚ (windowPins c u d₁ d₂ T) R'.centralChar Θ'.level R'.exceptionalSet
          Θ'.ofRawCentral w →
        w ∈ archCutSubmodule ℚ tys → w ∈ V₀)
    {tys : ArchTypeFamily ℚ} {fa : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ} (hfa : IsArchTestFactor ℚ fa)
    (hbf : IsArchFactorBiFinite ℚ tys fa) :
    ∀ m ∈ genSpan q R'.toFun, AutomorphicForm.ArchOp.archOp fa m.toFn ∈ V₀ := by
  exact archOp_toFn_mem_of_mem_genSpan q V₀ hst (hR' : Continuous R'.toFun) hfa
    (archOp_toFun_mem c u d₁ d₂ T hd hcov V₀ Θ' R' hR' hcl hfa hbf)

private theorem archOp_toFun_mem_levelInvariantSubmodule_inf_archCutSubmodule (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (Θ' : HeckeEigensystem ℚ ℂ)
    (R' : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ')
    (hR' : IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ' R') {tys : ArchTypeFamily ℚ}
    {fa : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ} (hfa : IsArchTestFactor ℚ fa) (hbf : IsArchFactorBiFinite ℚ tys fa) :
    AutomorphicForm.ArchOp.archOp fa R'.toFun ∈
      CuspidalConstituent.levelInvariantSubmodule ℚ (windowPins c u d₁ d₂ T) Θ'.level ⊓ archCutSubmodule ℚ tys := by
  obtain ⟨s, -, hs⟩ := AutomorphicForm.ArchOp.exists_archOp_eq_smul_rightConv Θ'.level_ne_bot
  rw [hs fa R'.toFun (fun g v hv => R'.level_invariant g v hv)]
  exact Submodule.smul_mem _ s
    (AutomorphicForm.CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite ℚ
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Θ'.level tys _
      (AutomorphicForm.ArchOp.isFactorizableTestFn_levelTestFn hfa Θ'.level_ne_bot)
      (AutomorphicForm.ArchOp.isArchBiFinite_levelTestFn hbf Θ'.level)
      (fun x hx => AutomorphicForm.ArchOp.levelTestFn_support fa Θ'.level x hx) R'.toFun hR'
      (fun g v hv => R'.level_invariant g v hv))

private def AdmIdx : Type :=
  {p : ArchTypeFamily ℚ × (GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ) //
    IsArchTestFactor ℚ p.2 ∧ IsArchFactorBiFinite ℚ p.1 p.2}

private theorem mk_add (x y : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    LocalNewvector.AdelicFnCarrier.mk (x + y) =
      LocalNewvector.AdelicFnCarrier.mk x + LocalNewvector.AdelicFnCarrier.mk y :=
  rfl

private theorem mk_smul (a : ℂ) (x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    LocalNewvector.AdelicFnCarrier.mk (a • x) = a • LocalNewvector.AdelicFnCarrier.mk x :=
  rfl

private noncomputable def coordMap (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (q : ℕ) [Fact q.Prime]
    (W : Type) [AddCommGroup W] [Module ℂ W] (ι₀ : Type) (Φ : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] (ι₀ →₀ W))
    (Θ' : HeckeEigensystem ℚ ℂ) (R' : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ')
    (hR' : IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ' R') :
    ↥(genSpan q R'.toFun) →ₗ[ℂ] (AdmIdx × ι₀ → W) where
  toFun m := fun pi =>
    Φ (LocalNewvector.AdelicFnCarrier.mk (AutomorphicForm.ArchOp.archOp pi.1.1.2 m.1.toFn)) pi.2
  map_add' m₁ m₂ := by
    funext pi
    simp only [Pi.add_apply]
    rw [Submodule.coe_add, archOp_toFn_add_of_mem_genSpan q (hR' : Continuous R'.toFun) pi.1.2.1 m₁.1 m₁.2 m₂.1 m₂.2,
      mk_add, map_add, Finsupp.add_apply]
  map_smul' a m := by
    funext pi
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Submodule.coe_smul, archOp_toFn_smul, mk_smul, map_smul, Finsupp.smul_apply]

private theorem coordMap_apply (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (q : ℕ) [Fact q.Prime]
    (W : Type) [AddCommGroup W] [Module ℂ W] (ι₀ : Type) (Φ : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] (ι₀ →₀ W))
    (Θ' : HeckeEigensystem ℚ ℂ) (R' : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ')
    (hR' : IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ' R') (m : ↥(genSpan q R'.toFun)) (p : AdmIdx)
    (i : ι₀) :
    coordMap c u d₁ d₂ T q W ι₀ Φ Θ' R' hR' m (p, i) =
      Φ (LocalNewvector.AdelicFnCarrier.mk (AutomorphicForm.ArchOp.archOp p.1.2 m.1.toFn)) i :=
  rfl

private theorem coordMap_injective (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (q : ℕ) [Fact q.Prime] (V₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hst : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ V₀ → (x • ψ).toFn ∈ V₀)
    (W : Type) [AddCommGroup W] [Module ℂ W] (ι₀ : Type) (Φ : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] (ι₀ →₀ W))
    (hinj : ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V₀ → Φ ψ = 0 → ψ = 0)
    (Θ' : HeckeEigensystem ℚ ℂ) (R' : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ')
    (hR' : IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ' R')
    (hcl :
      ∀ (w : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (tys : ArchTypeFamily ℚ),
        IsIsotypicCuspFormAt ℚ (windowPins c u d₁ d₂ T) R'.centralChar Θ'.level R'.exceptionalSet
          Θ'.ofRawCentral w →
        w ∈ archCutSubmodule ℚ tys → w ∈ V₀) :
    Function.Injective (coordMap c u d₁ d₂ T q W ι₀ Φ Θ' R' hR') := by
  intro m₁ m₂ h
  rw [← sub_eq_zero]
  have h0 : coordMap c u d₁ d₂ T q W ι₀ Φ Θ' R' hR' (m₁ - m₂) = 0 := by
    rw [map_sub, h, sub_self]
  by_contra hne
  have hne' : (m₁ - m₂).1 ≠ 0 := fun h' => hne (Subtype.ext h')
  obtain ⟨tys, fa, hfa, hbf, hop⟩ :=
    exists_archOp_toFn_ne_zero_of_mem_genSpan q (hR' : Continuous R'.toFun) (m₁ - m₂).1 (m₁ - m₂).2 hne'
  have hmem : (LocalNewvector.AdelicFnCarrier.mk (AutomorphicForm.ArchOp.archOp fa (m₁ - m₂).1.toFn)).toFn ∈ V₀ :=
    archOp_toFn_mem_of_mem_genSpan_toFun c u d₁ d₂ T hd hcov q V₀ hst Θ' R' hR' hcl hfa hbf (m₁ - m₂).1 (m₁ - m₂).2
  have hΦ : Φ (LocalNewvector.AdelicFnCarrier.mk (AutomorphicForm.ArchOp.archOp fa (m₁ - m₂).1.toFn)) = 0 := by
    ext i
    have h1 := congrFun h0 (⟨(tys, fa), hfa, hbf⟩, i)
    rw [coordMap_apply, Pi.zero_apply] at h1
    exact h1
  exact hop (congrArg LocalNewvector.AdelicFnCarrier.toFn (hinj _ hmem hΦ))

private theorem coordMap_smul (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (q : ℕ) [Fact q.Prime] (V₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hst : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ V₀ → (x • ψ).toFn ∈ V₀)
    (W : Type) [AddCommGroup W] [Module ℂ W] [DistribMulAction (GL (Fin 2) ℚ_[q]) W]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ W] (ι₀ : Type) (Φ : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] (ι₀ →₀ W))
    (heqv : ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V₀ → ∀ x : GL (Fin 2) ℚ_[q], Φ (x • ψ) = x • Φ ψ)
    (Θ' : HeckeEigensystem ℚ ℂ) (R' : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ')
    (hR' : IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ' R')
    (hcl :
      ∀ (w : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (tys : ArchTypeFamily ℚ),
        IsIsotypicCuspFormAt ℚ (windowPins c u d₁ d₂ T) R'.centralChar Θ'.level R'.exceptionalSet
          Θ'.ofRawCentral w →
        w ∈ archCutSubmodule ℚ tys → w ∈ V₀) :
    letI := LocalNewvector.AwayCarrier.stableAction q (genSpan q R'.toFun) (genSpan_padic_stable q R'.toFun)
    ∀ (x : GL (Fin 2) ℚ_[q]) (m : ↥(genSpan q R'.toFun)),
      coordMap c u d₁ d₂ T q W ι₀ Φ Θ' R' hR' (x • m) = x • coordMap c u d₁ d₂ T q W ι₀ Φ Θ' R' hR' m := by
  letI := LocalNewvector.AwayCarrier.stableAction q (genSpan q R'.toFun) (genSpan_padic_stable q R'.toFun)
  intro x m
  funext ⟨p, i⟩
  have hmem := archOp_toFn_mem_of_mem_genSpan_toFun c u d₁ d₂ T hd hcov q V₀ hst Θ' R' hR' hcl p.2.1 p.2.2 m.1 m.2
  rw [Pi.smul_apply, coordMap_apply, coordMap_apply,
    show (x • m : ↥(genSpan q R'.toFun)).1 = x • m.1 from rfl, archOp_toFn_padic_smul,
    LocalNewvector.AdelicFnCarrier.mk_toFn,
    heqv (LocalNewvector.AdelicFnCarrier.mk (AutomorphicForm.ArchOp.archOp p.1.2 m.1.toFn)) hmem x, Finsupp.smul_apply]

private theorem generator_mem_genSpan (q : ℕ) [Fact q.Prime] (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    LocalNewvector.AdelicFnCarrier.mk φ ∈ genSpan q φ :=
  Submodule.subset_span ⟨1, (one_smul _ _).symm⟩

private def generator (q : ℕ) [Fact q.Prime] (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) : ↥(genSpan q φ) :=
  ⟨LocalNewvector.AdelicFnCarrier.mk φ, generator_mem_genSpan q φ⟩

private theorem generator_val (q : ℕ) [Fact q.Prime] (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    (generator q φ).1 = LocalNewvector.AdelicFnCarrier.mk φ :=
  rfl

private theorem coordMap_generator_mem_fixedBy (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (q : ℕ) [Fact q.Prime] (V₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hst : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ V₀ → (x • ψ).toFn ∈ V₀)
    (W : Type) [AddCommGroup W] [Module ℂ W] [DistribMulAction (GL (Fin 2) ℚ_[q]) W]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ W] (ι₀ : Type) (Φ : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] (ι₀ →₀ W))
    (heqv : ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V₀ → ∀ x : GL (Fin 2) ℚ_[q], Φ (x • ψ) = x • Φ ψ)
    (Θ' : HeckeEigensystem ℚ ℂ) (R' : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ')
    (hR' : IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ' R')
    (hcl :
      ∀ (w : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (tys : ArchTypeFamily ℚ),
        IsIsotypicCuspFormAt ℚ (windowPins c u d₁ d₂ T) R'.centralChar Θ'.level R'.exceptionalSet
          Θ'.ofRawCentral w →
        w ∈ archCutSubmodule ℚ tys → w ∈ V₀) :
    ∀ pi : AdmIdx × ι₀,
      coordMap c u d₁ d₂ T q W ι₀ Φ Θ' R' hR' (generator q R'.toFun) pi ∈
        LocalNewvector.FixedPullback.fixedBy W
          {x : GL (Fin 2) ℚ_[q] |
            (AdelicDock.padicToAdelic q x : AdelicGL2 (𝓞 ℚ) ℚ) ∈ (windowPins c u d₁ d₂ T).U Θ'.level} := by
  letI := LocalNewvector.AwayCarrier.stableAction q (genSpan q R'.toFun) (genSpan_padic_stable q R'.toFun)
  intro pi
  rw [LocalNewvector.FixedPullback.mem_fixedBy]
  intro x hx
  have h1 : (x • (generator q R'.toFun).1).toFn = (generator q R'.toFun).1.toFn := by
    rw [generator_val, LocalNewvector.Members.toFn_padic_smul]
    funext y
    exact R'.level_invariant y _ hx
  have hfix : x • generator q R'.toFun = generator q R'.toFun := Subtype.ext h1
  have hs : coordMap c u d₁ d₂ T q W ι₀ Φ Θ' R' hR' (x • generator q R'.toFun) =
      x • coordMap c u d₁ d₂ T q W ι₀ Φ Θ' R' hR' (generator q R'.toFun) :=
    coordMap_smul c u d₁ d₂ T hd hcov q V₀ hst W ι₀ Φ heqv Θ' R' hR' hcl x _
  rw [← Pi.smul_apply, ← hs, hfix]

end LocalNewvector.NearClassEmbedding
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

section

open NumberField

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.toFn_mk AdelicFnCarrier.mk_toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_zero AdelicFnCarrier.toFn_add AdelicFnCarrier.toFn_csmul AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def IsIrreducibleGLRep exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace AwayTranslation
p2m_open "LocalNewvector"

section Generic

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (N : Ideal (𝓞 ℚ))

private theorem isLocalLevelOne_of_isLevelOneMatrix
    {m : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hm : AdelicLevel.IsLevelOneMatrix (𝓞 ℚ) ℚ N m) :
    AdelicDock.IsLocalLevelOne (𝓞 ℚ) ℚ v N (Matrix.of fun i j => m i j v) := by
  obtain ⟨⟨hint, hll⟩, hlr⟩ := hm
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · simpa only [Matrix.of_apply] using hint i j v
  · simpa only [Matrix.of_apply] using hll v
  · have h := hlr v
    rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply] at h
    simpa only [Matrix.of_apply] using h

private theorem coe_finComponent_eq
    (g : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ((AdelicLevel.finComponent (𝓞 ℚ) ℚ v g :
        Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) _)
      = Matrix.of fun i j =>
          (g : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) i j v := by
  ext i j
  rw [AdelicLevel.finComponent_apply, Matrix.of_apply]

private theorem localEmbed_finComponent_mem_finiteLevelOne
    {g : Matrix.GeneralLinearGroup (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hg : g ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ N) :
    AdelicDock.localEmbed (𝓞 ℚ) ℚ v (AdelicLevel.finComponent (𝓞 ℚ) ℚ v g)
      ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ N := by
  rw [AdelicLevel.mem_finiteLevelOne_iff] at hg ⊢
  obtain ⟨h₁, h₂⟩ := hg
  rw [← map_inv, ← map_inv, AdelicDock.coe_localEmbed, AdelicDock.coe_localEmbed,
    AdelicDock.isLevelOneMatrix_localMat_iff, AdelicDock.isLevelOneMatrix_localMat_iff,
    coe_finComponent_eq, coe_finComponent_eq]
  exact ⟨isLocalLevelOne_of_isLevelOneMatrix v N h₁, isLocalLevelOne_of_isLevelOneMatrix v N h₂⟩

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

section Padic

variable (q : ℕ) [Fact q.Prime]

private theorem exists_padicToAdelic_mul_of_mem_levelOne_inf (N : Ideal (𝓞 ℚ))
    (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (hg : g ∈ AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ) :
    ∃ x : Matrix.GeneralLinearGroup (Fin 2) ℚ_[q],
      x ∈ (AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ).comap
          (AdelicDock.padicToAdelic q) ∧
      ∃ h ∈ AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ,
        IsAwayFromQ q h ∧ g = AdelicDock.padicToAdelic q x * h := by
  obtain ⟨hg₁, -⟩ := Subgroup.mem_inf.mp hg

  set c := AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q) (AdelicLevel.glFin (𝓞 ℚ) ℚ g)
    with hc
  set x := padicGLInv q c with hx
  have hxc : AdelicDock.padicGL q x = c := padicGL_padicGLInv q c

  have hxU : AdelicDock.padicToAdelic q x ∈
      AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [AdelicLevel.mem_levelOne_iff, AdelicDock.glFin_padicToAdelic, AdelicDock.padicToFinAdelic_apply,
        hxc, hc]
      exact localEmbed_finComponent_mem_finiteLevelOne _ N (AdelicLevel.mem_levelOne_iff.mp hg₁)
    · rw [AutomorphicForm.mem_finiteAdelicGL2Subgroup_iff]
      exact AdelicDock.glArch_padicToAdelic q x
  refine ⟨x, Subgroup.mem_comap.mpr hxU, (AdelicDock.padicToAdelic q x)⁻¹ * g,
    mul_mem (inv_mem hxU) hg, ?_, (mul_inv_cancel_left _ _).symm⟩

  unfold IsAwayFromQ
  rw [map_mul, map_inv, map_mul, map_inv, AdelicDock.glFin_padicToAdelic,
    AdelicDock.finComponent_padicToFinAdelic_self, hxc, ← hc]
  exact inv_mul_cancel c

private noncomputable def awayGroup (N : Ideal (𝓞 ℚ)) : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :=
  (AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ) ⊓
    ((AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)).comp (AdelicLevel.glFin (𝓞 ℚ) ℚ)).ker

private theorem mem_awayGroup_iff (N : Ideal (𝓞 ℚ)) (h : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    h ∈ awayGroup q N ↔
      h ∈ AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ ∧ IsAwayFromQ q h := by
  simp only [awayGroup, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.comp_apply, IsAwayFromQ]

private theorem awayGroup_le (N : Ideal (𝓞 ℚ)) :
    awayGroup q N ≤ AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ :=
  inf_le_left

private theorem exists_mem_comap_mul_mem_awayGroup (N : Ideal (𝓞 ℚ)) (u : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)
    (hu : u ∈ AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ) :
    ∃ k ∈ (AdelicLevel.levelOne (𝓞 ℚ) ℚ N ⊓ AutomorphicForm.finiteAdelicGL2Subgroup ℚ).comap
        (AdelicDock.padicToAdelic q),
      ∃ h ∈ awayGroup q N, u = AdelicDock.padicToAdelic q k * h := by
  obtain ⟨x, hx, h, hh, hq, rfl⟩ := exists_padicToAdelic_mul_of_mem_levelOne_inf q N u hu
  exact ⟨x, hx, h, (mem_awayGroup_iff q N h).mpr ⟨hh, hq⟩, rfl⟩

end Padic
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end LocalNewvector.AwayTranslation
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

open NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm AutomorphicForm.CuspidalConstituent"
p2m_open "LocalNewvector P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.LocalNewvector"

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.toFn_mk AdelicFnCarrier.mk_toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_zero AdelicFnCarrier.toFn_add AdelicFnCarrier.toFn_csmul AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def IsIrreducibleGLRep exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace AwayCarrier
p2m_open "LocalNewvector"

variable (q : ℕ) [Fact q.Prime]

private def awayCarrier (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) (Uaw : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (tys : ArchTypeFamily ℚ) : Submodule ℂ (AdelicFnCarrier ℚ) where
  carrier := {ψ | ψ.toFn ∈ V ∧ (∀ h ∈ Uaw, rightTranslate ℚ h ψ.toFn = ψ.toFn) ∧
    ψ.toFn ∈ archCutSubmodule ℚ tys}
  zero_mem' := ⟨V.zero_mem, fun _ _ => funext fun _ => rfl, (archCutSubmodule ℚ tys).zero_mem⟩
  add_mem' := fun ha hb =>
    ⟨V.add_mem ha.1 hb.1,
      fun h hh => funext fun x => congrArg₂ (· + ·) (congrFun (ha.2.1 h hh) x) (congrFun (hb.2.1 h hh) x),
      (archCutSubmodule ℚ tys).add_mem ha.2.2 hb.2.2⟩
  smul_mem' := fun c {_a} ha =>
    ⟨V.smul_mem c ha.1, fun h hh => funext fun x => congrArg (c • ·) (congrFun (ha.2.1 h hh) x),
      (archCutSubmodule ℚ tys).smul_mem c ha.2.2⟩

private def fixedCarrier (U₀ : Subgroup (GL (Fin 2) ℚ_[q])) : Submodule ℂ (AdelicFnCarrier ℚ) where
  carrier := {ψ | ∀ k ∈ U₀, k • ψ = ψ}
  zero_mem' := fun k _ => smul_zero k
  add_mem' := fun {a b} ha hb k hk => by rw [smul_add, ha k hk, hb k hk]
  smul_mem' := fun c {a} ha k hk => by rw [smul_comm k c a, ha k hk]

private noncomputable def localLevel (N₀ : Ideal (𝓞 ℚ)) : Subgroup (GL (Fin 2) ℚ_[q]) :=
  (levelOne (𝓞 ℚ) ℚ N₀ ⊓ finiteAdelicGL2Subgroup ℚ).comap (AdelicDock.padicToAdelic q)

variable {q}

private theorem smul_mem_awayCarrier {V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)} {Uaw : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)}
    {tys : ArchTypeFamily ℚ}
    (hV : ∀ (ψ : AdelicFnCarrier ℚ) (x : GL (Fin 2) ℚ_[q]), ψ.toFn ∈ V → (x • ψ).toFn ∈ V)
    (hcomm : ∀ h ∈ Uaw, ∀ x : GL (Fin 2) ℚ_[q], Commute (AdelicDock.padicToAdelic q x) h)
    (harch : ∀ f ∈ archCutSubmodule ℚ tys, ∀ x : GL (Fin 2) ℚ_[q],
      (fun y => f (y * AdelicDock.padicToAdelic q x)) ∈ archCutSubmodule ℚ tys)
    (x : GL (Fin 2) ℚ_[q]) {ψ : AdelicFnCarrier ℚ} (hψ : ψ ∈ awayCarrier V Uaw tys) :
    x • ψ ∈ awayCarrier V Uaw tys := by
  obtain ⟨hψV, hfix, hcut⟩ := hψ
  refine ⟨hV ψ x hψV, fun h hh => funext fun y => ?_, harch _ hcut x⟩
  show ψ.toFn (y * h * AdelicDock.padicToAdelic q x) = ψ.toFn (y * AdelicDock.padicToAdelic q x)
  rw [mul_assoc, ← (hcomm h hh x).eq, ← mul_assoc]
  exact congrFun (hfix h hh) (y * AdelicDock.padicToAdelic q x)

private theorem toFn_image_awayCarrier_inf_fixedCarrier {V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)}
    {Uaw : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)} {tys : ArchTypeFamily ℚ} (pins : CarrierPins ℚ) (N₀ : Ideal (𝓞 ℚ))
    (hU : pins.U N₀ = levelOne (𝓞 ℚ) ℚ N₀ ⊓ finiteAdelicGL2Subgroup ℚ) (hUaw : Uaw ≤ pins.U N₀)
    (hsplit : ∀ u ∈ pins.U N₀, ∃ k ∈ localLevel q N₀, ∃ h ∈ Uaw, u = AdelicDock.padicToAdelic q k * h) :
    {f | ∃ ψ ∈ awayCarrier V Uaw tys ⊓ fixedCarrier q (localLevel q N₀), ψ.toFn = f} =
      ↑(V ⊓ levelInvariantSubmodule ℚ pins N₀ ⊓ archCutSubmodule ℚ tys) := by
  ext f
  constructor
  · rintro ⟨ψ, ⟨⟨hψV, hfix, hcut⟩, hfx⟩, rfl⟩
    refine ⟨⟨hψV, fun g u hu => ?_⟩, hcut⟩
    obtain ⟨k, hk, h, hh, rfl⟩ := hsplit u hu
    calc ψ.toFn (g * (AdelicDock.padicToAdelic q k * h))
        = ψ.toFn (g * AdelicDock.padicToAdelic q k * h) := congrArg ψ.toFn (mul_assoc _ _ _).symm
      _ = ψ.toFn (g * AdelicDock.padicToAdelic q k) := congrFun (hfix h hh) (g * AdelicDock.padicToAdelic q k)
      _ = (k • ψ).toFn g := rfl
      _ = ψ.toFn g := by rw [hfx k hk]
  · rintro ⟨⟨hfV, hflev⟩, hfcut⟩
    have hpad : ∀ k ∈ localLevel q N₀, AdelicDock.padicToAdelic q k ∈ pins.U N₀ := fun k hk => by
      rw [hU]; exact hk
    exact ⟨AdelicFnCarrier.mk f, ⟨⟨hfV, fun h hh => funext fun y => hflev y h (hUaw hh), hfcut⟩,
      fun k hk => AdelicFnCarrier.ext fun y => hflev y _ (hpad k hk)⟩, rfl⟩

private theorem finiteDimensional_awayCarrier_inf_fixedCarrier {V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)}
    {Uaw : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)} {tys : ArchTypeFamily ℚ} (pins : CarrierPins ℚ) (N₀ : Ideal (𝓞 ℚ))
    (hU : pins.U N₀ = levelOne (𝓞 ℚ) ℚ N₀ ⊓ finiteAdelicGL2Subgroup ℚ) (hUaw : Uaw ≤ pins.U N₀)
    (hsplit : ∀ u ∈ pins.U N₀, ∃ k ∈ localLevel q N₀, ∃ h ∈ Uaw, u = AdelicDock.padicToAdelic q k * h)
    (hfd : FiniteDimensional ℂ ↥(V ⊓ levelInvariantSubmodule ℚ pins N₀ ⊓ archCutSubmodule ℚ tys)) :
    FiniteDimensional ℂ ↥(awayCarrier V Uaw tys ⊓ fixedCarrier q (localLevel q N₀)) := by
  have hsub : ∀ ψ ∈ awayCarrier V Uaw tys ⊓ fixedCarrier q (localLevel q N₀),
      ψ.toFn ∈ V ⊓ levelInvariantSubmodule ℚ pins N₀ ⊓ archCutSubmodule ℚ tys := fun ψ hψ =>
    (toFn_image_awayCarrier_inf_fixedCarrier (V := V) (Uaw := Uaw) (tys := tys) pins N₀ hU hUaw hsplit).le
      ⟨ψ, hψ, rfl⟩
  let L : ↥(awayCarrier V Uaw tys ⊓ fixedCarrier q (localLevel q N₀)) →ₗ[ℂ]
      ↥(V ⊓ levelInvariantSubmodule ℚ pins N₀ ⊓ archCutSubmodule ℚ tys) :=
    { toFun := fun ψ => ⟨ψ.1.toFn, hsub ψ.1 ψ.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI := hfd
  exact FiniteDimensional.of_injective L fun a b hab =>
    Subtype.ext (AdelicFnCarrier.ext fun g => congrFun (congrArg Subtype.val hab) g)

private theorem awayCarrier_inf_fixedCarrier_ne_bot {V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)}
    {Uaw : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)} {tys : ArchTypeFamily ℚ} (pins : CarrierPins ℚ) (N₀ : Ideal (𝓞 ℚ))
    (hUaw : Uaw ≤ pins.U N₀) (hpad : ∀ k ∈ localLevel q N₀, AdelicDock.padicToAdelic q k ∈ pins.U N₀)
    (hne : V ⊓ levelInvariantSubmodule ℚ pins N₀ ⊓ archCutSubmodule ℚ tys ≠ ⊥) :
    awayCarrier V Uaw tys ⊓ fixedCarrier q (localLevel q N₀) ≠ ⊥ := by
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨⟨hfV, hflev⟩, hfcut⟩ := hf
  refine (Submodule.ne_bot_iff _).mpr ⟨AdelicFnCarrier.mk f, ⟨⟨hfV, fun h hh => funext fun y => ?_, hfcut⟩,
    fun k hk => AdelicFnCarrier.ext fun y => ?_⟩, AdelicFnCarrier.mk_ne_zero_of_ne_zero hf0⟩
  · exact hflev y h (hUaw hh)
  · exact hflev y _ (hpad k hk)

private theorem finiteDimensional_of_fixed (q : ℕ) [Fact q.Prime] (Z : Submodule ℂ (AdelicFnCarrier ℚ))
    (hZst : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ ψ ∈ Z, x • ψ ∈ Z) (U : Set (GL (Fin 2) ℚ_[q]))
    (C : Submodule ℂ (AdelicFnCarrier ℚ)) (hC : ∀ ψ : AdelicFnCarrier ℚ, ψ ∈ C ↔ ψ ∈ Z ∧ ∀ k ∈ U, k • ψ = ψ)
    [FiniteDimensional ℂ ↥C] (F₀ : Submodule ℂ ↥Z)
    (hF₀ : letI := stableAction q Z hZst; ∀ z : ↥Z, z ∈ F₀ ↔ ∀ k ∈ U, k • z = z) :
    FiniteDimensional ℂ ↥F₀ := by
  letI := stableAction q Z hZst
  let f : ↥F₀ →ₗ[ℂ] ↥C :=
    { toFun := fun w => ⟨((w : ↥Z) : AdelicFnCarrier ℚ), (hC _).mpr ⟨(w : ↥Z).2, fun k hk =>
        congrArg Subtype.val ((hF₀ (w : ↥Z)).mp w.2 k hk)⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective f fun a b hab => ?_
  have h : ((f a : ↥C) : AdelicFnCarrier ℚ) = ((f b : ↥C) : AdelicFnCarrier ℚ) := congrArg Subtype.val hab
  exact Subtype.ext (Subtype.ext h)

end LocalNewvector.AwayCarrier
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.toFn_mk AdelicFnCarrier.mk_toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_zero AdelicFnCarrier.toFn_add AdelicFnCarrier.toFn_csmul AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def IsIrreducibleGLRep exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace NearClassEmbedding
p2m_open "LocalNewvector"

open LocalNewvector.AwayCarrier LocalNewvector.AwayTranslation

private theorem finiteDimensional_fixedBy_localLevel (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (q : ℕ) [Fact q.Prime] (V₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hst : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ V₀ → (x • ψ).toFn ∈ V₀)
    (hfd : ∀ (N : Ideal (𝓞 ℚ)), N ≠ ⊥ → ∀ tys : ArchTypeFamily ℚ, FiniteDimensional ℂ
        ↥(V₀ ⊓ levelInvariantSubmodule ℚ (windowPins c u d₁ d₂ T) N ⊓ archCutSubmodule ℚ tys))
    (W : Type) [AddCommGroup W] [Module ℂ W] [DistribMulAction (GL (Fin 2) ℚ_[q]) W]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ W]
    (hW : LocalNewvector.IsIrreducibleGLRep q W) (ι₀ : Type) (Φ : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] (ι₀ →₀ W))
    (hinj : ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V₀ → Φ ψ = 0 → ψ = 0)
    (heqv : ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V₀ → ∀ x : GL (Fin 2) ℚ_[q], Φ (x • ψ) = x • Φ ψ)
    (N₀ : Ideal (𝓞 ℚ)) (hN₀ : N₀ ≠ ⊥) (tys₀ : ArchTypeFamily ℚ)
    (hne : V₀ ⊓ levelInvariantSubmodule ℚ (windowPins c u d₁ d₂ T) N₀ ⊓ archCutSubmodule ℚ tys₀ ≠ ⊥) :
    FiniteDimensional ℂ ↥(LocalNewvector.FixedPullback.fixedBy (V := W)
      {x : GL (Fin 2) ℚ_[q] |
        (AdelicDock.padicToAdelic q x : AdelicGL2 (𝓞 ℚ) ℚ) ∈ (windowPins c u d₁ d₂ T).U N₀}) := by
  have hVst : ∀ (ψ : AdelicFnCarrier ℚ) (x : GL (Fin 2) ℚ_[q]), ψ.toFn ∈ V₀ → (x • ψ).toFn ∈ V₀ :=
    fun ψ x hψ => hst x ψ hψ
  have hcomm : ∀ h ∈ awayGroup q N₀, ∀ x : GL (Fin 2) ℚ_[q], Commute (AdelicDock.padicToAdelic q x) h :=
    fun h hh x => padicToAdelic_mul_comm_of_finComponent_eq_one q h ((mem_awayGroup_iff q N₀ h).mp hh).2 x
  have hU : (windowPins c u d₁ d₂ T).U N₀ = levelOne (𝓞 ℚ) ℚ N₀ ⊓ finiteAdelicGL2Subgroup ℚ := rfl
  have hUaw : awayGroup q N₀ ≤ (windowPins c u d₁ d₂ T).U N₀ := by rw [hU]; exact awayGroup_le q N₀
  have hsplit : ∀ v ∈ (windowPins c u d₁ d₂ T).U N₀,
      ∃ k ∈ localLevel q N₀, ∃ h ∈ awayGroup q N₀, v = AdelicDock.padicToAdelic q k * h := by
    intro v hv
    rw [hU] at hv
    exact exists_mem_comap_mul_mem_awayGroup q N₀ v hv
  have hpad : ∀ k ∈ localLevel q N₀, AdelicDock.padicToAdelic q k ∈ (windowPins c u d₁ d₂ T).U N₀ := by
    intro k hk
    rw [hU]
    exact Subgroup.mem_comap.mp hk
  have harch : ∀ f ∈ archCutSubmodule ℚ tys₀, ∀ x : GL (Fin 2) ℚ_[q],
      (fun y => f (y * AdelicDock.padicToAdelic q x)) ∈ archCutSubmodule ℚ tys₀ :=
    fun f hf x => comp_mul_padicToAdelic_mem_archCutSubmodule hf q x

  set Z : Submodule ℂ (AdelicFnCarrier ℚ) := awayCarrier V₀ (awayGroup q N₀) tys₀ with hZdef
  have hZst : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ ψ ∈ Z, x • ψ ∈ Z := fun x ψ hψ => smul_mem_awayCarrier hVst hcomm harch x hψ
  have hC : ∀ ψ : AdelicFnCarrier ℚ, ψ ∈ Z ⊓ fixedCarrier q (localLevel q N₀) ↔
      ψ ∈ Z ∧ ∀ k ∈ (localLevel q N₀ : Set (GL (Fin 2) ℚ_[q])), k • ψ = ψ := fun ψ => Iff.rfl
  haveI hCfd : FiniteDimensional ℂ ↥(Z ⊓ fixedCarrier q (localLevel q N₀)) :=
    finiteDimensional_awayCarrier_inf_fixedCarrier (windowPins c u d₁ d₂ T) N₀ hU hUaw hsplit (hfd N₀ hN₀ tys₀)
  have hCne : Z ⊓ fixedCarrier q (localLevel q N₀) ≠ ⊥ :=
    awayCarrier_inf_fixedCarrier_ne_bot (windowPins c u d₁ d₂ T) N₀ hUaw hpad hne
  letI : DistribMulAction (GL (Fin 2) ℚ_[q]) ↥Z := stableAction q Z hZst
  haveI : SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ ↥Z := stableAction_smulCommClass q Z hZst
  haveI hF₀ :
      FiniteDimensional ℂ ↥(LocalNewvector.FixedPullback.fixedBy ↥Z (localLevel q N₀ : Set (GL (Fin 2) ℚ_[q]))) :=
    finiteDimensional_of_fixed q Z hZst _ (Z ⊓ fixedCarrier q (localLevel q N₀)) hC _ fun _ => Iff.rfl

  let L : ↥Z →ₗ[ℂ] (ι₀ →₀ W) := Φ.comp Z.subtype
  have hL : Function.Injective L := by
    intro a b hab
    have h0 : Φ ((a : AdelicFnCarrier ℚ) - b) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hab
    exact Subtype.ext (sub_eq_zero.mp (hinj _ (Z.sub_mem a.2 b.2).1 h0))
  have hLx : ∀ (x : GL (Fin 2) ℚ_[q]) (n : ↥Z), L (x • n) = x • L n := by
    intro x n
    show Φ ((x • n : ↥Z) : AdelicFnCarrier ℚ) = x • Φ (n : AdelicFnCarrier ℚ)
    rw [stableAction_coe_smul q Z hZst x n]
    exact heqv _ n.2.1 x
  obtain ⟨κ, f, hf, htop⟩ :=
    LocalNewvector.exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep q W ↥Z hW ι₀ L hL hLx

  obtain ⟨ψ, hψ, hψ0⟩ := (Submodule.ne_bot_iff _).mp hCne
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
    by_contra hall
    have hall' : ∀ i, f i = 0 := fun i => Classical.byContradiction fun h => hall ⟨i, h⟩
    have hbot : (⨆ i, LinearMap.range (f i)) = ⊥ :=
      eq_bot_iff.mpr (iSup_le fun i => by rw [hall' i, LinearMap.range_zero])
    have hz : (⟨ψ, hψ.1⟩ : ↥Z) ∈ (⊥ : Submodule ℂ ↥Z) := by
      rw [← hbot, htop]
      exact Submodule.mem_top
    exact hψ0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).mp hz))
  have hfi : Function.Injective (f i) :=
    LocalNewvector.FixedPullback.injective_of_forall_submodule_eq (f i) (hf i) hW.2 hi
  have key :
      FiniteDimensional ℂ ↥(LocalNewvector.FixedPullback.fixedBy W (localLevel q N₀ : Set (GL (Fin 2) ℚ_[q]))) :=
    LocalNewvector.FixedPullback.finiteDimensional_fixedBy_of_injective (f i) (hf i) hfi
  exact key

end LocalNewvector.NearClassEmbedding
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

namespace LocalNewvector
p2m_export "LocalNewvector" "AdelicFnCarrier AdelicFnCarrier.mk AdelicFnCarrier.toFn AdelicFnCarrier.toFn_mk AdelicFnCarrier.mk_toFn AdelicFnCarrier.ext AdelicFnCarrier.toFn_zero AdelicFnCarrier.toFn_add AdelicFnCarrier.toFn_csmul AdelicFnCarrier.toFn_smul AdelicFnCarrier.mk_ne_zero_of_ne_zero AdelicFnCarrier.padic_smul_def IsIrreducibleGLRep exists_iSup_range_eq_top_of_injective_linearMap_finsupp_of_isIrreducibleGLRep exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top"
namespace NearClassEmbedding
p2m_open "LocalNewvector"

private theorem exists_constituent_irreducible (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Θ : HeckeEigensystem ℚ ℂ) (q : ℕ) [Fact q.Prime]
    (Θ₁ : HeckeEigensystem ℚ ℂ) (hΘ₁ : Θ₁.AgreesAwayFromFinite Θ)
    (R₁ : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ₁)
    (hR₁ : IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ₁ R₁) :
    ∃ V₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      (∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ V₀ → (x • ψ).toFn ∈ V₀) ∧
      (∀ (Θ' : HeckeEigensystem ℚ ℂ) (_ : Θ'.AgreesAwayFromFinite Θ)
        (R' : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ')
        (_ : IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ' R'),
        ∀ (w : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (tys : ArchTypeFamily ℚ),
          IsIsotypicCuspFormAt ℚ (windowPins c u d₁ d₂ T) R'.centralChar Θ'.level R'.exceptionalSet
            Θ'.ofRawCentral w →
          w ∈ archCutSubmodule ℚ tys → w ∈ V₀) ∧
      (∀ (N : Ideal (𝓞 ℚ)), N ≠ ⊥ → ∀ tys : ArchTypeFamily ℚ, FiniteDimensional ℂ
        ↥(V₀ ⊓ CuspidalConstituent.levelInvariantSubmodule ℚ (windowPins c u d₁ d₂ T) N ⊓ archCutSubmodule ℚ tys)) ∧
      ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : DistribMulAction (GL (Fin 2) ℚ_[q]) W)
        (_ : SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ W),
        LocalNewvector.IsIrreducibleGLRep q W ∧
        ∃ (ι₀ : Type) (Φ : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] (ι₀ →₀ W)),
          (∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V₀ → Φ ψ = 0 → ψ = 0) ∧
          ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V₀ →
            ∀ x : GL (Fin 2) ℚ_[q], Φ (x • ψ) = x • Φ ψ := by
  obtain ⟨V₀, hV₀, ⟨S₁, -, m₁⟩, -, N₀, hN₀, tys₀, hne⟩ :=
    exists_constituent_of_genuine c u d₁ d₂ T hd hcov R₁ hR₁
  refine ⟨V₀, ?_, ?_, ?_, ?_⟩
  · intro x ψ hψ
    exact LocalNewvector.Members.toFn_smul_mem_of_isCuspConstituent (windowPins c u d₁ d₂ T) R₁.centralChar V₀
      hV₀ q x ψ hψ
  · intro Θ' hΘ' R' hR' w tys hiso hcut
    obtain ⟨V', hV', ⟨S', -, m'⟩, hcl', -⟩ := exists_constituent_of_genuine c u d₁ d₂ T hd hcov R' hR'
    have hVV : V₀ = V' :=
      constituent_eq_of_agreesAwayFromFinite c u d₁ d₂ T hd hcov (hmono_of_window c u d₁ d₂ T) hΘ₁ hΘ' R₁ hR₁
        R' hR' hV₀ m₁ hV' m'
    rw [hVV]
    exact hcl' w tys hiso hcut
  · intro N hN tys
    exact AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent ℚ
      c u d₁ d₂ T hd hcov R₁.centralChar N hN tys V₀ hV₀
  · exact AutomorphicForm.exists_isIrreducibleGLRep_injective_linearMap_finsupp_of_isCuspConstituent c u d₁ d₂ T
      hd hcov R₁.centralChar V₀ hV₀ N₀ hN₀ tys₀ hne q

private theorem exists_cover_genSpan (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Θ : HeckeEigensystem ℚ ℂ) (q : ℕ) [Fact q.Prime] (V₀ : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hst : ∀ (x : GL (Fin 2) ℚ_[q]) (ψ : LocalNewvector.AdelicFnCarrier ℚ), ψ.toFn ∈ V₀ → (x • ψ).toFn ∈ V₀)
    (hfd : ∀ (N : Ideal (𝓞 ℚ)), N ≠ ⊥ → ∀ tys : ArchTypeFamily ℚ, FiniteDimensional ℂ
        ↥(V₀ ⊓ CuspidalConstituent.levelInvariantSubmodule ℚ (windowPins c u d₁ d₂ T) N ⊓ archCutSubmodule ℚ tys))
    (W : Type) [AddCommGroup W] [Module ℂ W] [DistribMulAction (GL (Fin 2) ℚ_[q]) W]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ W]
    (hW : LocalNewvector.IsIrreducibleGLRep q W) (ι₀ : Type) (Φ : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] (ι₀ →₀ W))
    (hinj : ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V₀ → Φ ψ = 0 → ψ = 0)
    (heqv : ∀ ψ : LocalNewvector.AdelicFnCarrier ℚ, ψ.toFn ∈ V₀ → ∀ x : GL (Fin 2) ℚ_[q], Φ (x • ψ) = x • Φ ψ)
    (Θ' : HeckeEigensystem ℚ ℂ) (hΘ' : Θ'.AgreesAwayFromFinite Θ)
    (R' : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ')
    (hR' : IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ' R')
    (hcl :
      ∀ (w : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (tys : ArchTypeFamily ℚ),
        IsIsotypicCuspFormAt ℚ (windowPins c u d₁ d₂ T) R'.centralChar Θ'.level R'.exceptionalSet
          Θ'.ofRawCentral w →
        w ∈ archCutSubmodule ℚ tys → w ∈ V₀) :
    ∃ (κ : Type) (f : κ → (W →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ)),
      (∀ (k : κ) (x : GL (Fin 2) ℚ_[q]) (v : W), f k (x • v) = x • f k v) ∧
      (∀ k, LinearMap.range (f k) ≤ genSpan q R'.toFun) ∧
      genSpan q R'.toFun ≤ ⨆ k, LinearMap.range (f k) := by
  letI := LocalNewvector.AwayCarrier.stableAction q (genSpan q R'.toFun) (genSpan_padic_stable q R'.toFun)
  haveI := LocalNewvector.AwayCarrier.stableAction_smulCommClass q (genSpan q R'.toFun)
    (genSpan_padic_stable q R'.toFun)

  have hm₀ : LocalNewvector.AdelicFnCarrier.mk R'.toFun ≠ 0 := by
    intro h
    obtain ⟨g, hg⟩ := R'.exists_ne_zero
    exact hg (congrFun (congrArg LocalNewvector.AdelicFnCarrier.toFn h) g)
  obtain ⟨tys₀, fa₀, hfa₀, hbf₀, hne₀⟩ := exists_archOp_toFn_ne_zero_of_mem_genSpan q
    (show Continuous R'.toFun from hR') _ (generator_mem_genSpan q R'.toFun) hm₀
  have hlc := archOp_toFun_mem_levelInvariantSubmodule_inf_archCutSubmodule c u d₁ d₂ T Θ' R' hR' hfa₀ hbf₀
  have hne :
      V₀ ⊓ CuspidalConstituent.levelInvariantSubmodule ℚ (windowPins c u d₁ d₂ T) Θ'.level ⊓
        archCutSubmodule ℚ tys₀ ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨AutomorphicForm.ArchOp.archOp fa₀ R'.toFun,
      Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨archOp_toFun_mem c u d₁ d₂ T hd hcov V₀ Θ' R' hR' hcl hfa₀ hbf₀,
        (Submodule.mem_inf.1 hlc).1⟩, (Submodule.mem_inf.1 hlc).2⟩, hne₀⟩

  haveI := finiteDimensional_fixedBy_localLevel c u d₁ d₂ T q V₀ hst hfd W hW ι₀ Φ hinj heqv Θ'.level
    Θ'.level_ne_bot tys₀ hne

  have hgen : Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • generator q R'.toFun) = ⊤ := by
    apply Submodule.map_injective_of_injective (genSpan q R'.toFun).injective_subtype
    rw [Submodule.map_subtype_top, Submodule.map_span, ← Set.range_comp]
    show Submodule.span ℂ _ =
      Submodule.span ℂ {χ | ∃ x : GL (Fin 2) ℚ_[q], χ = x • LocalNewvector.AdelicFnCarrier.mk R'.toFun}
    congr 1
    ext χ
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩

  obtain ⟨κ, F, hF, htop⟩ := LocalNewvector.CoordCover.exists_cover_of_coordMap q hW
    (coordMap c u d₁ d₂ T q W ι₀ Φ Θ' R' hR')
    (coordMap_injective c u d₁ d₂ T hd hcov q V₀ hst W ι₀ Φ hinj Θ' R' hR' hcl)
    (coordMap_smul c u d₁ d₂ T hd hcov q V₀ hst W ι₀ Φ heqv Θ' R' hR' hcl) (generator q R'.toFun) hgen
    (LocalNewvector.FixedPullback.fixedBy W
      {x : GL (Fin 2) ℚ_[q] |
        (AdelicDock.padicToAdelic q x : AdelicGL2 (𝓞 ℚ) ℚ) ∈ (windowPins c u d₁ d₂ T).U Θ'.level})
    (coordMap_generator_mem_fixedBy c u d₁ d₂ T hd hcov q V₀ hst W ι₀ Φ heqv Θ' R' hR' hcl)
  refine ⟨κ, fun k => (genSpan q R'.toFun).subtype ∘ₗ F k, ?_, ?_, ?_⟩
  · intro k x v
    show ((F k (x • v) : ↥(genSpan q R'.toFun)) : LocalNewvector.AdelicFnCarrier ℚ) =
      x • ((F k v : ↥(genSpan q R'.toFun)) : LocalNewvector.AdelicFnCarrier ℚ)
    rw [hF k x v]
    rfl
  · intro k
    rw [LinearMap.range_comp]
    exact Submodule.map_subtype_le _ _
  · have h1 : (⨆ k, LinearMap.range ((genSpan q R'.toFun).subtype ∘ₗ F k)) =
        Submodule.map (genSpan q R'.toFun).subtype (⨆ k, LinearMap.range (F k)) := by
      rw [Submodule.map_iSup]
      exact iSup_congr fun k => LinearMap.range_comp _ _
    rw [h1, htop, Submodule.map_subtype_top]

private theorem exists_cover_span_of_cover_genSpan (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (Θ : HeckeEigensystem ℚ ℂ) (q : ℕ) [Fact q.Prime]
    (W : Type) [AddCommGroup W] [Module ℂ W] [DistribMulAction (GL (Fin 2) ℚ_[q]) W]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ W]
    (hgen : ∀ (Θ' : HeckeEigensystem ℚ ℂ) (_ : Θ'.AgreesAwayFromFinite Θ)
        (R' : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ')
        (_ : IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ' R'),
        ∃ (κ : Type) (f : κ → (W →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ)),
          (∀ (k : κ) (x : GL (Fin 2) ℚ_[q]) (v : W), f k (x • v) = x • f k v) ∧
          (∀ k, LinearMap.range (f k) ≤ genSpan q R'.toFun) ∧
          genSpan q R'.toFun ≤ ⨆ k, LinearMap.range (f k)) :
    (∀ (x : GL (Fin 2) ℚ_[q]), ∀ ψ ∈ Submodule.span ℂ (genSet c u d₁ d₂ T Θ),
      x • ψ ∈ Submodule.span ℂ (genSet c u d₁ d₂ T Θ)) ∧
    ∃ (κ : Type) (f : κ → (W →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ)),
      (∀ (k : κ) (x : GL (Fin 2) ℚ_[q]) (v : W), f k (x • v) = x • f k v) ∧
      (∀ k, LinearMap.range (f k) ≤ Submodule.span ℂ (genSet c u d₁ d₂ T Θ)) ∧
      Submodule.span ℂ (genSet c u d₁ d₂ T Θ) ≤ ⨆ k, LinearMap.range (f k) := by
  refine ⟨fun x => LocalNewvector.AwayCarrier.span_padic_stable q _ (genSet_smul_mem c u d₁ d₂ T Θ) x, ?_⟩
  choose κ' f' hf' hle' hmem' using exists_cover_of_mem_genSet c u d₁ d₂ T Θ q W hgen
  refine ⟨(χ : genSet c u d₁ d₂ T Θ) × κ' χ.1 χ.2, fun p => f' p.1.1 p.1.2 p.2, fun p => hf' p.1.1 p.1.2 p.2,
    fun p => hle' p.1.1 p.1.2 p.2, ?_⟩
  refine Submodule.span_le.2 fun χ hχ => ?_
  exact (iSup_le fun k => le_iSup (fun p : (χ : genSet c u d₁ d₂ T Θ) × κ' χ.1 χ.2 =>
    LinearMap.range (f' p.1.1 p.1.2 p.2)) ⟨⟨χ, hχ⟩, k⟩) (hmem' χ hχ)

private theorem exists_irreducible_cover (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Θ : HeckeEigensystem ℚ ℂ) (q : ℕ) [Fact q.Prime] :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : DistribMulAction (GL (Fin 2) ℚ_[q]) V)
      (_ : SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V),
      LocalNewvector.IsIrreducibleGLRep q V ∧
      (∀ (x : GL (Fin 2) ℚ_[q]), ∀ ψ ∈ Submodule.span ℂ (genSet c u d₁ d₂ T Θ),
        x • ψ ∈ Submodule.span ℂ (genSet c u d₁ d₂ T Θ)) ∧
      ∃ (κ : Type) (f : κ → (V →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ)),
        (∀ (k : κ) (x : GL (Fin 2) ℚ_[q]) (v : V), f k (x • v) = x • f k v) ∧
        (∀ k, LinearMap.range (f k) ≤ Submodule.span ℂ (genSet c u d₁ d₂ T Θ)) ∧
        Submodule.span ℂ (genSet c u d₁ d₂ T Θ) ≤ ⨆ k, LinearMap.range (f k) := by
  by_cases h : ∃ (Θ₁ : HeckeEigensystem ℚ ℂ) (_ : Θ₁.AgreesAwayFromFinite Θ)
      (R₁ : SmoothCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ₁),
      IsGenuineCuspRealizationAt ℚ (windowPins c u d₁ d₂ T) Θ₁ R₁
  · obtain ⟨Θ₁, hΘ₁, R₁, hR₁⟩ := h
    obtain ⟨V₀, hst, hcl, hfd, W, i₁, i₂, i₃, i₄, hW, ι₀, Φ, hinj, heqv⟩ :=
      exists_constituent_irreducible c u d₁ d₂ T hd hcov Θ q Θ₁ hΘ₁ R₁ hR₁
    obtain ⟨hS, κ, f, hf, hle, hge⟩ := exists_cover_span_of_cover_genSpan c u d₁ d₂ T Θ q W
      (fun Θ' hΘ' R' hR' => exists_cover_genSpan c u d₁ d₂ T hd hcov Θ q V₀ hst hfd W hW ι₀ Φ hinj heqv
        Θ' hΘ' R' hR' (hcl Θ' hΘ' R' hR'))
    exact ⟨W, i₁, i₂, i₃, i₄, hW, hS, κ, f, hf, hle, hge⟩
  · have hbot : Submodule.span ℂ (genSet c u d₁ d₂ T Θ) = ⊥ := by
      rw [Submodule.span_eq_bot]
      rintro χ ⟨g, Θ', hΘ', R', hR', rfl⟩
      exact (h ⟨Θ', hΘ', R', hR'⟩).elim
    letI := LocalNewvector.TrivialLine.trivialAction q
    refine ⟨ℂ, inferInstance, inferInstance, LocalNewvector.TrivialLine.trivialAction q,
      LocalNewvector.TrivialLine.trivialAction_smulCommClass q,
      LocalNewvector.TrivialLine.isIrreducibleGLRep_trivialAction q, ?_, PEmpty, fun e => e.elim, ?_, ?_, ?_⟩
    · intro x ψ hψ
      rw [hbot, Submodule.mem_bot] at hψ ⊢
      rw [hψ, smul_zero]
    · intro k
      exact k.elim
    · intro k
      exact k.elim
    · rw [hbot]
      exact bot_le

private theorem exists_linearMap_of_cover (q : ℕ) [Fact q.Prime]
    (S : Submodule ℂ (LocalNewvector.AdelicFnCarrier ℚ))
    (V : Type) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
    [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]
    (hV : LocalNewvector.IsIrreducibleGLRep q V) (hS : ∀ (x : GL (Fin 2) ℚ_[q]), ∀ ψ ∈ S, x • ψ ∈ S)
    (κ : Type) (f : κ → (V →ₗ[ℂ] LocalNewvector.AdelicFnCarrier ℚ))
    (hf : ∀ (k : κ) (x : GL (Fin 2) ℚ_[q]) (v : V), f k (x • v) = x • f k v)
    (hle : ∀ k, LinearMap.range (f k) ≤ S) (hge : S ≤ ⨆ k, LinearMap.range (f k)) :
    ∃ (ι : Type) (L : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] (ι →₀ V)),
      ∀ ψ ∈ S, (L ψ = 0 → ψ = 0) ∧ ∀ x : GL (Fin 2) ℚ_[q], L (x • ψ) = x • L ψ := by
  letI := LocalNewvector.AwayCarrier.stableAction q S hS
  haveI := LocalNewvector.AwayCarrier.stableAction_smulCommClass q S hS
  have hrange : ∀ (k : κ) (v : V), f k v ∈ S := fun k v => hle k (LinearMap.mem_range_self (f k) v)
  have hf' : ∀ (k : κ) (x : GL (Fin 2) ℚ_[q]) (v : V),
      (f k).codRestrict S (hrange k) (x • v) = x • (f k).codRestrict S (hrange k) v :=
    fun k x v => LocalNewvector.AwayCarrier.codRestrict_smul q S hS (f k) (hf k) (hrange k) x v
  have hmap : ∀ k, Submodule.map S.subtype (LinearMap.range ((f k).codRestrict S (hrange k))) =
      LinearMap.range (f k) := by
    intro k
    rw [← LinearMap.range_comp, LinearMap.subtype_comp_codRestrict]
  have htop : ⨆ k, LinearMap.range ((f k).codRestrict S (hrange k)) = ⊤ := by
    refine eq_top_iff.mpr ((Submodule.map_le_map_iff_of_injective S.injective_subtype _ _).mp ?_)
    rw [Submodule.map_subtype_top, Submodule.map_iSup]
    refine hge.trans (le_of_eq ?_)
    exact (iSup_congr hmap).symm
  obtain ⟨ι, L₀, hinj, hL₀⟩ :=
    LocalNewvector.exists_injective_linearMap_finsupp_of_isIrreducibleGLRep_of_iSup_range_eq_top q V (↥S) hV κ
      (fun k => (f k).codRestrict S (hrange k)) hf' htop
  obtain ⟨L, hL⟩ := LinearMap.exists_extend L₀
  refine ⟨ι, L, fun ψ hψ => ?_⟩
  have hLψ : L ψ = L₀ ⟨ψ, hψ⟩ := LinearMap.congr_fun hL ⟨ψ, hψ⟩
  refine ⟨fun h0 => ?_, fun x => ?_⟩
  · have hz : (⟨ψ, hψ⟩ : ↥S) = 0 := hinj (by rw [← hLψ, h0, map_zero])
    exact congrArg Subtype.val hz
  · have h1 : L (x • ψ) = L₀ ⟨x • ψ, hS x ψ hψ⟩ := LinearMap.congr_fun hL ⟨x • ψ, hS x ψ hψ⟩
    have h2 : (⟨x • ψ, hS x ψ hψ⟩ : ↥S) = x • (⟨ψ, hψ⟩ : ↥S) := rfl
    rw [h1, h2, hL₀, ← hLψ]

end LocalNewvector.NearClassEmbedding
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre.AutomorphicForm.SOTwoFourier"

theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hd : d₁ < d₂) (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Θ : HeckeEigensystem ℚ ℂ) (q : ℕ) [Fact q.Prime] :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : DistribMulAction (GL (Fin 2) ℚ_[q]) V)
      (_ : SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V),
      LocalNewvector.IsIrreducibleGLRep q V ∧
      ∃ (ι : Type) (L : LocalNewvector.AdelicFnCarrier ℚ →ₗ[ℂ] (ι →₀ V)),
        ∀ ψ ∈ Submodule.span ℂ
            {χ : LocalNewvector.AdelicFnCarrier ℚ |
              ∃ (g : AdelicGL2 (𝓞 ℚ) ℚ) (Θ' : HeckeEigensystem ℚ ℂ) (_ : Θ'.AgreesAwayFromFinite Θ)
                (R' : SmoothCuspRealizationAt ℚ
                  (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
                    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
                    (adelicBox ℚ))
                  Θ')
                (_ : IsGenuineCuspRealizationAt ℚ
                  (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
                    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
                    (adelicBox ℚ))
                  Θ' R'),
                χ = g • LocalNewvector.AdelicFnCarrier.mk R'.toFun},
          (L ψ = 0 → ψ = 0) ∧ ∀ x : GL (Fin 2) ℚ_[q], L (x • ψ) = x • L ψ := by
  obtain ⟨V, i₁, i₂, i₃, i₄, hV, hS, κ, f, hf, hle, hge⟩ :=
    LocalNewvector.NearClassEmbedding.exists_irreducible_cover c u d₁ d₂ T hd hcov Θ q
  obtain ⟨ι, L, hL⟩ :=
    LocalNewvector.NearClassEmbedding.exists_linearMap_of_cover q _ V hV hS κ f hf hle hge
  exact ⟨V, i₁, i₂, i₃, i₄, hV, ι, L, hL⟩

#print axioms solution

end S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre (solution)
