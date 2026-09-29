-- Prove2me | solution 1 for AutomorphicForm.adelicGLHaar_canonicalTruncationDomain_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/0448c771-a883-51ba-a406-c2873d0454a4

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_FnTwist
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_adelicGLHaar_canonicalTruncationDomain_pos
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open NumberField AutomorphicForm

noncomputable section

namespace POSB

variable (F : Type) [Field F] [NumberField F]

abbrev slab (d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}

abbrev Γ : Subgroup (AdelicGL2 (𝓞 F) F) := (globalPoints (𝓞 F) F).range

theorem countable_of_numberField : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

theorem countable_range_globalPoints :
    Countable ((globalPoints (𝓞 F) F).range : Subgroup (AdelicGL2 (𝓞 F) F)) := by
  haveI : Countable F := countable_of_numberField F
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  have hinj : Function.Injective
      (Units.val : (Matrix (Fin 2) (Fin 2) F)ˣ → Matrix (Fin 2) (Fin 2) F) := fun _ _ h => Units.ext h
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := hinj.countable
  exact (Set.countable_range (globalPoints (𝓞 F) F)).to_subtype

theorem globalPoints_mul_mem_slab_iff (a b : ℝ)
    (hpf : ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F x)) = 1)
    (γ : Γ F) (g : AdelicGL2 (𝓞 F) F) : (γ : AdelicGL2 (𝓞 F) F) * g ∈ slab F a b ↔ g ∈ slab F a b := by
  obtain ⟨x, hx⟩ := γ.2
  have hdet : NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 F) F) * g))
      = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, ← hx, hpf x, one_mul]
  show NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det ((γ : AdelicGL2 (𝓞 F) F) * g)) ∈ Set.Icc a b ↔
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b
  rw [hdet]

theorem smulInvariantMeasure_slabHaar (a b : ℝ) (hslab : MeasurableSet (slab F a b))
    (hpf : ∀ x : Matrix.GeneralLinearGroup (Fin 2) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 F) F x)) = 1) :
    SMulInvariantMeasure (Γ F) (AdelicGL2 (𝓞 F) F) ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F a b)) := by
  have _ := hslab
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨fun γ s hs => ?_⟩
  have hpre : (fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' slab F a b = slab F a b := by
    ext g
    exact globalPoints_mul_mem_slab_iff F a b hpf γ g
  have hmeas : MeasurableSet ((fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' s) :=
    measurable_const_mul (γ : AdelicGL2 (𝓞 F) F) hs
  calc (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F a b) ((fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' s)
      = adelicGLHaar (Fin 2) (𝓞 F) F ((fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' s ∩ slab F a b) :=
        Measure.restrict_apply hmeas
    _ = adelicGLHaar (Fin 2) (𝓞 F) F ((fun x : AdelicGL2 (𝓞 F) F => γ • x) ⁻¹' (s ∩ slab F a b)) := by
        rw [Set.preimage_inter, hpre]
    _ = adelicGLHaar (Fin 2) (𝓞 F) F (s ∩ slab F a b) :=
        measure_preimage_mul (adelicGLHaar (Fin 2) (𝓞 F) F) (γ : AdelicGL2 (𝓞 F) F) _
    _ = (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F a b) s := (Measure.restrict_apply hs).symm

end POSB

end

open NumberField AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    0 < adelicGLHaar (Fin 2) (𝓞 K) K (AutomorphicForm.canonicalTruncationDomain K α β) := by
  classical
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  set μ := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  set D := AutomorphicForm.canonicalTruncationDomain K α β with hD
  obtain ⟨-, -, -, hslabD, hFD⟩ := AutomorphicForm.canonicalTruncationData_isTruncationDatum K α β hα hαβ
  have hslabm : MeasurableSet (POSB.slab K α β) := NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc K α β
  haveI : Countable (POSB.Γ K) := POSB.countable_range_globalPoints K
  haveI : MeasurableConstSMul (POSB.Γ K) (AdelicGL2 (𝓞 K) K) := ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)⟩
  haveI : SMulInvariantMeasure (POSB.Γ K) (AdelicGL2 (𝓞 K) K) (μ.restrict (POSB.slab K α β)) :=
    POSB.smulInvariantMeasure_slabHaar K α β hslabm (fun x => AutomorphicForm.ideleNorm_det_globalPoints (F := K) x)

  have hslab_pos : 0 < μ (POSB.slab K α β) := by
    have hm : 0 < (α + β) / 2 := by linarith
    obtain ⟨z, -, hz⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K _ (Real.sqrt_pos.2 hm)
    have hdc : Continuous fun g : AdelicGL2 (𝓞 K) K =>
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) := by
      have hdet : Continuous (Matrix.GeneralLinearGroup.det : AdelicGL2 (𝓞 K) K → (AdeleRing (𝓞 K) K)ˣ) := by
        refine Units.continuous_iff.mpr ⟨?_, ?_⟩
        · exact Units.continuous_val.matrix_det
        · have : (fun g : AdelicGL2 (𝓞 K) K => ((Matrix.GeneralLinearGroup.det g)⁻¹ : (AdeleRing (𝓞 K) K)ˣ).val) =
              fun g => ((g⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det := by
            funext g; rw [← map_inv]; rfl
          rw [this]
          exact (Units.continuous_val.comp continuous_inv).matrix_det
      exact (NumberField.TateGlobal.continuous_ideleNorm K).comp hdet
    have hopen : IsOpen {g : AdelicGL2 (𝓞 K) K |
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo α β} :=
      isOpen_Ioo.preimage hdc
    have hne : ({g : AdelicGL2 (𝓞 K) K |
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo α β}).Nonempty := by
      refine ⟨centralScalar (𝓞 K) K z, ?_⟩
      show NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z)) ∈ Set.Ioo α β
      rw [det_centralScalar K, pow_two, NumberField.TateGlobal.ideleNorm_mul, hz, Real.mul_self_sqrt hm.le]
      constructor <;> linarith
    have h1 : 0 < μ {g : AdelicGL2 (𝓞 K) K |
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo α β} := hopen.measure_pos μ hne
    exact h1.trans_le (measure_mono fun g hg => Set.Ioo_subset_Icc_self hg)

  rw [pos_iff_ne_zero]
  intro hD0
  have hν : (μ.restrict (POSB.slab K α β)) D = 0 :=
    le_antisymm ((Measure.restrict_le_self _).trans (le_of_eq hD0)) bot_le
  have hzero : (μ.restrict (POSB.slab K α β)) Set.univ = 0 :=
    hFD.measure_zero_of_invariant Set.univ (fun γ => Set.smul_set_univ) (by rwa [Set.univ_inter])
  rw [Measure.restrict_apply_univ] at hzero
  exact hslab_pos.ne' hzero

end S_AutomorphicForm_adelicGLHaar_canonicalTruncationDomain_pos
end P2MW
export P2MW.S_AutomorphicForm_adelicGLHaar_canonicalTruncationDomain_pos (solution)
