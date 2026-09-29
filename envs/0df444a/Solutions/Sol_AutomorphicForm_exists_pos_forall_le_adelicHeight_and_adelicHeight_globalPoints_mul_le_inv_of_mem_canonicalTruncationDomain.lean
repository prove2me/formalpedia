-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/caa96ddb-fa48-579f-8ba2-67bb8e8cabeb

import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_AutomorphicForm_canonicalTruncationData_isTruncationDatum
import Theorems.Thm_NumberField_AdelicHeight_exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicHeight
open AutomorphicForm AutomorphicForm.WindowedSiegel

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace R1TruncationSeam

variable {F : Type} [Field F] [NumberField F]

theorem pow_le_adelicHeight_of_mem_centreCutSiegelSet {c u d₁ d₂ : ℝ} (hc : 0 ≤ c)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ centreCutSiegelSet F c u d₁ d₂) :
    c ^ (∑ w : InfinitePlace F, w.mult) ≤ adelicHeight F g := by
  have h := centreCutSiegelSet_subset_integralWindowedSiegelSet (F := F) (u := u) (d₁ := d₁)
    (d₂ := d₂) hc hg
  obtain ⟨hK, hfloor, -⟩ := h
  rw [adelicHeight_eq_archHeight_of_mem hK]
  exact hfloor

end R1TruncationSeam

open R1TruncationSeam in

theorem solution
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    ∃ h₀ : ℝ, 0 < h₀ ∧
      (∀ g ∈ AutomorphicForm.canonicalTruncationDomain F α β,
        h₀ ≤ NumberField.AdelicHeight.adelicHeight F g) ∧
      (∀ g ∈ AutomorphicForm.canonicalTruncationDomain F α β, ∀ γ : GL (Fin 2) F,
        (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 →
          NumberField.AdelicHeight.adelicHeight F (AutomorphicForm.globalPoints (𝓞 F) F γ * g) ≤ h₀⁻¹) := by
  obtain ⟨hc, hTc, hcov, -, -⟩ :=
    AutomorphicForm.canonicalTruncationData_isTruncationDatum F α β hα hαβ
  obtain ⟨κ, K, hκ, hκK⟩ :=
    NumberField.AdelicHeight.exists_forall_mul_adelicHeight_le_adelicHeight_mul_of_isCompact F
      (canonicalTruncationTranslates F α β) hTc
  set c := canonicalTruncationFloor F α β with hcdef
  set h₀ : ℝ := κ * c ^ (∑ w : InfinitePlace F, w.mult) with hh₀
  have hcpow : 0 < c ^ (∑ w : InfinitePlace F, w.mult) := pow_pos hc _
  have hh₀pos : 0 < h₀ := mul_pos hκ hcpow
  have hfloor : ∀ g ∈ AutomorphicForm.canonicalTruncationDomain F α β,
      h₀ ≤ NumberField.AdelicHeight.adelicHeight F g := by
    intro g hg
    have hg' := hcov hg
    simp only [Set.mem_iUnion, Set.mem_image] at hg'
    obtain ⟨y, hy, x, hx, rfl⟩ := hg'
    have h1 : c ^ (∑ w : InfinitePlace F, w.mult) ≤ adelicHeight F x :=
      pow_le_adelicHeight_of_mem_centreCutSiegelSet hc.le hx
    have h2 : κ * adelicHeight F x ≤ adelicHeight F (x * y) := (hκK x y hy).1
    calc h₀ = κ * c ^ (∑ w : InfinitePlace F, w.mult) := rfl
      _ ≤ κ * adelicHeight F x := mul_le_mul_of_nonneg_left h1 hκ.le
      _ ≤ adelicHeight F (x * y) := h2
  refine ⟨h₀, hh₀pos, hfloor, ?_⟩
  intro g hg γ hγ
  have hprod := adelicHeight_globalPoints_mul_mul_adelicHeight_le_one γ hγ g
  have hHg : 0 < adelicHeight F g := adelicHeight_pos g
  have hle : adelicHeight F (globalPoints (𝓞 F) F γ * g) ≤ (adelicHeight F g)⁻¹ := by
    rw [← one_div, le_div_iff₀ hHg]
    exact hprod
  exact hle.trans ((inv_le_inv₀ hHg hh₀pos).mpr (hfloor g hg))

end S_AutomorphicForm_exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_le_adelicHeight_and_adelicHeight_globalPoints_mul_le_inv_of_mem_canonicalTruncationDomain (solution)
