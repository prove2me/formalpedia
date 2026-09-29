-- Prove2me | solution 1 for AutomorphicForm.isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/181aca60-7da8-54f0-b9ef-6e7e6e5ecc98

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (α β : ℝ) (hα : 0 < α)
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K) (B : Set (AdeleRing (𝓞 K) K))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (π : HeckeEigensystem K ℂ) :
    isotypicCuspSubmodule K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U gen B) ξ N S π ≤
      isotypicCuspSubmodule K (productionPinsOf K Φ U gen B) ξ N S π := by
  refine Submodule.span_mono ?_
  intro φ hφ
  have hφ' : IsIsotypicCuspFormAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U gen B) ξ N S π φ := hφ
  obtain ⟨⟨hA, hcusp⟩, hsm⟩ := hφ'.smoothCusp
  have hA' : IsAutomorphicFnAt K (productionPinsOf K Φ U gen B) ξ φ :=
    AutomorphicForm.isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre
      K c u d₁ d₂ T hd hcov α β hα Φ hΦs hΦ ξ φ hA
  refine (?_ : IsIsotypicCuspFormAt K (productionPinsOf K Φ U gen B) ξ N S π φ)
  exact ⟨⟨⟨hA', hcusp⟩, hsm⟩, hφ'.continuous, hφ'.level_invariant, hφ'.hecke_eigen,
    hφ'.central_eigen⟩

#print axioms solution

end S_AutomorphicForm_isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab (solution)
