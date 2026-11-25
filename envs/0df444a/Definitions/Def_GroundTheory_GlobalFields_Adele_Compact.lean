-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
-- name    : GroundTheory_GlobalFields_Adele_Compact
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:45:25.704132+00:00
-- url     : https://prove2.me/theorems/07c110c4-d6e8-499d-b207-d5744f7f5a66
-- title:
--   Compact
-- statement:
--   Definitions and structural lemmas for Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Compact.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Theorems.Thm_GroundTheory_Global_exists_isCompact_forall_exists_sub_mem
import Theorems.Thm_GroundTheory_Global_isClosed_principalSubgroup
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
namespace GroundTheory.Global
open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K] [NumberField K]
theorem isCompact_integralFiniteAdeles :
    IsCompact (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
  have : ∀ v : HeightOneSpectrum (𝓞 K),
      CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    isCompact_iff_compactSpace.1 (isCompact_adicCompletionIntegers v)
  have hcont := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (𝓕 := Filter.cofinite)).continuous
  have h := isCompact_range hcont
  rw [RestrictedProduct.range_structureMap] at h
  exact h
abbrev AdeleQuotient : Type _ := 𝔸[K] ⧸ AdeleRing.principalSubgroup (𝓞 K) K
instance : IsClosed (AdeleRing.principalSubgroup (𝓞 K) K : Set 𝔸[K]) :=
  isClosed_principalSubgroup K
instance compactSpace_adeleQuotient : CompactSpace (AdeleQuotient K) := by
  obtain ⟨C, hC, hx⟩ := exists_isCompact_forall_exists_sub_mem K
  have hD : IsCompact (C ×ˢ (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) :
      Set 𝔸[K]) := hC.prod (isCompact_integralFiniteAdeles K)
  refine ⟨?_⟩
  convert hD.image (QuotientAddGroup.continuous_mk (N := AdeleRing.principalSubgroup (𝓞 K) K))
  refine (Set.eq_univ_of_forall fun q => ?_).symm
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    obtain ⟨k, hk⟩ := hx x
    refine ⟨x - algebraMap K 𝔸[K] k, hk, ?_⟩
    rw [QuotientAddGroup.eq]
    exact ⟨k, by simp⟩
instance t2Space_adeleQuotient : T2Space (AdeleQuotient K) := inferInstance
end GroundTheory.Global


