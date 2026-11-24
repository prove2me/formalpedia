-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractBlocksSplitPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:43.278988+00:00
-- url     : https://prove2.me/theorems/6577f3fd-460a-4cb4-a798-adb66114f8ba
-- title:
--   Contract Blocks Split Prime
-- statement:
--   Definitions and structural lemmas for Contract Blocks Split Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractBlocksSplitPrime.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_HomFracDegZeroEqFunField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_AddBlockVarEquivFst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
section Split
variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)
def splitBlockEquiv : K ⊕ blockCompl j ≃ K' :=
  Equiv.ofBijective (Sum.elim j Subtype.val) (by
    refine ⟨?_, fun k' => ?_⟩
    · rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (j.injective h)
      · exact absurd ⟨a, h⟩ b.2
      · exact absurd ⟨b, h.symm⟩ a.2
      · exact congrArg Sum.inr (Subtype.ext h)
    · by_cases h : k' ∈ Set.range j
      · obtain ⟨k, rfl⟩ := h
        exact ⟨Sum.inl k, rfl⟩
      · exact ⟨Sum.inr ⟨k', h⟩, rfl⟩)
def splitVarEquiv : (Σ s, splitCoord j ι' s) ≃ (Σ k', ι' k') :=
  Equiv.ofBijective (splitVar j ι') (by
    refine ⟨?_, fun ⟨k', i⟩ => ?_⟩
    · rintro ⟨a | a, x⟩ ⟨b | b, y⟩ h
      · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
        cases j.injective h1
        cases eq_of_heq h2
        rfl
      · exact absurd ⟨a, congrArg Sigma.fst h⟩ b.2
      · exact absurd ⟨b, (congrArg Sigma.fst h).symm⟩ a.2
      · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp h
        cases Subtype.ext h1
        cases eq_of_heq h2
        rfl
    · by_cases h : k' ∈ Set.range j
      · obtain ⟨k, rfl⟩ := h
        exact ⟨⟨Sum.inl k, i⟩, rfl⟩
      · exact ⟨⟨Sum.inr ⟨k', h⟩, i⟩, rfl⟩)
end Split
end
end GroundTheory.Heights₂.Heights.FieldNumbers


