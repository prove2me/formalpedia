-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_PropsEquivA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_PropsEquivA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:32:21.477798+00:00
-- url     : https://prove2.me/theorems/4ab52484-506a-4b10-8ac2-eaccad34f4db
-- title:
--   Props Equiv A
-- statement:
--   Definitions and structural lemmas for Props Equiv A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/DiscreteSeriesExistence/PropsEquivA.lean

import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.ChartRestriction.DS
namespace KTypeIsomorphism
variable {ι : Type*} {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
theorem lc_mem (y₁ : ι → H₁) (C₁ : Submodule ℂ H₁) (h₁ : ∀ i, y₁ i ∈ C₁) (f : ι →₀ ℂ) :
    Finsupp.linearCombination ℂ y₁ f ∈ C₁ := by
  have h : Finsupp.linearCombination ℂ y₁ f ∈ Submodule.span ℂ (Set.range y₁) := by
    rw [← Finsupp.range_linearCombination]; exact LinearMap.mem_range_self _ f
  exact Submodule.span_le.2 (Set.range_subset_iff.2 h₁) h
def lcC (y₁ : ι → H₁) (C₁ : Submodule ℂ H₁) (h₁ : ∀ i, y₁ i ∈ C₁) : (ι →₀ ℂ) →ₗ[ℂ] C₁ :=
  (Finsupp.linearCombination ℂ y₁).codRestrict C₁ (lc_mem y₁ C₁ h₁)
variable [CompleteSpace H₁] [CompleteSpace H₂]
end KTypeIsomorphism
end ReciprocityTheory.ChartRestriction.DS


