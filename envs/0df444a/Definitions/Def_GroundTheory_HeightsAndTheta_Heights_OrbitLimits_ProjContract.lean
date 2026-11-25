-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ProjContract
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ProjContract
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T04:57:37.881918+00:00
-- url     : https://prove2.me/theorems/e1fa8933-d926-5086-b455-6c644394ade2
-- title:
--   Proj Contract
-- statement:
--   Definitions and structural lemmas for Proj Contract, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ProjContract.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_BlockInclInjectiveOfEmbedding
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_blockIncl_injective_of_embedding_ab21dab97000

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
universe u
namespace ProjContract
section Theory
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
end Theory
section Image
variable {F : Type u} [Field F] {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
def emb (hv : AI.I1.IsBlockMap κ v) : K ↪ K' := ⟨κ, hv.1⟩
theorem range_eq (hv : AI.I1.IsBlockMap κ v) :
    Set.range v = Set.range (FieldNumbers.blockIncl (emb hv) ι') := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    have h := hv.2.2.1 p
    revert h
    generalize v p = q
    obtain ⟨a, b⟩ := q
    rintro (rfl : a = κ p.1)
    exact ⟨⟨p.1, b⟩, rfl⟩
  · rintro ⟨⟨k, x⟩, rfl⟩
    exact hv.2.2.2 _ ⟨k, rfl⟩
def blockEquiv (hv : AI.I1.IsBlockMap κ v) : (Σ k, ι k) ≃ (Σ k, ι' (emb hv k)) :=
  (Equiv.ofInjective v hv.2.1).trans ((Equiv.setCongr (range_eq hv)).trans
    (Equiv.ofInjective _ (FieldNumbers.PFContracted.blockIncl_injective_of_embedding (emb hv) ι')).symm)
end Image
end ProjContract
end
end GroundTheory.Heights₂.Heights.Targets


