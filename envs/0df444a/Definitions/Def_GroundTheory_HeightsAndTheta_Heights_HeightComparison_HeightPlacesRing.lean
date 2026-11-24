-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlacesRing
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightPlacesRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:27.796321+00:00
-- url     : https://prove2.me/theorems/e6b996c5-527a-4bec-ad0f-45de39b8ab8c
-- title:
--   Height Places Ring
-- statement:
--   Definitions and structural lemmas for Height Places Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightPlacesRing.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open NumberField
def placesRing {L : Type*} [Field L] [NumberField L] (S : Set (FinitePlace L)) : Subring L where
  carrier := {x | ∀ w ∈ S, w x ≤ 1}
  zero_mem' := fun w _ ↦ by simp
  one_mem' := fun w _ ↦ by simp
  add_mem' := fun hx hy w hw ↦ (FinitePlace.add_le w _ _).trans (max_le (hx w hw) (hy w hw))
  neg_mem' := fun hx w hw ↦ by simpa [map_neg_eq_map] using hx w hw
  mul_mem' := fun hx hy w hw ↦ by
    rw [map_mul]
    exact mul_le_one₀ (hx w hw) (apply_nonneg w _) (hy w hw)
example {L : Type*} [Field L] [NumberField L] (S : Set (FinitePlace L)) (x : 𝓞 L) :
    algebraMap (𝓞 L) L x ∈ placesRing S := fun w _ ↦ by
  rw [← FinitePlace.norm_embedding_eq]
  exact FinitePlace.norm_le_one _ _ x
example : placesRing (∅ : Set (FinitePlace ℚ)) = ⊤ :=
  eq_top_iff.2 fun _ _ w hw ↦ absurd hw (Set.notMem_empty w)
end GroundTheory.Heights₂.Heights


