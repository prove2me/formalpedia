-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
-- name    : GroundTheory_AutomorphicForms_WhittakerLSpace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:34.322281+00:00
-- url     : https://prove2.me/theorems/8fc963c9-f930-467d-b770-a5cdc8d541af
-- title:
--   Whittaker LSpace
-- statement:
--   Definitions and structural lemmas for Whittaker LSpace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
namespace Whittaker
open Set Topology
variable {X : Type*} [TopologicalSpace X]
def supportedIn (U : Set X) : Submodule ℂ (X → ℂ) where
  carrier := {f | f ∈ locallyConstantCompactSupport X ℂ ℂ ∧ Function.support f ⊆ U}
  add_mem' {f g} hf hg := ⟨(locallyConstantCompactSupport X ℂ ℂ).add_mem hf.1 hg.1,
    (Function.support_add f g).trans (union_subset hf.2 hg.2)⟩
  zero_mem' := ⟨(locallyConstantCompactSupport X ℂ ℂ).zero_mem, by simp⟩
  smul_mem' c f hf := ⟨(locallyConstantCompactSupport X ℂ ℂ).smul_mem c hf.1,
    (Function.support_const_smul_subset c f).trans hf.2⟩
def vanishingOn (Z : Set X) : Submodule ℂ (X → ℂ) where
  carrier := {f | ∀ x ∈ Z, f x = 0}
  add_mem' {f g} hf hg x hx := by simp [hf x hx, hg x hx]
  zero_mem' x _ := rfl
  smul_mem' c f hf x hx := by simp [hf x hx]
section LSpace
variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]
end LSpace
end Whittaker
end GroundTheory.Automorphic


