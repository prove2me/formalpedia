-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_BrUnrA
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_BrUnrA
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T14:51:31.668288+00:00
-- url     : https://prove2.me/theorems/cda93bed-507c-449c-8948-917a7d2789ec
-- title:
--   Br Unr A
-- statement:
--   Definitions and structural lemmas for Br Unr A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/BrUnrA.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_ImportsAlt
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HSubsingletonOfUniquelyDivisible
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_FinCoh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Gal Function
noncomputable section
variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
  [IsTopologicalGroup G']
def trivInfl (φ : G' →* G) (hφ : Continuous φ) (A : Type) [AddCommGroup A] :
    Pair (trivRep G A) (trivRep G' A) where
  φ := φ
  u := (LinearMap.id : A →ₗ[ℤ] A)
  φ_cont := hφ
  u_cont := continuous_of_discreteTopology
  equiv _ _ := rfl
end
end ReciprocityTheory.DiscreteGroups.LocalClassField


