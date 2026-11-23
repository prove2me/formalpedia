-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_IsTwoCocycleCoboundary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:49.264977+00:00
-- url     : https://prove2.me/theorems/5778a433-e0b3-42fc-9538-1a7b2a8b8e25
-- title:
--   Is Two Cocycle Coboundary
-- statement:
--   Definitions and structural lemmas for Is Two Cocycle Coboundary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/IsTwoCocycleCoboundary.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_InfRes
import Definitions.Def_ReciprocityTheory_GroupCohomology_ComapZeroCoboundariesEqBot
import Definitions.Def_ReciprocityTheory_GroupCohomology_PartialProdCoe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2
section Alg
variable {R : Type*} [CommRing R] {G : Type*} [Group G] {A : Type*} [AddCommGroup A] [Module R A]
  (ρ : Representation R G A) (N : Subgroup G)
def IsTwoCocycle (c : G → G → A) : Prop := ∀ g h k, ρ g (c h k) - c (g * h) k + c g (h * k) - c g h = 0
def D1 (y : G → A) (g h : G) : A := ρ g (y h) - y (g * h) + y g
variable {ρ}
variable {N} {c : G → G → A} (hc : IsTwoCocycle ρ c)
  {r s : G → G} (hrs : ∀ g, r g * s g = g) (hr : ∀ g, r g ∈ N)
  (hrn : ∀ n ∈ N, ∀ g, r (n * g) = n * r g) (hsn : ∀ n ∈ N, ∀ g, s (n * g) = s g)
end Alg
end ReciprocityTheory.DiscreteGroups.LocalClassField.Deg2


