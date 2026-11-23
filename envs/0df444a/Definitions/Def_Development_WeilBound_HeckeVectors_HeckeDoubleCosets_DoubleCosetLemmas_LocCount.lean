-- Prove2me | Definitions.Def_Development_WeilBound_HeckeVectors_HeckeDoubleCosets_DoubleCosetLemmas_LocCount
-- name    : Development_WeilBound_HeckeVectors_HeckeDoubleCosets_DoubleCosetLemmas_LocCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:20.653632+00:00
-- url     : https://prove2.me/theorems/bb352f79-91e2-4b8c-9e82-a8e6814f9d7e
-- title:
--   Loc Count
-- statement:
--   Definitions and structural lemmas for Loc Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/HeckeVectors/HeckeDoubleCosets/DoubleCosetLemmas/LocCount.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
namespace CompanionTheory.D.Upq.DoubleCosetLemmas
variable {G M : Type} [Group G] [MeasurableSpace M]
def stab (J : Subgroup G) (g : G) : Set G := {k | k ∈ J ∧ g⁻¹ * k * g ∈ J}
def cos (J : Subgroup G) (g : G) (A : Set G) : Set (G ⧸ J) := {z | ∃ k ∈ A, z = ((k * g : G) : G ⧸ J)}
structure Meas (dx : Measure M) (φ : G → M) (J : Subgroup G) (g : G) : Prop where
  inj : Function.Injective φ
  meas : ∀ k ∈ J, MeasurableSet (φ '' ((k * ·) '' stab J g))
  vol : ∀ k ∈ J, dx (φ '' ((k * ·) '' stab J g)) = dx (φ '' stab J g)
  ne : dx (φ '' stab J g) ≠ 0
  fin : dx (φ '' (J : Set G)) ≠ ⊤
variable {dx : Measure M} {φ : G → M} {J : Subgroup G} {g : G}
section Sum
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y] {F : G → Y}
end Sum
end CompanionTheory.D.Upq.DoubleCosetLemmas


