-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_Artin_MackeyFrobenius
-- name    : GroundTheory_GlobalFields_Artin_MackeyFrobenius
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:45:34.49934+00:00
-- url     : https://prove2.me/theorems/7bba44f3-ae02-4c71-98dd-641722773194
-- title:
--   Mackey Frobenius
-- statement:
--   Definitions and structural lemmas for Mackey Frobenius, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/MackeyFrobenius.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
namespace GroundTheory.Global.Artin
open GroundTheory.LocalField
section Cyclic
variable {Γ : Type*} [Group Γ] {N : Subgroup Γ} [N.Normal] {g : Γ}
end Cyclic
section Frobenius
variable {G : Type*} [Group G]
def frobIndex (H D I : Subgroup G) (x : G) : ℕ :=
  (I ⊔ ((MulAut.conj x⁻¹ • H : Subgroup G) ⊓ D)).relIndex D
def cosetAvg {Γ : Type*} [Group Γ] (I : Subgroup Γ) [Fintype I] (φ : Γ) (F : Γ → ℂ) (m : ℤ) :
    ℂ :=
  (Nat.card I : ℂ)⁻¹ * ∑ i : I, F (φ ^ m * i)
variable {H D I : Subgroup G}
end Frobenius
section Formula
variable {G : Type*} [Group G] [Fintype G] {H D I : Subgroup G}
end Formula
section Main
variable {G : Type*} [Group G] [Fintype G] {H D I : Subgroup G}
end Main
end GroundTheory.Global.Artin


