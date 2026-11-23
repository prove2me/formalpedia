-- Prove2me | Definitions.Def_GroundTheory_LocalFields_BrauerInductionElementary
-- name    : GroundTheory_LocalFields_BrauerInductionElementary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:28.20774+00:00
-- url     : https://prove2.me/theorems/a48c7fda-1e71-477a-8fa8-e0c2f87f50d6
-- title:
--   Brauer Induction Elementary
-- statement:
--   Definitions and structural lemmas for Brauer Induction Elementary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionElementary.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
variable {G : Type*} [Group G]
def IsElementaryAt (p : ℕ) (H : Subgroup G) : Prop :=
  ∃ C P : Subgroup G, C ≤ H ∧ P ≤ H ∧ IsCyclic C ∧ (Nat.card C).Coprime p ∧ IsPGroup p P ∧
    (∀ c ∈ C, ∀ y ∈ P, c * y = y * c) ∧ ∀ h ∈ H, ∃ c ∈ C, ∃ y ∈ P, h = c * y
def IsElementary (H : Subgroup G) : Prop := ∃ p : ℕ, p.Prime ∧ IsElementaryAt p H
variable [Finite G] {p : ℕ}
end GroundTheory.LocalField


