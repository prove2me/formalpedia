-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_BlockSplit
-- name    : Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_BlockSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:54.412938+00:00
-- url     : https://prove2.me/theorems/f5f1c701-86da-4846-bc37-f00dd5c7ee66
-- title:
--   Block Split
-- statement:
--   Definitions and structural lemmas for Block Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/BlockSplit.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.MainNotions.flipOneThree.Pf.KP
def BlockSplit : Prop :=
  ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {J : Type} [Fintype J] (n : ℕ) (z : O), z ≠ 0 →
    ∀ (A : J → Matrix (Fin n) (Fin n) O), ∑ j, A j = z • (1 : Matrix (Fin n) (Fin n) O) →
    ∃ ν : J → ℕ, n ≤ ∑ j, ν j ∧ ∀ j, ∃ (P : Matrix (Fin (ν j)) (Fin n) O) (Q : Matrix (Fin n) (Fin (ν j)) O),
      P * A j * Q = z • (1 : Matrix (Fin (ν j)) (Fin (ν j)) O)
open Module
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
noncomputable def bspZ (n : ℕ) (z : O) : Submodule O (Fin n → O) :=
  LinearMap.range (z • (LinearMap.id : (Fin n → O) →ₗ[O] (Fin n → O)))
end Formalism.MainNotions.flipOneThree.Pf.KP


