-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_SymplZ
-- name    : Formalism_PeriodIntegrals_SymplZ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:51.656382+00:00
-- url     : https://prove2.me/theorems/733057c0-460a-4720-b009-03f85ab6d09b
-- title:
--   Sympl Z
-- statement:
--   Definitions and structural lemmas for Sympl Z, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/SymplZ.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
open Matrix
def SymplZ : Prop :=
  ∀ (n : ℕ) (E : Matrix (Fin n) (Fin n) ℤ), Eᵀ = -E → IsUnit E.det →
    ∃ (k : ℕ) (e : Fin n ≃ Fin k ⊕ Fin k) (P : Matrix (Fin n) (Fin n) ℤ), IsUnit P.det ∧
      P * E * Pᵀ = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 0 1 (-1) 0)
end PI


