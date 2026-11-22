-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_Minkowski
-- name    : Formalism_PeriodIntegrals_Minkowski
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:08:24.143816+00:00
-- url     : https://prove2.me/theorems/d401214a-5882-482c-b2cb-ff7391d74720
-- title:
--   Minkowski
-- statement:
--   Definitions and structural lemmas for Minkowski, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/Minkowski.lean

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
def minkowskiExp (N p : ℕ) : ℕ := ∑ i ∈ Finset.range (N + 1), N / (p ^ i * (p - 1))
def minkowskiM (N : ℕ) : ℕ := ∏ p ∈ (Finset.range (N + 2)).filter Nat.Prime, p ^ minkowskiExp N p
def MinkowskiBound : Prop :=
  ∀ (N : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ)), Finite G →
    Nat.card G ∣ minkowskiM N
end PI


