-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_DiagRank
-- name    : Formalism_PeriodIntegrals_DiagRank
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:45.413025+00:00
-- url     : https://prove2.me/theorems/7798fed3-62d7-4672-a4b3-99c8a7014be9
-- title:
--   Diag Rank
-- statement:
--   Definitions and structural lemmas for Diag Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/DiagRank.lean

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
open Classical in

def DiagRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n m : ℕ) (X Y : Fin n → Fin m → ℤ_[p]) (c : Fin m → ℚ_[p]) (D : ℤ),
    (∀ i j, ∑ a, (X i a : ℚ_[p]) * c a * (Y j a : ℚ_[p]) = if i = j then (p : ℚ_[p]) ^ D else 0) →
    n ≤ (Finset.univ.filter (fun a : Fin m => c a ≠ 0 ∧ (c a).valuation ≤ D)).card
end PI


