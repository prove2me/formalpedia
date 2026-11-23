-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_PolydiscInt
-- name    : Formalism_PeriodIntegrals_PolydiscInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:50.944136+00:00
-- url     : https://prove2.me/theorems/dd690bb4-d6df-47c3-9252-f39f99b58915
-- title:
--   Polydisc Int
-- statement:
--   Definitions and structural lemmas for Polydisc Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/PolydiscInt.lean

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
def PolydiscInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (a : (Fin n →₀ ℕ) → ℂ_[p]),
    (∀ z : Fin n → ℂ_[p], (∀ i, ‖z i‖ < 1) →
      Summable (fun α : Fin n →₀ ℕ => a α * ∏ i, z i ^ α i) ∧
      ‖∑' α : Fin n →₀ ℕ, a α * ∏ i, z i ^ α i‖ ≤ 1) →
    ∀ α, ‖a α‖ ≤ 1
end PI


