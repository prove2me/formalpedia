-- Prove2me | Definitions.Def_FirstPassageLinearTransport_TimeoutExecution
-- name    : FirstPassageLinearTransport_TimeoutExecution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:20:48.999792+00:00
-- url     : https://prove2.me/theorems/f0703517-da19-4166-bcca-c22c7b08ef7d
-- title:
--   Timeout Execution
-- statement:
--   Definitions and structural lemmas for Timeout Execution, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutExecution.lean

import Definitions.Def_FirstPassageLinearTransport_TimeoutEnvelope
set_option autoImplicit true
namespace FirstPassageLinearTransport
noncomputable section
def HasTimeoutTerminalLanding
    (P : TimeoutHighRunData) (K₀ : ℝ)
    (L M S n : ℕ) : Prop :=
  (∃ elapsed q : ℕ,
      q ≤ L ∧ TimeoutRecertificationRun P K₀ L M S n elapsed q) ∨
  (∃ elapsed q : ℕ,
      L < q ∧ q ≤ S ∧
        TimeoutRecertificationRun P K₀ L M S n elapsed q ∧
        orbit elapsed n = 2 ^ q)
end
end FirstPassageLinearTransport


