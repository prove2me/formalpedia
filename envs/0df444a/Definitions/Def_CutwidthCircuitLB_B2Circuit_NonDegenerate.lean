-- Prove2me | Definitions.Def_CutwidthCircuitLB_B2Circuit_NonDegenerate
-- name    : CutwidthCircuitLB_B2Circuit_NonDegenerate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:28.249242+00:00
-- url     : https://prove2.me/theorems/ab2e3eb3-7dc6-48fd-b4e6-673048b48bb7
-- title:
--   Non-degenerate $B_2$-circuit
-- statement:
--   A $B_2$-circuit is **non-degenerate** if every input variable is read, that is, has a directed path to the output gate.
--
--   Lemma 3.1 compiles non-degenerate circuits; a degenerate circuit is reduced to a non-degenerate one by deleting its unread variables.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Section 3, p.8

import Mathlib
import Definitions.Def_CutwidthCircuitLB_B2Circuit
import Definitions.Def_CutwidthCircuitLB_B2Circuit_IsRead

namespace CutwidthCircuitLB

/-- A B₂-circuit is **non-degenerate** if every input variable is read, i.e. has a directed path to
the output gate (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), §3, p.8). -/
def B2Circuit.NonDegenerate {n : ℕ} (C : B2Circuit n) : Prop :=
  ∀ j : Fin n, C.IsRead (Sum.inl j)

end CutwidthCircuitLB


