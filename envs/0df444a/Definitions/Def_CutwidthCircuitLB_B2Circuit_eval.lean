-- Prove2me | Definitions.Def_CutwidthCircuitLB_B2Circuit_eval
-- name    : CutwidthCircuitLB_B2Circuit_eval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:35.962855+00:00
-- url     : https://prove2.me/theorems/80642582-e83a-427b-8892-c99aa388ffaf
-- title:
--   Output $C(x)$ of a $B_2$-circuit
-- statement:
--   The **output** $C(x) \in \{0,1\}$ of a $B_2$-circuit $C$ on the input $x \in \{0,1\}^n$ is the value of its output gate, which is the last gate in the topological order.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.1, p.6

import Mathlib
import Definitions.Def_CutwidthCircuitLB_B2Circuit
import Definitions.Def_CutwidthCircuitLB_B2Circuit_prefixValues

namespace CutwidthCircuitLB

/-- The output `C(x)` of a B₂-circuit on the input `x ∈ {0,1}ⁿ` (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Definition 2.1, p.6):
the value of the output gate, which is the last gate in the topological order. -/
def B2Circuit.eval {n : ℕ} (C : B2Circuit n) (x : Fin n → Bool) : Bool :=
  C.prefixValues x C.size le_rfl ⟨C.size - 1, Nat.sub_lt C.size_pos Nat.one_pos⟩

end CutwidthCircuitLB


