-- Prove2me | Definitions.Def_CutwidthCircuitLB_ROBP_Accepts
-- name    : CutwidthCircuitLB_ROBP_Accepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:31.226201+00:00
-- url     : https://prove2.me/theorems/ba13ae2d-82e3-46e1-a64d-134be024268b
-- title:
--   A read-once program accepts $x$
-- statement:
--   A read-once program **accepts** an input $x \in \{0,1\}^n$ if some start-to-accept path consistent with $x$ exists.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.2, p.7

import Mathlib
import Definitions.Def_CutwidthCircuitLB_ROBP
import Definitions.Def_CutwidthCircuitLB_ROBP_IsAcceptingPath

namespace CutwidthCircuitLB

/-- A read-once program **accepts** `x ∈ {0,1}ⁿ` if some consistent start-to-accept path exists
(McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Definition 2.2, p.7). -/
def ROBP.Accepts {n : ℕ} (R : ROBP n) (x : Fin n → Bool) : Prop :=
  ∃ vs es, R.IsAcceptingPath vs es x

end CutwidthCircuitLB


