-- Prove2me | Definitions.Def_CutwidthCircuitLB_ROBP_Computes
-- name    : CutwidthCircuitLB_ROBP_Computes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:28:28.996886+00:00
-- url     : https://prove2.me/theorems/75e97bdf-c4a8-4b36-8abd-0d76ad099375
-- title:
--   A read-once program computes $f$
-- statement:
--   A read-once program **computes** $f : \{0,1\}^n \to \{0,1\}$ if it accepts exactly the inputs on which $f = 1$.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.2, p.7

import Mathlib
import Definitions.Def_CutwidthCircuitLB_ROBP
import Definitions.Def_CutwidthCircuitLB_ROBP_Accepts

namespace CutwidthCircuitLB

/-- A read-once program **computes** `f : {0,1}ⁿ → {0,1}` if it accepts exactly the inputs on which
`f = 1` (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Definition 2.2, p.7). -/
def ROBP.Computes {n : ℕ} (R : ROBP n) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool, R.Accepts x ↔ f x = true

end CutwidthCircuitLB


