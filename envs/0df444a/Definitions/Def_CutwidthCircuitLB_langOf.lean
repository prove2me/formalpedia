-- Prove2me | Definitions.Def_CutwidthCircuitLB_langOf
-- name    : CutwidthCircuitLB_langOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:28.610884+00:00
-- url     : https://prove2.me/theorems/ce087afb-d778-4bf5-a050-5c9c6236d2d9
-- title:
--   The language $L_F = \{x : F_{|x|}(x) = 1\}$
-- statement:
--   For a family $F_n : \{0,1\}^n \to \{0,1\}$, the language $L_F := \{x \in \{0,1\}^\star : F_{|x|}(x) = 1\}$.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Section 1.2, p.4

import Mathlib

namespace CutwidthCircuitLB

/-- The language `L_F := {x : F_(|x|)(x) = 1}` of a family `Fₙ : {0,1}ⁿ → {0,1}` (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), §1.2,
p.4). -/
def langOf (F : (n : ℕ) → (Fin n → Bool) → Bool) : Language Bool :=
  {w | F w.length (fun i => w.get i) = true}

end CutwidthCircuitLB


