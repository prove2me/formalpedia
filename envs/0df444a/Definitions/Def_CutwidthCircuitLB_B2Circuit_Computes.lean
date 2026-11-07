-- Prove2me | Definitions.Def_CutwidthCircuitLB_B2Circuit_Computes
-- name    : CutwidthCircuitLB_B2Circuit_Computes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:19.679893+00:00
-- url     : https://prove2.me/theorems/1a46e876-8f9a-4899-a665-cf710bf500a1
-- title:
--   A $B_2$-circuit computes $f$
-- statement:
--   A $B_2$-circuit $C$ on $n$ inputs **computes** a function $f : \{0,1\}^n \to \{0,1\}$ if $C(x) = f(x)$ for every $x \in \{0,1\}^n$.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Section 4.2, p.12

import Mathlib
import Definitions.Def_CutwidthCircuitLB_B2Circuit
import Definitions.Def_CutwidthCircuitLB_B2Circuit_eval

namespace CutwidthCircuitLB

/-- A B₂-circuit `C` **computes** `f : {0,1}ⁿ → {0,1}` (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), §4, p.12): `C(x) = f(x)` for every
input `x`. -/
def B2Circuit.Computes {n : ℕ} (C : B2Circuit n) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool, C.eval x = f x

end CutwidthCircuitLB


