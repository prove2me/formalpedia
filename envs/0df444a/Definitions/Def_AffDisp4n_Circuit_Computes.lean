-- Prove2me | Definitions.Def_AffDisp4n_Circuit_Computes
-- name    : AffDisp4n_Circuit_Computes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:59:54.3375+00:00
-- url     : https://prove2.me/theorems/201e1f48-6b8a-4da3-8023-79a83ea09a0f
-- title:
--   A $B_2$-circuit computes $f : \mathbb F_2^n \to \mathbb F_2$
-- statement:
--   A $B_2$-circuit $C$ on $n$ inputs **computes** $f : \mathbb F_2^n \to \mathbb F_2$ if $C(x) = f(x)$ for every $x \in \mathbb F_2^n$.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), Theorem 4.1, p.21

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_Acyclic_gateVal
import Definitions.Def_AffDisp4n_Acyclic_eval
import Definitions.Def_AffDisp4n_Circuit

namespace AffDisp4n

/-- A B₂-circuit `C` on `n` inputs **computes** `f : 𝔽₂ⁿ → 𝔽₂` (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), Theorem 4.1, p.21: "any
B₂-circuit C₀ computing f"): `C(x) = f(x)` for every `x ∈ 𝔽₂ⁿ`. -/
def Circuit.Computes {n : ℕ} (C : Circuit n) (f : (Fin n → ZMod 2) → ZMod 2) : Prop :=
  ∀ x : Fin n → ZMod 2, C.eval x = f x

end AffDisp4n


