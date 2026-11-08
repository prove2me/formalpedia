-- Prove2me | Definitions.Def_AffDisp4n_ofBool
-- name    : AffDisp4n_ofBool
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:55:30.681722+00:00
-- url     : https://prove2.me/theorems/5ca8cf17-8387-4392-9ba5-4ba3baad2875
-- title:
--   The identification of $\{0,1\}$ with $\mathbb F_2$
-- statement:
--   The bits $\{0, 1\}$ are identified with the field $\mathbb F_2$: $\mathtt{false} \mapsto 0$, $\mathtt{true} \mapsto 1$. Addition is XOR and multiplication is AND.
--
--   It converts the binary strings of a language into inputs of a circuit over $\mathbb F_2$.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.1, p.12

import Mathlib

namespace AffDisp4n

/-- The identification of `{0, 1}` with `𝔽₂` (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.1, p.12: "We identify {0, 1} with the field
𝔽₂ of two elements"): `false ↦ 0`, `true ↦ 1`. It is a bijection `Bool ≃ ZMod 2`. -/
def ofBool (b : Bool) : ZMod 2 := if b then 1 else 0

end AffDisp4n


