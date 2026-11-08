-- Prove2me | Definitions.Def_AffDisp4n_langOf
-- name    : AffDisp4n_langOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:56:11.249564+00:00
-- url     : https://prove2.me/theorems/b7da0455-d8bd-44d1-b9a5-af3c3b9a1cd2
-- title:
--   The language of a family of Boolean functions
-- statement:
--   For a family $(f_n)_{n \ge 0}$ of functions $f_n : \mathbb F_2^n \to \mathbb F_2$, its **language** is
--   $$
--   L_f = \{\, w \in \{0,1\}^* : f_{|w|}(w) = 1 \,\}.
--   $$
--   The family is **polynomial-time explicit** when $L_f \in \mathbf P$, that is, when $f_n(x)$ can be computed in time polynomial in $n$.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §4, p.21

import Mathlib
import Definitions.Def_AffDisp4n_ofBool

namespace AffDisp4n

/-- The **language of a family** `fₙ : 𝔽₂ⁿ → 𝔽₂` of Boolean functions: the binary strings `w` with
`f_{|w|}(w) = 1` (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §4, p.21: "a polynomial-time explicit family (fₙ)"). The family is
polynomial-time explicit when this language is in `P`.

**Formalization Note** The bit `true` is `1 ∈ 𝔽₂` (`ofBool`). -/
def langOf (F : (n : ℕ) → (Fin n → ZMod 2) → ZMod 2) : Language Bool :=
  {w | F w.length (fun i => ofBool (w.get i)) = 1}

end AffDisp4n


