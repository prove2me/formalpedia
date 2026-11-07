-- Prove2me | Definitions.Def_OWFLocalDesc_decodeOut
-- name    : OWFLocalDesc_decodeOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:16.031572+00:00
-- url     : https://prove2.me/theorems/e3ed62a8-d8d5-4aa4-9315-a85558726ab0
-- title:
--   Well-formed heuristic outputs in $\mathbb Z\cup\{\infty\}$
-- statement:
--   A heuristic estimating a quantile outputs either a binary integer or a fixed symbol for $\infty$; such an output is **well formed**, and any other output counts as a failure.
--
--   Here the output string $1$ is the symbol for $\infty$, a string $0\,s\,d_0d_1\cdots d_r$ is the integer with sign bit $s$ and binary digits $d_0,d_1,\dots$ (least significant first), and every other string is malformed.
--
--   **Formalization Note** The paper fixes some such code; this is one fixed code in which every integer and $\infty$ can be written.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), §2.1, p.13

import Mathlib
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Well-formed heuristic outputs.** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), §2.1, p.13: "A heuristic
estimating a quantile outputs either a binary integer or a fixed symbol for ∞; such an output is
well formed, and any other output counts as a failure."

`decodeOut` reads an output string as an element of `ℤ ∪ {∞}` (`WithTop ℤ`): the string `[1]`
is the symbol for `∞`; a string `0 s d₀ d₁ …` is the integer with sign bit `s` (`1` = negative)
and binary digits `d₀ d₁ …` (least significant first); every other string is malformed (`none`).

**Formalization Note.** The paper fixes some code; this is one fixed code in which every integer
and `∞` is representable. -/
def decodeOut : List Bool → Option (WithTop ℤ)
  | [true] => some ⊤
  | false :: sgn :: digits =>
      some (((if sgn then (-1 : ℤ) else 1) *
        (Nat.ofDigits 2 (digits.map fun b => if b then 1 else 0) : ℤ) : ℤ) : WithTop ℤ)
  | _ => none

end OWFLocalDesc


