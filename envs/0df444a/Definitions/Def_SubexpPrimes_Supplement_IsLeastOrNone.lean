-- Prove2me | Definitions.Def_SubexpPrimes_Supplement_IsLeastOrNone
-- name    : SubexpPrimes_Supplement_IsLeastOrNone
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:45:50.982859+00:00
-- url     : https://prove2.me/theorems/7cd78fbf-2565-4699-9db2-62d15c50bdeb
-- title:
--   Answer of a search for the least element, or none
-- statement:
--   For a set $S$ of natural numbers, an answer to "find the least element of $S$, or report that none exists" is either **some** $p$, where $p$ is the least element of $S$, or **none**, when $S$ is empty. The module also fixes the output word of such an answer: a single $0$ bit for "none", and a $1$ bit followed by the binary digits of $p$ (least significant first) for "some $p$".
--
--   Every "find the least … or report that none exists" claim of Theorems 3 and 8.2 is stated with this answer.
-- source:
--   Gajulapalli, Deterministic Construction of Primes in Subexponential Time (manuscript, sha256 6ad4d3de…), Theorem 3, p.5 (PDF p.7); Theorem 8.2, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

namespace SubexpPrimes.Supplement

open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **The answer of "find the least … or report that none exists"** — Gajulapalli, *Deterministic
Construction of Primes in Subexponential Time* (manuscript, sha256 6ad4d3de…), Theorem 3, p.5, and
Theorem 8.2, p.35: `some p` with `p` the least element of `S`, or `none` when `S` is empty. -/
def IsLeastOrNone (S : Set ℕ) : Option ℕ → Prop
  | none => ∀ p : ℕ, p ∉ S
  | some p => IsLeast S p

/-- The output word of such an answer: `[false]` for "none exists", and `true` followed by
`countWord p` (the binary digits of `p`, least significant first) for `some p`. -/
def natOptWord : Option ℕ → List Bool
  | none => [false]
  | some p => true :: countWord p

end SubexpPrimes.Supplement


