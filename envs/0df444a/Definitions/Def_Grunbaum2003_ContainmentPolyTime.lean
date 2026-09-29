-- Prove2me | Definitions.Def_Grunbaum2003_ContainmentPolyTime
-- name    : Grunbaum2003_ContainmentPolyTime
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T07:04:27.946795+00:00
-- url     : https://prove2.me/theorems/04f63e58-8393-4611-b116-f36f26ebfe84
-- title:
--   Polynomial-time binary function
-- statement:
--   A binary function is polynomial-time when it is computed by a Mathlib TM2 machine with finite stack alphabets under one polynomial time bound.
-- source:
--   Expression-essential complexity model for Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §12.4 algorithmic reconstruction, printed p. 234a / PDF p. 277; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

namespace Grunbaum2003

/-- Polynomial-time binary function. All stack alphabets are finite, including
internal stacks (a stronger finiteness condition than FinTM2 alone supplies). -/
def ContainmentPolyTime (f : List Bool → List Bool) : Prop :=
  ∃ M : Turing.TM2ComputableInPolyTime id id f, ∀ k, Finite (M.tm.Γ k)

end Grunbaum2003


