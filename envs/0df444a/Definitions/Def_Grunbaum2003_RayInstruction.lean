-- Prove2me | Definitions.Def_Grunbaum2003_RayInstruction
-- name    : Grunbaum2003_RayInstruction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:35:06.037517+00:00
-- url     : https://prove2.me/theorems/bb267e31-f440-4d02-82e1-75198bfe9f05
-- title:
--   Exact real ray machine instructions
-- statement:
--   Finite instruction syntax for exact real arithmetic, branching, tape movement, ray queries and halt.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §3.6, printed pp. 52b–52c / PDF pp. 74–75; exact-real ray-machine expression adapter; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

inductive RayInstruction where
  | constant (dst : ℤ) (value : ℚ) (next : ℕ)
  | add (dst a b : ℤ) (next : ℕ)
  | sub (dst a b : ℤ) (next : ℕ)
  | mul (dst a b : ℤ) (next : ℕ)
  | div (dst a b : ℤ) (next : ℕ)
  | branch (a : ℤ) (negative equal positive : ℕ)
  | shift (offset : ℤ) (next : ℕ)
  | query (next : ℕ)
  | halt

end Grunbaum2003


