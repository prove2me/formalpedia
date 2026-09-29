-- Prove2me | Definitions.Def_Grunbaum2003_RayConfiguration
-- name    : Grunbaum2003_RayConfiguration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:35:19.433042+00:00
-- url     : https://prove2.me/theorems/febbd01e-5e20-4802-8217-2308192802e3
-- title:
--   Ray machine configuration
-- statement:
--   The program counter, tape head, real tape and count of ray queries.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §3.6, printed pp. 52b–52c / PDF pp. 74–75; exact-real ray-machine expression adapter; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

structure RayConfiguration where
  pc : ℕ
  head : ℤ
  tape : ℤ → ℝ
  queries : ℕ

end Grunbaum2003


