-- Prove2me | Definitions.Def_Grunbaum2003_containmentBitBlock
-- name    : Grunbaum2003_containmentBitBlock
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T07:04:16.164985+00:00
-- url     : https://prove2.me/theorems/3a8bd7a1-b35f-4430-b03f-4f5d455364bf
-- title:
--   Self-delimiting binary block
-- statement:
--   A Boolean word is encoded by a unary length prefix, a false delimiter, and then the word itself.
-- source:
--   Expression-essential binary encoding for Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §12.4 algorithmic reconstruction, printed p. 234a / PDF p. 277; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace Grunbaum2003

/-- Self-delimiting binary block, with linear overhead. -/
def containmentBitBlock (s : List Bool) : List Bool :=
  List.replicate s.length true ++ [false] ++ s

end Grunbaum2003


