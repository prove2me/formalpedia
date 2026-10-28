-- Prove2me | Definitions.Def_D1Bound5_Regular_Definitions
-- name    : D1Bound5_Regular_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:29:32.339061+00:00
-- url     : https://prove2.me/theorems/b0abdb25-4e60-454a-a6cc-b713a19e4629
-- title:
--   Regular
-- statement:
--   The symmetric regularity polynomial from Section 2. The named objects in this bundle include `regularDefect`.
-- source:
--   D1Bound5/Regular.lean, lines 6-8, SHA-256 216649d224d94c38aed36aa23129fd314ab8957413daa9e4aa3f53dd8156c10a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring

section
namespace D1Bound5

/-- The symmetric regularity polynomial from Section 2. -/
def regularDefect {R : Type*} [CommRing R] (a b c : R) : R :=
  a ^ 2 + b ^ 2 + c ^ 2 - 2*a*b - 2*a*c - 2*b*c - 4









end D1Bound5
end


