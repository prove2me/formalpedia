-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartV_ch15_IsCoeffSeq
-- name    : RamanujanLostNotebook_PartV_ch15_IsCoeffSeq
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-06T18:33:32.876221+00:00
-- url     : https://prove2.me/theorems/5c662593-434a-4977-ad4f-d1f8a627df82
-- title:
--   Ramanujan's Lost Notebook Part V, Ch. 15: IsCoeffSeq
-- statement:
--   `IsCoeffSeq a f`: the integer sequence `a` is the sequence of Taylor coefficients at `0`
--   of the function `f` on the open unit disc, i.e. `f q = ∑_{n ≥ 0} a(n) q^n` (as `HasSum`) for
--   every complex `q` with `‖q‖ < 1`.  This is how the chapter's "define `a_n` by
--   `∑_{n ≥ 1} a_n q^n := q f^3(-q) f^3(-q^7)`" ((15.2.1), p. 323, and all later displays of that
--   kind) is expressed.
--   A proposition, total, no junk value.  For a given `f` at most one `a` satisfies it (uniqueness
--   of power series coefficients: a theorem, not part of the definition).  In this chapter `f` is
--   always a power of `q` times a product of `eulerF`, `eisP`, `eisQ`, `eisR` at powers of `q`;
--   such an `f` is analytic on the disc with integer Taylor coefficients, so a (unique) `a` exists,
--   and `a 0 = 0` because `f 0 = 0`.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part V, Springer 2018, Chapter 15.

import Mathlib

namespace RamanujanLostNotebook.PartV

/-- `IsCoeffSeq a f`: the integer sequence `a` is the sequence of Taylor coefficients at `0`
of the function `f` on the open unit disc, i.e. `f q = ∑_{n ≥ 0} a(n) q^n` (as `HasSum`) for
every complex `q` with `‖q‖ < 1`.  This is how the chapter's "define `a_n` by
`∑_{n ≥ 1} a_n q^n := q f^3(-q) f^3(-q^7)`" ((15.2.1), p. 323, and all later displays of that
kind) is expressed.
A proposition, total, no junk value.  For a given `f` at most one `a` satisfies it (uniqueness
of power series coefficients: a theorem, not part of the definition).  In this chapter `f` is
always a power of `q` times a product of `eulerF`, `eisP`, `eisQ`, `eisR` at powers of `q`;
such an `f` is analytic on the disc with integer Taylor coefficients, so a (unique) `a` exists,
and `a 0 = 0` because `f 0 = 0`. -/
def IsCoeffSeq (a : ℕ → ℤ) (f : ℂ → ℂ) : Prop :=
  ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n : ℕ => ((a n : ℤ) : ℂ) * q ^ n) (f q)

end RamanujanLostNotebook.PartV


