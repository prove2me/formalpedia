-- Prove2me | Definitions.Def_Yukon_fce1ab10c536c75cdaab6eaf
-- name    : Yukon_fce1ab10c536c75cdaab6eaf
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-29T22:18:16.823273+00:00
-- url     : https://prove2.me/theorems/b03c5226-e5df-4d8f-9a55-d6862551407a
-- title:
--   ProximityPrize.SubmissionUpper.ComplementTruncationPencil.truncationQuotient
-- statement:
--   The quotient whose negative is the desired two-monomial word on roots of
--   the locator.
--
--   Original contribution: dtumad, verified Better Codes submission 3cf4cb0e-7415-4347-9264-f1e9f9d8da9b. Source Lean 4.32.2, exact commit 20fb04406d24efa1ee911ff5c8694cbb5b206036. Statements, definitions and proof bodies preserved; imports and exported names adapted for Prove2Me.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/20fb04406d24efa1ee911ff5c8694cbb5b206036/ProximityPrize/SubmissionUpper/ComplementTruncationPencil.lean
--
--   p2m-history-complement:3a6991b6a81da68bbe77576157ce7d0c780c4dba4e6a1e633fd71255be8b7132
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwMm0taGlzdG9yeS1jb21wbGVtZW50OjNhNjk5MWI2YTgxZGE2OGJiZTc3NTc2MTU3Y2U3ZDBjNzgwYzRkYmE0ZTZhMWU2MzNmZDcxMjU1YmU4YjcxMzIiLCJoYXNoIjoiNDg1ZWUyOThlMTQxODRiN2E2N2E0OTIxYmU1NGVjMTM1MWM4YTg0ZTIwOTAwYjBlYmM0MmYxMjQxOTI0NjRmNiIsImtpbmQiOiJkZWZpbml0aW9uIiwidGFyZ2V0IjoiWXVrb25fZmNlMWFiMTBjNTM2Yzc1Y2RhYWI2ZWFmIiwiZW52aXJvbm1lbnQiOnsidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIiwibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQifSwidGFnIjoiYmV0dGVyLWNvZGVzLWhpc3RvcnkifQ]

/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/




import Mathlib
/-!
# Complement truncation and a monomial pencil

Let `L * R = X^N - 1`, and split the complementary factor as

`R = X^s * H + r * X^(s - 1) + E`.

If `gamma * r = -1`, multiplying the resulting quotient candidate by `X^s`
gives an expression involving only the locator `L` and the short residual
tail `E`.  At every root of `L`, the negative quotient evaluates as the
two-monomial pencil

`x^(A - 1) + gamma * x^(N - s)`.

This is the exact algebraic bridge behind the complement-truncation syndrome
experiment.  It deliberately does not assert that the residual high band can
be cancelled: at the current benchmark agreement it still has `8709`
coefficients.
-/

namespace ProximityPrize.SubmissionUpper.ComplementTruncationPencil

open Polynomial

variable {F : Type} [Field F]
/-- The quotient whose negative is the desired two-monomial word on roots of
the locator. -/
noncomputable def truncationQuotient (N A s : ℕ) (gamma : F)
    (L H : Polynomial F) : Polynomial F :=
  Polynomial.C gamma * L * H - Polynomial.C gamma * Polynomial.X ^ (N - s) -
    Polynomial.X ^ (A - 1)
end ComplementTruncationPencil
end SubmissionUpper
end ProximityPrize


