-- Prove2me | Definitions.Def_Yukon_c8e407f0f265709344b29f9b
-- name    : Yukon_c8e407f0f265709344b29f9b
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-29T22:18:34.238904+00:00
-- url     : https://prove2.me/theorems/e9c3f850-66e4-4034-baa8-eba42e24114a
-- title:
--   ProximityPrize.SubmissionUpper.ComplementTruncationPencil.monomialPencil
-- statement:
--   The target two-monomial pencil.
--
--   Original contribution: dtumad, verified Better Codes submission 3cf4cb0e-7415-4347-9264-f1e9f9d8da9b. Source Lean 4.32.2, exact commit 20fb04406d24efa1ee911ff5c8694cbb5b206036. Statements, definitions and proof bodies preserved; imports and exported names adapted for Prove2Me.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/20fb04406d24efa1ee911ff5c8694cbb5b206036/ProximityPrize/SubmissionUpper/ComplementTruncationPencil.lean
--
--   p2m-history-complement:b2097b1a67daf5dedeb0b86de9aac2f28e112a78a85048f58d7fd2d2511a589e
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwMm0taGlzdG9yeS1jb21wbGVtZW50OmIyMDk3YjFhNjdkYWY1ZGVkZWIwYjg2ZGU5YWFjMmYyOGUxMTJhNzhhODUwNDhmNThkN2ZkMmQyNTExYTU4OWUiLCJoYXNoIjoiOWVhMjkwNWZiZGZkZGRhMWFlMmQ4NGFjY2Y5NTgzNWIxNGQ1YzIyNzI1Yjk1NWIwY2ZjYTIxZDFiZWQxZGJmYyIsImtpbmQiOiJkZWZpbml0aW9uIiwidGFyZ2V0IjoiWXVrb25fYzhlNDA3ZjBmMjY1NzA5MzQ0YjI5ZjliIiwiZW52aXJvbm1lbnQiOnsidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIiwibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQifSwidGFnIjoiYmV0dGVyLWNvZGVzLWhpc3RvcnkifQ]

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
/-- The target two-monomial pencil. -/
noncomputable def monomialPencil (N A s : ℕ) (gamma : F) : Polynomial F :=
  Polynomial.X ^ (A - 1) + Polynomial.C gamma * Polynomial.X ^ (N - s)
end ComplementTruncationPencil
end SubmissionUpper
end ProximityPrize


