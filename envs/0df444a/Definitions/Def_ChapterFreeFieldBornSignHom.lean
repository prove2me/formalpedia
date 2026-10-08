-- Prove2me | Definitions.Def_ChapterFreeFieldBornSignHom
-- name    : ChapterFreeFieldBornSignHom
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T21:41:29.223161+00:00
-- url     : https://prove2.me/theorems/d2393875-edf5-45b7-ba45-a84d3ad8286d
-- title:
--   ChapterFreeFieldBornSignHom

import Definitions.Def_ChapterFreeFieldBornSignAction
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# the diagonal sign gauge as a homomorphism with parity character

Source: `book.tex`, Introduction, section *"Wave-function collapse versus Euler's
formula"* (`book.tex` line ~805) together with the free-field construction of §5
(`book.tex` ~line 1706).

Wave 158 (`ChapterFreeFieldBornSignAction`) recorded the diagonal `{±1}ⁿ` sign
gauge as an *action* of the elementary abelian 2-group `(Fin n → Bool, ⊕)`: the
sign flip `boolFlip b` (flip coordinate `k` iff `b k = true`) satisfies the
action laws (identity, `xor` composition, involution), preserves the unit sphere,
and fixes the Born image.

This wave records the underlying `±1` **sign vector** `flipVec b` as a *group
homomorphism*: `flipVec` sends the all-`false` vector to the pointwise unit `1`,
turns coordinate-wise `xor` into the pointwise product, is self-inverse, and is
injective (distinct boolean choices give distinct sign vectors, so the diagonal
gauge really has `2ⁿ` elements).  Finally we compute the **parity character**
`∏ k, flipVec b k = (-1) ^ (#flipped coordinates)` — the one-dimensional sign
representation `b ↦ (-1)^{|b|}` of the elementary abelian 2-group.

## Main results

* `flipVec_false` — `flipVec` sends the all-`false` vector to the pointwise `1`.
* `flipVec_xor` — `flipVec` turns coordinate-wise `xor` into the pointwise
  product (the homomorphism law).
* `flipVec_mul_self` — each `flipVec b` is self-inverse: `flipVec b * flipVec b = 1`.
* `flipVec_injective` — distinct boolean choices give distinct sign vectors.
* **headline** `flipVec_prod` — the parity character:
  `∏ k, flipVec b k = (-1) ^ (flipCount b)`.

Everything is intended to be `sorry`-free and axiom-clean.
-/

open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornSignAction

namespace BookProof.ChapterFreeFieldBornSignHom

variable {n : ℕ}

/-- The number of *flipped* coordinates of a boolean flip choice `b` — the
Hamming weight `|b|`.  The parity character below is `(-1)` to this power. -/
def flipCount (b : Fin n → Bool) : ℕ := (Finset.univ.filter (fun k => b k = true)).card

/-
`flipVec` sends the all-`false` vector to the pointwise multiplicative unit.
-/


/-
**Homomorphism law.** `flipVec` turns coordinate-wise `xor` into the
pointwise product of sign vectors, exhibiting it as a group homomorphism from
`(Fin n → Bool, ⊕)` to the pointwise `±1` sign vectors.
-/


/-
Each sign vector is self-inverse (the group is 2-torsion).
-/


/-
Distinct boolean flip choices give distinct sign vectors: `flipVec` is
injective, so the diagonal gauge group really has `2ⁿ` elements.
-/


/-
**Headline (parity character).** The product of the coordinates of a sign
vector is `(-1)` to the number of flipped coordinates — the one-dimensional sign
representation `b ↦ (-1)^{|b|}` of the elementary abelian 2-group.
-/


end BookProof.ChapterFreeFieldBornSignHom


