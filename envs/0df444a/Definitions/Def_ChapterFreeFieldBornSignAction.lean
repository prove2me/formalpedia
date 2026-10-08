-- Prove2me | Definitions.Def_ChapterFreeFieldBornSignAction
-- name    : ChapterFreeFieldBornSignAction
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T20:57:00.644281+00:00
-- url     : https://prove2.me/theorems/d0a16fda-05e3-4cb9-b459-eba736cf089d
-- title:
--   ChapterFreeFieldBornSignAction

import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBorn
import Mathlib


/-!
# Chapter "Wave-function parametrization of a probability measure", §5 —
# the diagonal sign gauge as an action of the elementary abelian 2-group

Source: `book.tex`, Introduction, section *"Wave-function collapse versus Euler's
formula"* (`book.tex` line ~805) together with the free-field construction of §5
(`book.tex` ~line 1706).

Earlier waves recorded the *combinatorics* of the diagonal `{±1}ⁿ` sign gauge of
the Born map `x ↦ (x_k)²`: each Born fiber is a full orbit of the sign group
restricted to the positive support, `#fiber = 2 ^ (#positive coordinates)`, and
the orbit–stabilizer identity `#orbit · #stabilizer = 2ⁿ`.

This wave records the underlying **group action** itself. Indexing the sign group
by boolean vectors under coordinate-wise `xor` — the elementary abelian
2-group `(Fin n → Bool, ⊕)` — the sign flip `boolFlip b` (flip the sign of the
`k`-th coordinate exactly when `b k = true`) satisfies the action laws:

* the all-`false` vector acts as the identity;
* composition follows the `xor` group law (`boolFlip b₁ ∘ boolFlip b₂ =
  boolFlip (b₁ ⊕ b₂)`);
* every element is an involution;
* each `boolFlip b` preserves the unit sphere and leaves the Born image fixed.

Finally we record when the action is trivial and, in particular, that it is
**free on the strictly positive sphere** (`boolFlip b x = x ↔ b = 0` when every
coordinate of `x` is nonzero) — the group-theoretic reason the generic Born fiber
has the full `2ⁿ` elements.

## Main results

* `boolFlip_pm` — the sign vector of a boolean flip is `±1`.
* `boolFlip_false` — the all-`false` vector acts as the identity.
* `boolFlip_comp` — composition realizes the `xor` group law.
* `boolFlip_involutive` — every flip is an involution.
* `boolFlip_mem_sphere` — the action preserves the unit sphere.
* `bornMap_boolFlip` — the Born image is fixed by the action.
* `boolFlip_eq_self_iff` — `boolFlip b x = x` iff `b` is `false` on every
  nonzero coordinate of `x`.
* **headline** `boolFlip_free_of_pos` — the action is free on the strictly
  positive sphere: `boolFlip b x = x ↔ b = fun _ => false` when every coordinate
  of `x` is nonzero.

Everything is intended to be `sorry`-free and axiom-clean.
-/

open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge

namespace BookProof.ChapterFreeFieldBornSignAction

variable {n : ℕ}

/-- The `±1` sign vector determined by a boolean flip choice: coordinate `k` is
flipped (`-1`) exactly when `b k = true`. With this convention the group law on
boolean vectors is coordinate-wise `xor`. -/
def flipVec (b : Fin n → Bool) : Fin n → ℝ := fun k => if b k then -1 else 1

/-- The sign flip of `x` induced by a boolean flip vector `b`. -/
noncomputable def boolFlip (b : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  signFlip (flipVec b) x

@[simp] theorem boolFlip_apply (b : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    boolFlip b x k = (if b k then -1 else 1) * x k := rfl



/-
The all-`false` boolean vector acts as the identity.
-/


/-
**Composition follows the `xor` group law.** Flipping by `b₂` and then by
`b₁` is the single flip by the coordinate-wise `xor` `b₁ ⊕ b₂`; this exhibits
`boolFlip` as an action of the elementary abelian 2-group `(Fin n → Bool, ⊕)`.
-/


/-
Every sign flip is an involution.
-/






/-
`boolFlip b x = x` exactly when `b` is `false` on every nonzero coordinate of
`x` (the flip may act arbitrarily on the vanishing coordinates).
-/


/-
**Headline (free action on the strictly positive sphere).** If every
coordinate of `x` is nonzero, the diagonal sign action is free: `boolFlip b x = x`
forces `b` to be the identity `fun _ => false`. This is the group-theoretic
reason the Born fiber over a strictly positive distribution has the full `2ⁿ`
elements.
-/


end BookProof.ChapterFreeFieldBornSignAction


