-- Prove2me | Definitions.Def_ChapterRotaryPosition
-- name    : ChapterRotaryPosition
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T10:58:28.915245+00:00
-- url     : https://prove2.me/theorems/b904999d-f672-463e-8c44-150de8e8af52
-- title:
--   Chapter RotaryPosition
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterRotaryPosition.lean`): generated def bundle for ChapterRotaryPosition. See BookProof/ChapterRotaryPosition.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterRotaryPosition.lean

import Definitions.Def_ChapterCoherentOverlapComplex
import Mathlib


/-!
# Chapter "The Coherent State of Attention" — position enters only as a relative
phase

A transformer head has to know *where* its tokens are, and the rotary encoding
does this by rotating each complex coordinate of the query and the key by an
angle proportional to the token's position: `q ↦ (e^{i p ωᵢ} qᵢ)ᵢ`.  This module
proves the property that makes the device work: after the encoding, the alignment
of a query at position `a` with a key at position `b` depends on `a` and `b`
**only through the offset `b − a`**.  Absolute position is unobservable; relative
position is the whole content.

Deliverables (all `sorry`-free, `axiom`-free):

* `rotaryEncode ω p` — the rotary positional encoding at position `p` with
  per-coordinate frequencies `ω`;
* `rotaryEncode_zero`, `rotaryEncode_add` — it is an action of the additive group
  of positions;
* `norm_rotaryEncode` — it is norm preserving (each coordinate is multiplied by a
  unit-modulus phase), hence a unitary;
* **`inner_rotaryEncode`** — the headline: `⟪R_a q, R_b k⟫ = ⟪q, R_{b−a} k⟫`, so
  the complex alignment depends only on the offset; `inner_rotaryEncode_shift`
  states the shift invariance directly;
* `coherentOverlapC_rotaryEncode`, `bornWeightC_rotaryEncode_shift` — the Bargmann
  kernel and hence every coherent-state attention weight inherit the same
  invariance: translating the whole sequence changes nothing.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/

open scoped BigOperators

noncomputable section

namespace BookProof.ChapterRotaryPosition

open BookProof.ChapterCoherentOverlapComplex

variable {n m : ℕ}

/-! ## The rotary encoding -/

/-- The **rotary positional encoding**: at position `p`, the `i`-th complex
coordinate is rotated by the angle `p·ωᵢ`. -/
def rotaryEncode (omega : Fin n → ℝ) (p : ℝ) (q : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun i => Complex.exp ((p * omega i : ℝ) * Complex.I) * q i









/-! ## Only the relative position is visible -/











end BookProof.ChapterRotaryPosition

end


