-- Prove2me | Definitions.Def_MultiAccessLogspace_Halting_Encoding
-- name    : MultiAccessLogspace_Halting_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:35.718676+00:00
-- url     : https://prove2.me/theorems/26c64033-10e2-48f8-b0b9-64e896f7748d
-- title:
--   §5 — binary tuple encoding and iterated bit languages
-- statement:
--   Encode a tuple of finite bit strings by doubling each bit and separating adjacent fields by $01$. Each field can be empty; the encoded length is twice the total field length plus twice the number of separators. Natural numbers use the canonical least-significant-first binary expansion, with zero represented by the empty string. A bit position $i$ starts at one and is undefined if $i=0$ or $i>|y|$.
--
--   For a function $f$ on finite bit strings, let
--   $$
--   L_f=\{\operatorname{enc}(x,i): f(x)_i=1\},\qquad
--   L'_f=\{\operatorname{enc}(x,1^t,i):(f^{(t)}(x))_i=1\}.
--   $$
--   Here $t$ is unary, $i$ is binary, and $f^{(0)}$ is the identity. A string without such a tuple representation is outside the respective language. Out-of-range bit positions are outside as well.
--
--   These definitions make the inputs of amplification and composition explicit and give a total-language interpretation for Lemmas 5.2 and 5.3.
-- source:
--   William M. Hoza, STOC 2027 submission #92 (October 2026), §5.1 (pairs), §5.2, Eq. (2) (triples on PDF p. 11), PDF p. 10 (printed p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/92.pdf; PDF SHA-256 92de35889559d87b5a77d83317b9c7b2c8924912fbd5c712f2af3c005c8998d8

import Mathlib

/-!
Hoza, STOC 2027 submission #92: the source writes tuples `(x, k)`, `(x, i)`, `(x, 1^t, i)` as
inputs without fixing an encoding. This module fixes one, and the `1`-based bit lookup `y_i`.
-/

namespace MultiAccessLogspace.Halting

/-- Double every bit: `b₁ b₂ … ↦ b₁ b₁ b₂ b₂ …`. -/
def doubleBits (x : List Bool) : List Bool := x.flatMap fun b => [b, b]

/-- The self-delimiting encoding of a tuple of bit strings: every bit is doubled, and consecutive
fields are separated by `01`. Its length is linear in the total length of the fields. -/
def encodeFields (fields : List (List Bool)) : List Bool :=
  List.intercalate [false, true] (fields.map doubleBits)

/-- The binary digits of `k` (`Nat.bits`, least significant first, no redundant high zero; `0` has
the empty expansion). -/
def binary (k : ℕ) : List Bool := Nat.bits k

/-- The bit `y_i`, indexed from `1`. If `i = 0` or `i > |y|` it is undefined (`none`). -/
def bitAt (y : List Bool) (i : ℕ) : Option Bool :=
  if i = 0 then none else y[i - 1]?

/-- The language `L = {(x, i) : f(x)_i = 1}` of Eq. (2) (PDF p. 11). A string that encodes no pair,
or a pair with `i` out of range, is not in it. -/
def composeBase (f : List Bool → List Bool) : List Bool → Prop := fun s =>
  ∃ (x : List Bool) (i : ℕ), s = encodeFields [x, binary i] ∧ bitAt (f x) i = some true

/-- The language `L' = {(x, 1^t, i) : f^(t)(x)_i = 1}` of Eq. (2) (PDF p. 11), with `t` in unary and
`i` in binary. `t = 0` is included, with `f^(0) = id`. A string that encodes no triple, or a triple
with `i` out of range, is not in it. -/
def composeIter (f : List Bool → List Bool) : List Bool → Prop := fun s =>
  ∃ (x : List Bool) (t i : ℕ),
    s = encodeFields [x, List.replicate t true, binary i] ∧ bitAt (f^[t] x) i = some true

end MultiAccessLogspace.Halting


