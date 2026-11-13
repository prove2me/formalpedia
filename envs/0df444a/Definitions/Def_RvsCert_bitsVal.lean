-- Prove2me | Definitions.Def_RvsCert_bitsVal
-- name    : RvsCert_bitsVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:19.666502+00:00
-- url     : https://prove2.me/theorems/5e36c19b-aff9-440c-8797-2db6d3a30fd6
-- title:
--   Binary value of a block of bits
-- statement:
--   A block of $w$ bits $b_0,\dots,b_{w-1}$ encodes the number
--   $$
--   \sum_{t=0}^{w-1} b_t\,2^t,
--   $$
--   with $b_0$ the least significant bit. Race entries and card entries are decoded this way.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Section 2, p.2 (encoding of numbers)

import Mathlib

namespace RvsCert

/-- **Binary value of a block of bits** (encoding convention for Section 2, p.2 of
Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): `bitsVal b = ∑ₜ b(t)·2ᵗ`, bit `0` least significant. -/
def bitsVal {w : ℕ} (b : Fin w → Bool) : ℕ :=
  ∑ t : Fin w, if b t then 2 ^ (t : ℕ) else 0

end RvsCert


