-- Prove2me | Definitions.Def_HardTilingSimple_DecisionCounting_BinaryCodec
-- name    : HardTilingSimple_DecisionCounting_BinaryCodec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T00:30:58.050339+00:00
-- url     : https://prove2.me/theorems/1620db87-ca8e-4782-a536-e462fa0dd0e4
-- title:
--   Canonical natural-number parsing and zigzag signed coordinates
-- statement:
--   The natural-number encoder is reused from ExponomialAssortment.FPTAS.encodeNat: a unary prefix of ones giving the binary payload length, a zero delimiter, and canonical little-endian binary digits. Zero has no payload, so its code is the single zero bit. The parser returns the decoded natural and remaining suffix, and rejects missing delimiters, truncation and noncanonical digits.
--
--   Signed coordinates use the zigzag bijection 0, -1, 1, -2, 2, ... mapped to 0, 1, 2, 3, 4, ... . Integer encoding applies the published natural-number encoder to the zigzag value. Integer decoding applies the inverse bijection after parsing. All integers are allowed; this is a general codec independent of any region or tile set.
-- source:
--   Moore and Robson, Hard Tiling Problems with Simple Tiles, Discrete & Computational Geometry 26, 573–590 (2001), published DOI https://doi.org/10.1007/s00454-001-0047-6, §2, p. 574 (PDF 2), complexity of finite-region inputs; the explicit signed binary convention is supplied by this formalization.

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine

namespace HardTilingSimple.DecisionCounting.BinaryCodec

def valueBits (bs : List Bool) : ℕ :=
  bs.foldr (fun b n => (if b then 1 else 0) + 2 * n) 0

/-- Parse one natural and return the unconsumed suffix; reject noncanonical digits. -/
def decodeNat (bs : List Bool) : Option (ℕ × List Bool) := do
  let k := (bs.takeWhile id).length
  match bs.drop k with
  | false :: rest =>
    if k ≤ rest.length then
      let ds := rest.take k
      let n := valueBits ds
      if ds = n.bits then some (n, rest.drop k) else none
    else none
  | _ => none

/-- Zigzag bijection: 0, -1, 1, -2, 2, ... have codes 0, 1, 2, 3, 4, ... . -/
def zigzag : ℤ → ℕ
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

def unzigzag (n : ℕ) : ℤ :=
  if n % 2 = 0 then Int.ofNat (n / 2) else Int.negSucc (n / 2)

def encodeInt (z : ℤ) : List Bool := ExponomialAssortment.FPTAS.encodeNat (zigzag z)

def decodeInt (bs : List Bool) : Option (ℤ × List Bool) := do
  let (n, rest) ← decodeNat bs
  pure (unzigzag n, rest)

end HardTilingSimple.DecisionCounting.BinaryCodec


