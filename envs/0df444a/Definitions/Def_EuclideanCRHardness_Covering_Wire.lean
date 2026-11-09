-- Prove2me | Definitions.Def_EuclideanCRHardness_Covering_Wire
-- name    : EuclideanCRHardness_Covering_Wire
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:28.133809+00:00
-- url     : https://prove2.me/theorems/607a58e9-a523-43d8-9e04-33fba98a6fba
-- title:
--   Binary integer and rational field codec
-- statement:
--   An integer is stored as a sign bit and a length-delimited binary magnitude. A list begins with its binary field count, followed by its signed integer fields. Rational numbers use the signed numerator and positive denominator of their reduced fraction. Length delimiters repeat the number of binary digits, not the numerical value of a field.
--
--   These fixed codecs support the computational claims without unary expansion of large numbers. The parser rejects truncation, a nonpositive rational denominator, and trailing unconsumed bits.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, STOC 2027 submission #38 (October 2026), binary input convention after Definition 1.1, printed p. 1 / PDF p. 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/38.pdf

import Mathlib

namespace EuclideanCRHardness.Covering

def lengthPrefixedWord (word : List Bool) : List Bool :=
  List.replicate word.length true ++ false :: word
def readUnaryPrefix : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false::rest => some (0,rest)
  | true::rest => do
      let (n,tail) ← readUnaryPrefix rest
      return (n+1,tail)
def readLengthPrefixedWord (bits : List Bool) : Option (List Bool × List Bool) := do
  let (n,rest) ← readUnaryPrefix bits
  if n ≤ rest.length then some (rest.take n, rest.drop n) else none

/-- Signed binary integers; length prefixes count bits, never integer magnitudes. -/
def intWord (z : ℤ) : List Bool :=
  (z < 0) :: lengthPrefixedWord (Computability.encodeNat z.natAbs)
def readInt (bits : List Bool) : Option (ℤ × List Bool) := do
  let sign :: rest := bits | none
  let (word, tail) ← readLengthPrefixedWord rest
  let a : ℤ := Computability.decodeNat word
  return (if sign then -a else a, tail)
def readInts : ℕ → List Bool → Option (List ℤ × List Bool)
  | 0, bits => some ([], bits)
  | n+1, bits => do
      let (z, rest) ← readInt bits
      let (zs, tail) ← readInts n rest
      return (z::zs, tail)
def wireEncode (zs : List ℤ) : List Bool :=
  lengthPrefixedWord (Computability.encodeNat zs.length) ++ zs.flatMap intWord
def wireDecode (bits : List Bool) : Option (List ℤ) := do
  let (word, rest) ← readLengthPrefixedWord bits
  let (zs, tail) ← readInts (Computability.decodeNat word) rest
  if tail.isEmpty then some zs else none
def ratFields (q : ℚ) : List ℤ := [q.num, q.den]
def readRat : List ℤ → Option (ℚ × List ℤ)
  | a::b::tail => if 0 < b then some ((a : ℚ) / (b : ℚ), tail) else none
  | _ => none
def readRats : List ℤ → Option (List ℚ)
  | [] => some []
  | a::b::tail => do
      if b ≤ 0 then none else do
        let qs ← readRats tail
        return ((a : ℚ) / (b : ℚ)) :: qs
  | _ => none

end EuclideanCRHardness.Covering


