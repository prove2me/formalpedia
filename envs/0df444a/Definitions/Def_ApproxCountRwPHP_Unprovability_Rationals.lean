-- Prove2me | Definitions.Def_ApproxCountRwPHP_Unprovability_Rationals
-- name    : ApproxCountRwPHP_Unprovability_Rationals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:56:00.419801+00:00
-- url     : https://prove2.me/theorems/1e8a0cad-901f-4399-8508-995b0e98416a
-- title:
--   Rational encodings and total decoding
-- statement:
--   Rational values are encoded by sign, binary numerator and denominator, and a self-delimiting length field. Zero and one use the Boolean representations. Decoding returns an optional rational, rejecting zero denominators and malformed descriptions.
--
--   $$\operatorname{rationalValue}(x)=\begin{cases}q&\text{if decoding succeeds with }q,\\0&\text{otherwise.}\end{cases}$$
--
--   The Basic Axiom explicitly requires successful rational decoding. Consequently the arithmetic default never supplies validity for an invalid counting answer. Rational equality in the Boundary Axiom compares values rather than the choice of encoding.
-- source:
--   Oliver Korten, Jiatu Li, Igor Oliveira, Hanlin Ren, STOC 2027 submission #1023 (October 2026), §2.2, §3.1, printed p. 13–16, PDF p. 15–18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1023.pdf#page=15–18

import Definitions.Def_ApproxCountRwPHP_Unprovability_Strings

namespace ApproxCountRwPHP.Unprovability

/-! Efficient rational encodings for §2.2 and §3.1. Zero and one have the same
representations as Boolean output values. Other rationals use a sign bit,
a unary length delimiter, then binary numerator and denominator. Invalid
encodings are rejected by the Basic Axiom; arithmetic is totalized to zero
on them and is used only after that axiom has supplied validity. -/
def encodeRational (q : ℚ) : BitString :=
  if q = 0 then [] else if q = 1 then [true] else
  let num := numeral q.num.natAbs
  [false, q.num < 0] ++ unary num.length ++ [false] ++ num ++ numeral q.den

def decodeRational (x : BitString) : Option ℚ :=
  match x with
  | [] => some 0
  | [true] => some 1
  | false :: sign :: rest =>
      let n := (rest.takeWhile id).length
      let tail := rest.drop (n + 1)
      if rest.getD n true = false && n ≤ tail.length then
        let denominator := number (tail.drop n)
        if denominator = 0 then none else
          some ((if sign then -(number (tail.take n) : ℚ) else (number (tail.take n) : ℚ)) /
            (denominator : ℚ))
      else none
  | _ => none

def rationalValue (x : BitString) : ℚ := (decodeRational x).getD 0

end ApproxCountRwPHP.Unprovability


