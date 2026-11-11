-- Prove2me | Definitions.Def_FixedPolyominoSquare_SquareCounting_BinaryModel
-- name    : FixedPolyominoSquare_SquareCounting_BinaryModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:25.022209+00:00
-- url     : https://prove2.me/theorems/8c553a2a-d877-480a-beb4-a5d0715f0e6b
-- title:
--   Canonical binary inputs and the side-length encoding
-- statement:
--   A bit string is a finite list, written most significant bit first. The canonical code of zero is the one-bit string $0$, and positive integers have their usual leading-one code. The decoder accepts exactly these codes, and rejects the empty string and every redundant leading-zero representation. A pair of strings is encoded by tagging each bit of the first string with a preceding $1$, followed by a separator $0$ and the second string.
--
--   For a string $x$ of length $m$, define
--
--   $$\beta(x)=1x1\,0^m1\,0^{72m+72},\qquad E_{\rm side}(x)=\operatorname{val}_2(\beta(x)),\qquad p_U(m)=8(m+1).$$
--
--   These definitions fix the total input syntax and the exact side-encoding formula. They assert no parser, simulation or complexity correctness theorem.
-- source:
--   Qiuyu Chen, Ba'ao Xie, STOC 2027 submission #219 (October 2026), pp. 3, 6, Section 2 and Section 3

import Mathlib

namespace FixedPolyominoSquare.SquareCounting

abbrev Bits := List Bool

/-- Most significant bit first; the zero code is the one-bit word `0`. -/
def bin (n : ℕ) : Bits := if n = 0 then [false] else n.bits.reverse

def bitsValue (w : Bits) : ℕ :=
  w.foldl (fun n b => 2 * n + if b then 1 else 0) 0

/-- Rejects empty words and every redundant leading-zero representation. -/
def decode (w : Bits) : Option ℕ :=
  let n := bitsValue w
  if bin n = w then some n else none

/-- A self-delimiting pair code, of length `2*|x|+1+|y|`. -/
def pairBits (x y : Bits) : Bits :=
  x.flatMap (fun b => [true, b]) ++ [false] ++ y

def beta (x : Bits) : Bits :=
  [true] ++ x ++ [true] ++ List.replicate x.length false ++ [true] ++
    List.replicate (72 * x.length + 72) false

def Eside (x : Bits) : ℕ := bitsValue (beta x)

def pU (m : ℕ) : ℕ := 8 * (m + 1)

end FixedPolyominoSquare.SquareCounting


