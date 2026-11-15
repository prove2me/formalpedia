-- Prove2me | Definitions.Def_StableMSR_Recovery_Supplement_BinaryEncoding
-- name    : StableMSR_Recovery_Supplement_BinaryEncoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T03:11:53.909336+00:00
-- url     : https://prove2.me/theorems/8b8a6970-77d0-4608-ae6c-28dbd9d0c563
-- title:
--   Parsers for published binary integers and rational numbers
-- statement:
--   Use the published QAlgorithms.LocalHamiltonian.encBin binary convention for the rational finite inputs of Appendix C; no new natural-number encoder is defined. A natural number is encoded by its little-endian binary digits, each prefixed by a true marker, followed by the two-bit terminator $00$. Thus an integer of bit length $b$ has code length $2b+2$, including the terminator. Zero has the two-bit code $00$.
--
--   $$
--   \operatorname{code}(q)=\operatorname{code}(s)\,\operatorname{code}(|u|)\,\operatorname{code}(v),\qquad q=u/v,
--   $$
--
--   where $q$ is in reduced form with $v>0$, and $s=1$ exactly for a negative numerator. Parsers require canonical integer and rational representations and reject truncation. Lists of these self-delimiting fields concatenate without ambiguity.
--
--   This is an explicit ordinary binary convention for input and certificate lengths. It uses logarithmic-length integer codes; no unary encoding of input values or arbitrary coding oracle is used.
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), p. 4 bit model; Appendix C pp. 23–26, rational binary input conventions; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Supplement

abbrev Bits := List Bool

/-- Each payload bit is prefixed by true; false,false terminates the integer. -/
def takeBinary : ℕ → Bits → Option (Bits × Bits)
  | _, false :: false :: rest => some ([],rest)
  | fuel + 1, true :: b :: rest => do
    let (bs,tail) ← takeBinary fuel rest
    pure (b :: bs,tail)
  | _, _ => none

def takeNat (w : Bits) : Option (ℕ × Bits) := do
  let (bs,rest) ← takeBinary w.length w
  let n := Nat.ofDigits 2 (bs.map (fun b => if b then 1 else 0))
  if QAlgorithms.LocalHamiltonian.encBin n ++ rest = w then some (n,rest) else none

def readNats : ℕ → Bits → Option (List ℕ)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, w => do
    let (x, rest) ← takeNat w
    let xs ← readNats fuel rest
    pure (x :: xs)

def packNats (ns : List ℕ) : Bits := ns.flatMap QAlgorithms.LocalHamiltonian.encBin

def ratNumbers (q : ℚ) : List ℕ := [if q < 0 then 1 else 0, q.num.natAbs, q.den]

def takeRat : List ℕ → Option (ℚ × List ℕ)
  | sign :: num :: den :: rest =>
    let q : ℚ := (if sign = 0 then (num : ℤ) else -(num : ℤ)) / (den : ℚ)
    if sign ≤ 1 ∧ 0 < den ∧ ratNumbers q = [sign,num,den] then some (q,rest) else none
  | _ => none

def takeRats : ℕ → List ℕ → Option (List ℚ × List ℕ)
  | 0, ns => some ([],ns)
  | t + 1, ns => do
    let (q, rest) ← takeRat ns
    let (qs, tail) ← takeRats t rest
    pure (q :: qs,tail)

end StableMSR.Recovery.Supplement


