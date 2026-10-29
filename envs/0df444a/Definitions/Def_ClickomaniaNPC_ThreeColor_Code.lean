-- Prove2me | Definitions.Def_ClickomaniaNPC_ThreeColor_Code
-- name    : ClickomaniaNPC_ThreeColor_Code
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T03:26:36.360297+00:00
-- url     : https://prove2.me/theorems/ec1b1632-81dc-4bb2-a1e5-7820fa763ef7
-- title:
--   Self-delimiting binary natural-number codes and concrete parsing
-- statement:
--   Natural numbers are encoded over the two-symbol alphabet {0,1}. For n, let l be its binary size plus one (the size of zero is zero). Its code consists of l ones, a zero delimiter, and l binary digits in low-order-first order, padded with zeros. Thus zero has code 100. Every number has a nonempty, self-delimiting code.
--
--   The concrete parser reads the unary length prefix, checks that the length is positive and that enough payload bits remain, computes the value of those bits, and checks that the consumed prefix is exactly the canonical encoding of that value. It returns the number and the unused suffix. It rejects a missing delimiter, a truncated payload, a zero length or noncanonical padding. A second parser reads a specified finite number of such codes and returns their values and the remaining suffix.
--
--   These are general number-encoding operations, independent of the puzzle rules. The paper does not fix a bit syntax; this is an explicit encoding convention for its computational decision problem, with logarithmic code length for each natural number.
-- source:
--   Biedl, Demaine, Demaine, Fleischer, Jacobsen and Munro, The Complexity of Clickomania, arXiv:cs/0107031v1 (21 July 2001), section 1, p. 1; section 4, Theorem 15, p. 11. https://arxiv.org/abs/cs/0107031v1

import Mathlib

namespace ClickomaniaNPC.ThreeColor

/-- Low-order-first binary digits, padded to the specified length. -/
def lowBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | l + 1, n => (n % 2 == 1) :: lowBits l (n / 2)

def bitsValue (bits : List Bool) : ℕ :=
  bits.foldr (fun b n => b.toNat + 2 * n) 0

/-- A self-delimiting natural code: l ones, a zero, and l low-order-first bits,
where l = Nat.size n + 1. In particular zero is coded, not omitted. -/
def encodeNat (n : ℕ) : List Bool :=
  let l := n.size + 1
  List.replicate l true ++ false :: lowBits l n

/-- Read the unary length prefix and its terminating zero. -/
def readLength : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (l, tail) ← readLength rest
      pure (l + 1, tail)

/-- Read one canonical natural code. Reject truncated payloads, zero lengths,
and noncanonical padding. Return the unused suffix. -/
def readNat (s : List Bool) : Option (ℕ × List Bool) := do
  let (l, rest) ← readLength s
  if l = 0 ∨ rest.length < l then none else
    let payload := rest.take l
    let n := bitsValue payload
    if encodeNat n = List.replicate l true ++ false :: payload then
      some (n, rest.drop l)
    else none

/-- Read precisely n natural numbers, without silently discarding any suffix. -/
def readNats : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0, s => some ([], s)
  | n + 1, s => do
      let (a, rest) ← readNat s
      let (as, tail) ← readNats n rest
      pure (a :: as, tail)

end ClickomaniaNPC.ThreeColor


