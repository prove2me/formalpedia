-- Prove2me | Definitions.Def_DerivationHitting_Commutative_Supplement_AlgorithmData
-- name    : DerivationHitting_Commutative_Supplement_AlgorithmData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:55:14.429194+00:00
-- url     : https://prove2.me/theorems/369c3d45-9a31-490e-894f-986bf9496938
-- title:
--   Executable binary emission of the rational matrix tuple
-- statement:
--   The input encoding is n unary ones, a separator, then s unary ones, so its length is n+s+1. A fixed six-symbol alphabet contains two binary digits, two signs, a separator and a header marker. A natural magnitude is written in little-endian binary, with zero represented by the empty digit sequence. Each rational entry is emitted as a sign, numerator magnitude, separator, positive denominator magnitude, separator. Fractions need not be reduced.
--
--   The executable map writes a header containing n and B=ns²+s in binary, then the nB² numerator-denominator pairs in variable, row, column order. Each pair is exactly that used to define the §5 rational matrices:
--
--   $$\bigl((-1)^{r-k-1}i^{r-k},r\bigr)\quad(k<r),\qquad (0,1)\quad(k\ge r).$$
--
--   All loops are finite natural-number loops. This definition supplies an actual output word; polynomial Turing time is asserted in Theorem 1.2, rather than assumed in the definition. The rational output is independent of the field and of the polynomial being tested.
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026). Canonical submission artifact, not proceedings publication; no arXiv pin. Printed page = PDF page throughout 1–29. p.5, Theorem 1.2; p.21, explicit construction in Theorem 5.12.

import Definitions.Def_DerivationHitting_Commutative_Supplement_MatrixData

namespace DerivationHitting.Commutative.Supplement

/-- Six fixed symbols: binary digits 0,1; plus 2; minus 3; separator 4; header 5. -/
abbrev OutputSymbol := Fin 6

/-- Little-endian binary magnitude; zero is the empty digit string, delimited by 4. -/
def binaryMagnitude (a : ℕ) : List OutputSymbol :=
  (Nat.digits 2 a).map fun b => if b = 0 then 0 else 1

def encodePair (p : ℤ × ℕ) : List OutputSymbol :=
  [if p.1 < 0 then 3 else 2] ++ binaryMagnitude p.1.natAbs ++ [4] ++
    binaryMagnitude p.2 ++ [4]

/-- Unary n, separator, unary s. Input length is n+s+1. -/
def unaryInput (p : ℕ × ℕ) : List OutputSymbol :=
  List.replicate p.1 1 ++ [4] ++ List.replicate p.2 1

/-- One executable bounded-loop emitter: header n,B, followed by variable/row/column order.
Each entry is an unreduced signed integer numerator and positive denominator in binary. -/
def rationalMatrixOutput (p : ℕ × ℕ) : List OutputSymbol :=
  let n := p.1
  let B := cutoff n p.2
  [5] ++ binaryMagnitude n ++ [4] ++ binaryMagnitude B ++ [4] ++
    (List.range n).flatMap fun i =>
      (List.range B).flatMap fun r =>
        (List.range B).flatMap fun k => encodePair (sectionEntryPair i r k)

end DerivationHitting.Commutative.Supplement


