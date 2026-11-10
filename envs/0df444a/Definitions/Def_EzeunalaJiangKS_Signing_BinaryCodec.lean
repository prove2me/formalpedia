-- Prove2me | Definitions.Def_EzeunalaJiangKS_Signing_BinaryCodec
-- name    : EzeunalaJiangKS_Signing_BinaryCodec
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T01:01:03.256683+00:00
-- url     : https://prove2.me/theorems/eb3ff849-c3b5-4fc2-a3f3-f83823af1702
-- title:
--   Canonical binary codec for rational matrix lists
-- statement:
--   Each input consists of dimensions $d,N$ and $N$ matrices whose entries are pairs of rational numbers. Their complex interpretation is $a+ib$. Natural numbers use the gamma-style prefix code of $a+1$; integers have a negative-sign bit followed by the code of their absolute value. A rational uses its canonical reduced numerator and positive denominator.
--   $$w=\operatorname{enc}(d)\operatorname{enc}(N)\prod_{i=1}^N\bigl(1\,\operatorname{entries}(H_i)\bigr)0.$$
--   Entries are in row order, real part before imaginary part. The validity promise is only Hermitian symmetry and rank at most one. Enumerating canonical encodings specifies exactly the valid words without invoking a free parser or a signing oracle. Empty dimensions and lists remain allowed; each matrix consumes a marker. This codec makes the bit length explicit.
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), Theorem 1.1 and rationality footnote, printed p. 3 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_MatrixData

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

/-- Most-significant-first suffix of length k. -/
def binarySuffix (a k : ℕ) : List Bool :=
  (List.range k).map (fun j => a.testBit (k - 1 - j))

/-- Gamma-style code for a+1. Nat.log2(1)=0, so zero is encoded as [false]. -/
def encodeNat (a : ℕ) : List Bool :=
  let k := Nat.log2 (a + 1)
  List.replicate k true ++ [false] ++ binarySuffix (a + 1) k

def encodeInt (a : ℤ) : List Bool := decide (a < 0) :: encodeNat a.natAbs

def encodeRat (a : ℚ) : List Bool := encodeInt a.num ++ encodeNat a.den

structure RationalInput where
  d : ℕ
  N : ℕ
  entries : Fin N → Fin d → Fin d → ℚ × ℚ

def RationalInput.matrices (I : RationalInput) : Fin I.N → CMat I.d :=
  fun i j k => (I.entries i j k).1 + (I.entries i j k).2 * Complex.I

def RationalInput.word (I : RationalInput) : List Bool :=
  encodeNat I.d ++ encodeNat I.N ++
  ((List.finRange I.N).flatMap fun i => true ::
    ((List.finRange I.d).flatMap fun j =>
      (List.finRange I.d).flatMap fun k =>
        encodeRat (I.entries i j k).1 ++ encodeRat (I.entries i j k).2)) ++ [false]

def RationalInput.valid (I : RationalInput) : Prop :=
  ∀ i, (I.matrices i).IsHermitian ∧ (I.matrices i).rank ≤ 1

end EzeunalaJiangKS.Signing


