-- Prove2me | Definitions.Def_HypRecov_encNat
-- name    : HypRecov_encNat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:59.184685+00:00
-- url     : https://prove2.me/theorems/d38a4535-3209-406d-8179-b5e835cfde70
-- title:
--   Self-delimiting binary codes for bits, numbers, integers and vertex sets
-- statement:
--   The machines read and write bit strings. A bit string $l$ is written with each bit $b$ as the pair $1,b$ followed by a closing $0$ (length $2|l|+1$); a natural number is its binary expansion written this way (length $O(\log x)$); an integer is its sign bit followed by its absolute value; a vertex set $A\subseteq\{0,\dots,n-1\}$ is the increasing list of its members, each in binary preceded by a $1$, followed by a $0$ (length $O(|A|\log n)$); the parameters $n,r,k,m$ are four numbers in binary.
--
--   All codes are self-delimiting, so concatenations decode uniquely. Integers are binary because the update time of Theorem 1.1 is polynomial in the bit length of the increment.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 1.1, p.2 (PDF p.3)

import Mathlib

namespace HypRecov

/-- **Self-delimiting binary codes.** Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous Projection
Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Theorem 1.1, p.2 (PDF p.3): "Update
time also accounts for the supplied increment's bit length."

`encBits l` writes each bit `b` of `l` as the pair `true, b` and ends with `false`; it is
self-delimiting and has length `2|l| + 1`. -/
def encBits (l : List Bool) : List Bool := l.flatMap (fun b => [true, b]) ++ [false]

/-- A natural number in binary (`Nat.bits`, least significant bit first), self-delimited. Its length
is `2 ⌈log₂(x+1)⌉ + 1`. -/
def encNat (x : ℕ) : List Bool := encBits x.bits

/-- An integer: its sign bit, then its absolute value in binary. The length is linear in the bit
length of the integer.

**Formalization Note.** A unary code would make the update time bound of Theorem 1.1, which is
polynomial in the bit length of the increment, unsatisfiable; the code is binary. -/
def encInt (z : ℤ) : List Bool := decide (z < 0) :: encNat z.natAbs

/-- A vertex set `A ⊆ Fin n`: its members in increasing order, each as a binary number preceded by
`true`, and a closing `false`. Its length is `O(|A| log n)`. -/
def encSet {n : ℕ} (A : Finset (Fin n)) : List Bool :=
  ((List.finRange n).filter (fun v => decide (v ∈ A))).flatMap (fun v => true :: encNat v.val) ++
    [false]

/-- The parameters `n, r, k` and `m = ⌈1/η⌉`, each in binary. -/
def encParams (n r k m : ℕ) : List Bool := encNat n ++ encNat r ++ encNat k ++ encNat m

end HypRecov


