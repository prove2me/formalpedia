-- Prove2me | Definitions.Def_IntractableCoding_Weights_Problems
-- name    : IntractableCoding_Weights_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:19.252297+00:00
-- url     : https://prove2.me/theorems/3f3e892c-5969-409e-bfc3-c356f2162cee
-- title:
--   COSET WEIGHTS and SUBSPACE WEIGHTS (Section III-A, III-B, p. 385): instances, yes-predicates and binary encodings
-- statement:
--   **COSET WEIGHTS.** An instance consists of a binary $m\times n$ matrix $A$, a binary vector $y$ of length $n$ and a nonnegative integer $w$. It is a yes-instance if there is a row vector $x\in\mathrm{GF}(2)^m$ of Hamming weight $|x|\le w$ with
--   $$xA=y\pmod 2.$$
--
--   **SUBSPACE WEIGHTS.** An instance consists of a binary $m\times n$ matrix $A$ and a nonnegative integer $w$. It is a yes-instance if there is a row vector $x\in\mathrm{GF}(2)^m$ of Hamming weight exactly $|x|=w$ with
--   $$xA=0\pmod 2.$$
--   With $A$ a parity-check matrix, this asks whether the code $\{x : xA=0\}$ has a word of weight $w$; COSET WEIGHTS is the decision form of syndrome decoding.
--
--   **Encodings.** An instance is presented to a machine as a binary string: the number of rows $m$ in unary ($m$ ones) followed by a $0$, the number of columns $n$ in unary followed by a $0$, the $mn$ entries of $A$ row by row, then (COSET WEIGHTS only) the $n$ entries of $y$, and finally $w$ in binary, each bit (least significant first) preceded by a $1$ and the whole number terminated by a $0$. The encodings are injective and their length is polynomial in $m$, $n$ and $\log w$.
--
--   **Formalization Note** Entries live in `ZMod 2`; $xA$ is `Matrix.vecMul x A` ($x$ indexed by the rows of $A$); the Hamming weight is `hammingNorm`.
-- source:
--   Berlekamp, McEliece & van Tilborg, On the Inherent Intractability of Certain Coding Problems, IEEE Trans. Inform. Theory IT-24(3), 1978, https://doi.org/10.1109/TIT.1978.1055873, p. 385, Section III-A and III-B

import Mathlib

namespace IntractableCoding.Weights

/-- An instance of COSET WEIGHTS (Section III-A, p. 385): a binary `m × n` matrix `A`
(entries in GF(2) = `ZMod 2`), a binary vector `y` of length `n`, and a nonnegative
integer `w`. -/
structure CosetInstance where
  /-- number of rows of `A` (= length of the unknown row vector `x`) -/
  m : ℕ
  /-- number of columns of `A` (= length of `y`) -/
  n : ℕ
  A : Matrix (Fin m) (Fin n) (ZMod 2)
  y : Fin n → ZMod 2
  w : ℕ

/-- An instance of SUBSPACE WEIGHTS (Section III-B, p. 385): a binary `m × n` matrix `A`
and a nonnegative integer `w`. -/
structure SubspaceInstance where
  /-- number of rows of `A` (= length of the unknown row vector `x`) -/
  m : ℕ
  /-- number of columns of `A` -/
  n : ℕ
  A : Matrix (Fin m) (Fin n) (ZMod 2)
  w : ℕ

/-- COSET WEIGHTS property: there is a row vector `x` of Hamming weight `≤ w` with `xA = y`
(computed over GF(2)). -/
def CosetWeightsYes (I : CosetInstance) : Prop :=
  ∃ x : Fin I.m → ZMod 2, hammingNorm x ≤ I.w ∧ Matrix.vecMul x I.A = I.y

/-- SUBSPACE WEIGHTS property: there is a row vector `x` of Hamming weight exactly `w` with
`xA = 0` (computed over GF(2)). -/
def SubspaceWeightsYes (I : SubspaceInstance) : Prop :=
  ∃ x : Fin I.m → ZMod 2, hammingNorm x = I.w ∧ Matrix.vecMul x I.A = 0

/-- The bit of an element of GF(2). -/
def bitOf (a : ZMod 2) : Bool := decide (a = 1)

/-- Self-delimiting binary encoding of a natural number: each bit of `k` (least significant
first, `Nat.bits`) is preceded by a `true` marker, and a final `false` ends the number. -/
def encodeNatBinary (k : ℕ) : List Bool :=
  (Nat.bits k).flatMap (fun b => [true, b]) ++ [false]

/-- Encoding of a COSET WEIGHTS instance: `m` in unary, a separator, `n` in unary, a
separator, the `m n` entries of `A` row by row, the `n` entries of `y`, and `w` in binary. -/
def encodeCoset (I : CosetInstance) : List Bool :=
  List.replicate I.m true ++ [false] ++ List.replicate I.n true ++ [false] ++
    (List.finRange I.m).flatMap (fun i => (List.finRange I.n).map (fun j => bitOf (I.A i j))) ++
    (List.finRange I.n).map (fun j => bitOf (I.y j)) ++ encodeNatBinary I.w

/-- Encoding of a SUBSPACE WEIGHTS instance: `m` in unary, a separator, `n` in unary, a
separator, the `m n` entries of `A` row by row, and `w` in binary. -/
def encodeSubspace (I : SubspaceInstance) : List Bool :=
  List.replicate I.m true ++ [false] ++ List.replicate I.n true ++ [false] ++
    (List.finRange I.m).flatMap (fun i => (List.finRange I.n).map (fun j => bitOf (I.A i j))) ++
    encodeNatBinary I.w

end IntractableCoding.Weights


