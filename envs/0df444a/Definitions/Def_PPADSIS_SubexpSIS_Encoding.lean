-- Prove2me | Definitions.Def_PPADSIS_SubexpSIS_Encoding
-- name    : PPADSIS_SubexpSIS_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:45:26.250975+00:00
-- url     : https://prove2.me/theorems/393ba8e0-e166-4c8e-a0ac-c3f4a76a3099
-- title:
--   Binary codes: unary, self-delimiting naturals, strings, pairs and integers; big-endian bits
-- statement:
--   The fixed binary codes used to hand objects to algorithms and adversaries.
--
--   - $1^\lambda$ (`unary`) is the string of $\lambda$ ones.
--   - `encNat a` is a self-delimiting binary code of $a\in\mathbb N$: each bit of $a$ (least significant first) is written as the pair $1b$, and a single $0$ ends the code.
--   - `encStr x` is a self-delimiting code of a bit string: each bit $b$ is written as $1b$, and $0$ ends the code; `encPair x y` is `encStr x` followed by $y$.
--   - `encInt z` is a sign bit followed by `encNat |z|`.
--   - `bitsBE w a` is the $w$-bit big-endian binary representation of $a$ (most significant bit first; exact for $a<2^w$), and `valBE` reads a bit string as a big-endian number.
--
--   All codes are prefix-free where they are concatenated, so every composite description in the mission is injective.
--
--   **Formalization Note** The paper fixes no encoding; these are conventions of the formalization.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), pp. 19-21, §3 (instances given by their descriptions); conventions of the formalization

import Mathlib

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

/-- The **unary** string `1^λ`. -/
def unary (lam : ℕ) : List Bool := List.replicate lam true

/-- Self-delimiting binary code of a natural number: each bit of `Nat.bits a` (least significant
first) is written as the pair `1b`, and a single `0` ends the code. Prefix-free and injective. -/
def encNat (a : ℕ) : List Bool := (Nat.bits a).flatMap (fun b => [true, b]) ++ [false]

/-- Self-delimiting code of a bit string: each bit `b` is written as `1b`, and `0` ends the code.
Prefix-free and injective. -/
def encStr (x : List Bool) : List Bool := x.flatMap (fun b => [true, b]) ++ [false]

/-- Code of a pair of strings: the first one self-delimited, the second appended. -/
def encPair (x y : List Bool) : List Bool := encStr x ++ y

/-- Self-delimiting code of an integer: a sign bit (`true` for negative), then `encNat |z|`. -/
def encInt (z : ℤ) : List Bool := decide (z < 0) :: encNat z.natAbs

/-- The `w`-bit **big-endian** binary representation of `a` (most significant bit first; the bits
of `a` above position `w` are dropped, so it is exact for `a < 2^w`). -/
def bitsBE : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, a => decide (a / 2 ^ w % 2 = 1) :: bitsBE w a

/-- The number written by a big-endian bit string: `[b_{k-1}, …, b_0] ↦ ∑ b_i 2^i`. -/
def valBE (l : List Bool) : ℕ := l.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0

end PPADSIS.SubexpSIS


