-- Prove2me | Definitions.Def_TargetedSamplers_encInput
-- name    : TargetedSamplers_encInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:03:54.78142+00:00
-- url     : https://prove2.me/theorems/5b28b4f2-2bd4-4de5-bc57-5a9ac0d9e7cc
-- title:
--   Encodings of several arguments as one input string
-- statement:
--   Algorithms in §4.3 take several arguments, e.g. $(x,j)$, $(x,i,j)$, $(1^n,i)$. A natural number $v$ is written in the self-delimiting code $\mathrm{enc}(v)$: each bit of its binary expansion (least significant first) is preceded by a $1$, and the code ends with a $0$. A list of numbers followed by a list of strings is the concatenation of the codes of the numbers, then, for each string, the code of its length followed by the string itself.
--
--   The definition also fixes the little-endian value $\mathrm{ofBits}(q)=\sum_i q_i 2^i$ of a bit string, the fixed-width binary $\mathrm{bits}_w(v)$ (the $w$ low-order bits of $v$), and the conversions between bit lists and bit vectors.
--
--   **Formalization Note** The paper fixes no encoding. This one lets an algorithm recover each argument, and it reaches the last string at a polylogarithmic offset.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), §4.3, pp.30–39 (pdf pp.32–41)

import Mathlib

namespace TargetedSamplers

/-- Self-delimiting binary code of a natural number: each bit of its little-endian binary expansion
is preceded by `1`, and the code ends with `0`. -/
def encNat (v : ℕ) : List Bool := (Nat.bits v).flatMap (fun b => [true, b]) ++ [false]

/-- Natural number of a little-endian bit string (leading zeros allowed). -/
def ofBitsLE : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * ofBitsLE l

/-- The `w` low-order bits of `v`, least significant first (fixed-width binary). -/
def bitsFixed (w v : ℕ) : List Bool := List.ofFn (fun j : Fin w => v.testBit j)

/-- The bit string of a list of numbers followed by a list of strings, as one input
(Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…,
§4.3: algorithms "get input (x, j)", "(x, i, j)", "(1ⁿ, i)").

**Formalization Note** The paper gives several arguments to one algorithm without fixing an
encoding. Numbers are written with `encNat`, and each string is preceded by `encNat` of its length,
so the arguments can be recovered and random access into the last string costs a polylogarithmic
offset. -/
def encInput (nums : List ℕ) (strs : List (List Bool)) : List Bool :=
  nums.flatMap encNat ++ strs.flatMap (fun s => encNat s.length ++ s)

/-- A vector of bits as a list. -/
def toList {n : ℕ} (x : Fin n → Bool) : List Bool := List.ofFn x

/-- A list of bits as a vector indexed by its positions. -/
def toVec (x : List Bool) : Fin x.length → Bool := fun j => x.get j

end TargetedSamplers


