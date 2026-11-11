-- Prove2me | Definitions.Def_QuadExt_Main_Bits
-- name    : QuadExt_Main_Bits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:03:00.867503+00:00
-- url     : https://prove2.me/theorems/4dac1cac-f948-4932-9924-6317ec055eb0
-- title:
--   Bit strings as inputs and outputs of an explicit (polynomial-time) machine
-- statement:
--   "We say that the extractor is **explicit** if it is a deterministic polynomial time algorithm" (Definition 1.1). Explicitness is the published `LowErrExt_IsPolyTime`: a function $F$ from tuples of bit strings to bit strings is explicit if one Turing machine computes it on every input in time polynomial in the input length. This module fixes how the objects of the paper are given to and read from such a machine: a string $x \in \mathbb F_2^n$ is the list of its $n$ bits (`toBits`), a number $k$ is written in unary as $1^k$ (`unary k`), and the first $m$ bits of an output list are read as an element of $\mathbb F_2^m$ (`ofBits m`).
--
--   **Formalization Note.** Statements that read an output with `ofBits m` also assert that the output has length exactly $m$.
-- source:
--   Chandrasekaran, Goodman, Zuckerman, Quadratic Extractors, STOC 2027 submission (manuscript sha256 ddc80a9a…), p. 1 (PDF 2), Definition 1.1

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime

namespace QuadExt.Main

/-!
# Bit strings as machine inputs and outputs

Chandrasekaran, Goodman, Zuckerman, *Quadratic Extractors*, STOC 2027 submission (manuscript
sha256 ddc80a9a…), p. 1 (PDF 2), Definition 1.1: "We say that the extractor is explicit if it is a
deterministic polynomial time algorithm." Explicitness is the published
`LowErrExt.IsPolyTime F` (one Turing machine computing `F : List (List Bool) → List Bool` in time
polynomial in the input length); this module converts between `𝔽₂` strings and the machine's
lists of bits.
-/

/-- An `𝔽₂` string `x ∈ 𝔽₂^n` written as a list of `n` bits (`1 ↦ true`, `0 ↦ false`). -/
def toBits {n : ℕ} (x : Fin n → ZMod 2) : List Bool :=
  List.ofFn fun i => decide (x i = 1)

/-- A number `k` written in **unary**, `1^k`. -/
def unary (k : ℕ) : List Bool :=
  List.replicate k true

/-- The first `m` bits of a machine output, as an element of `𝔽₂^m` (via `LowErrExt.listOut`;
statements also assert that the output has length exactly `m`). -/
def ofBits (m : ℕ) (l : List Bool) : Fin m → ZMod 2 :=
  fun i => if LowErrExt.listOut m l i then 1 else 0

end QuadExt.Main


