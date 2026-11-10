-- Prove2me | Definitions.Def_NashOrTriangle_decode
-- name    : NashOrTriangle_decode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:48:17.556755+00:00
-- url     : https://prove2.me/theorems/6bd3701a-0a3e-44e7-9e65-a67d18a97962
-- title:
--   Decoding the output of a halted program
-- statement:
--   When the program halts, its answer is read from memory starting at the address it names. The answer is either a **strategy pair** — a finite rational mixture of known rows and one of known columns, each written as a count followed by (label, weight) pairs — or a **triangle**, written as a length $\ell$ followed by $\ell$ row labels and $\ell$ column labels. A leading tag ($0$ or $1$) says which.
--
--   **Formalization Note** The memory layout is a convention; any fixed layout gives an equivalent theorem.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Definition 1.1, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_NashOrTriangle_OracleMachine

namespace NashOrTriangle

/-- A decoded answer, in labels: a strategy pair (a row-label mixture `p` and a column-label
mixture `q`), or a triangle (a list of row labels and a list of column labels). -/
inductive Answer where
  | pair (p q : ℕ →₀ ℚ)
  | triangle (rs cs : List ℕ)

/-- Decode the answer written in memory at address `base` when the program halts.
Layout: cell `base` is a tag. Tag `0` (a pair): at `base + 1` the row mixture (a count `n`, then
`n` pairs label, weight), immediately followed by the column mixture in the same format. Tag `1`
(a triangle): at `base + 1` a length `ℓ`, then `ℓ` row labels, then `ℓ` column labels. Anything
else does not decode.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Definition 1.1, printed p. 3 (PDF p. 4): "Mixed strategies in inputs and outputs are
finitely supported and have rational probabilities."

**Formalization Note** The memory layout is a convention of this formalization; any fixed
layout gives an equivalent theorem up to a constant number of steps. -/
noncomputable def decode (mem : ℤ → ℝ) (base : ℤ) : Option Answer :=
  (readNat (mem base)).bind fun tag =>
    if tag = 0 then
      (readMix mem (base + 1)).bind fun np =>
        (readMix mem (base + 2 + 2 * (np.1 : ℤ))).map fun mq => Answer.pair np.2 mq.2
    else if tag = 1 then
      (readNat (mem (base + 1))).bind fun len =>
        ((List.range len).mapM fun i => readNat (mem (base + 2 + (i : ℤ)))).bind fun rs =>
          ((List.range len).mapM fun i => readNat (mem (base + 2 + (len : ℤ) + (i : ℤ)))).map
            fun cs => Answer.triangle rs cs
    else none

end NashOrTriangle


