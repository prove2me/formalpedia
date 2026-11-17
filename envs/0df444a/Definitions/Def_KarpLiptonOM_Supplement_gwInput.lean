-- Prove2me | Definitions.Def_KarpLiptonOM_Supplement_gwInput
-- name    : KarpLiptonOM_Supplement_gwInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:42:18.303895+00:00
-- url     : https://prove2.me/theorems/061d4605-7752-4e4d-8fea-aa221ca1f306
-- title:
--   Input encoding of a matrix circuit: $1^a0\,1^b0\,\langle V\rangle$
-- statement:
--   The procedure of Theorem A.5.2 receives a circuit $V:\{0,1\}^a\times\{0,1\}^b\to\{0,1\}$ with at most $s$ gates as the string
--
--   $$
--   1^a\,0\,1^b\,0\,\langle V\rangle_{a+b,s},
--   $$
--
--   where $\langle V\rangle_{a+b,s}$ is the paper's fixed code of circuits with $a+b$ inputs and at most $s$ gates. The dimensions $a$ and $b$ are written in unary, as a circuit description lists its inputs, so a polynomial-time machine can write down a row or a column.
--
--   **Formalization Note** The circuit code is the published `KarpLiptonOM.circuitCode`; the row occupies the first $a$ inputs.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Theorem A.5.2, p.33; circuit encoding §A.2.1, p.20

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit
import Definitions.Def_KarpLiptonOM_circuitCode

namespace KarpLiptonOM.Supplement

/-- The input of the procedure of Theorem A.5.2 (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.33): a circuit `V : {0,1}^a × {0,1}^b → {0,1}`
with at most `s` gates, written as `1ᵃ 0 1ᵇ 0` followed by the fixed circuit code
`circuitCode (a + b) s V` (§A.2.1, p.20).

**Formalization Note** `a` and `b` are given in unary (a circuit description lists its inputs), so a
polynomial-time machine can write a row or a column; `V` has `a + b` inputs, the row first. -/
def gwInput (a b s : ℕ) (V : Circuit (a + b)) : List Bool :=
  List.replicate a true ++ false :: (List.replicate b true ++ false :: circuitCode (a + b) s V)

end KarpLiptonOM.Supplement


