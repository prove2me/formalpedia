-- Prove2me | Definitions.Def_CNFEncComplexity_encAnramIn
-- name    : CNFEncComplexity_encAnramIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:28.197773+00:00
-- url     : https://prove2.me/theorems/bc3d6bc0-8345-48c6-af2e-fe98387033b1
-- title:
--   Input of the construction of Theorem 2
-- statement:
--   The construction of Theorem 2 receives $(\pi, n, t, b, A)$: $n$ and $t$ in unary, $b$ in binary, the advice string $A$ as its $m$ bits, and then the program $\pi$ (opcodes in unary, operands in binary), as words.
--
--   The input length is $n+t+m+O(\log b)$ plus the length of the program, so "time polynomial in $n+t+m$ given the advice string" becomes time polynomial in the input length.
--
--   **Formalization Note** The parameter $b$ is part of the hypothesis and must be given; in binary it costs $O(\log b)$ symbols. Operands longer than $t$ bits can never be executed within cost $t$.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614 (held version, sha256 97421ce1…), Theorem 2, p.2 (PDF 3)

import Mathlib
import Definitions.Def_CNFEncComplexity_Instr
import Definitions.Def_CNFEncComplexity_encWords

namespace CNFEncComplexity

/-- **Input of the construction of Theorem 2.** Krapivin, Przybocki, Subercaseaux, *The CNF Encoding Complexity of Boolean Functions*, arXiv:2611.05614 (held version, sha256 97421ce1…), Theorem 2, p.2 (PDF 3): "such an encoding can be
constructed deterministically in time polynomial in n + t + m given the advice string".

`encAnramIn (prog, n, t, b, A)` writes `n` and `t` in unary, `b` in binary, the advice string `A`
as its `m` bits, then the program (opcodes in unary, operands in binary), as words (`encWords`).

**Formalization Note.** The input length is `n + t + m + O(log b)` plus the length of the program, so
"polynomial in `n + t + m`" is read as polynomial in the input length (`b` is part of the
hypothesis and must be given; in binary it costs `O(log b)` symbols). Operands longer than `t` bits
can never be executed within cost `t`, as for `encRobsonIn`. -/
def encAnramIn (x : List Instr × ℕ × ℕ × ℕ × List Bool) : List (Fin 3) :=
  encWords ([unaryWord x.2.1, unaryWord x.2.2.1, binWord x.2.2.2.1, x.2.2.2.2] ++ progWords x.1)

end CNFEncComplexity


