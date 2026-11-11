-- Prove2me | Definitions.Def_CNFEncComplexity_encRobsonIn
-- name    : CNFEncComplexity_encRobsonIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:24.361206+00:00
-- url     : https://prove2.me/theorems/a63fdb1e-424a-4b09-ab50-bd75ef4e0631
-- title:
--   Input of the construction of Theorem 10
-- statement:
--   The construction of Theorem 10 receives the triple $(\pi, n, t)$: the number of input variables $n$ and the time bound $t$, both in unary, followed by the program $\pi$ (opcodes in unary, operands in binary), as words.
--
--   With $n$ and $t$ in unary, "time polynomial in $n+t$" becomes time polynomial in the input length.
--
--   **Formalization Note** The length of the program also counts. An operand longer than $t$ bits belongs to an instruction that can never run within cost $t$; its bits enter the input length only because the machine reads past them.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614 (held version, sha256 97421ce1…), Theorem 10, p.10 (PDF 11)

import Mathlib
import Definitions.Def_CNFEncComplexity_Instr
import Definitions.Def_CNFEncComplexity_encWords

namespace CNFEncComplexity

/-- **Input of the construction of Theorem 10.** Krapivin, Przybocki, Subercaseaux, *The CNF Encoding Complexity of Boolean Functions*, arXiv:2611.05614 (held version, sha256 97421ce1…), Theorem 10, p.10 (PDF 11): "such an encoding
can be constructed deterministically in time polynomial in n + t".

`encRobsonIn (prog, n, t)` writes `n` and `t` in unary, then the program (opcodes in unary, operands
in binary), as words (`encWords`).

**Formalization Note.** With `n` and `t` in unary, the input length is `n + t` plus the length of
the program, so "polynomial in `n + t`" is read as polynomial in the input length. An operand of more
than `t` bits belongs to an instruction that can never execute within cost `t`; its bits are counted
in the input length only because the machine has to read past them. -/
def encRobsonIn (x : List Instr × ℕ × ℕ) : List (Fin 3) :=
  encWords ([unaryWord x.2.1, unaryWord x.2.2] ++ progWords x.1)

end CNFEncComplexity


