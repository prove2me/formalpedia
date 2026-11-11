-- Prove2me | Definitions.Def_CNFEncComplexity_encMassIn
-- name    : CNFEncComplexity_encMassIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:23.849865+00:00
-- url     : https://prove2.me/theorems/23095e4c-94d2-4f71-9850-5497b1984a62
-- title:
--   Input of the construction of Lemma 11, and truth tables
-- statement:
--   The **truth table** of $f:\{0,1\}^n\to\{0,1\}$ is the bit string of length $2^n$ whose entry $v$ is $f$ evaluated at the binary expansion of $v$, with $x_1$ the most significant bit. The construction of Lemma 11 receives $n$ in unary, the truth table of $f$, and $b$ in unary, as words.
--
--   The input length is $n+2^n+b+4$, so time polynomial in the input length is time polynomial in $2^n$ and $b$.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614 (held version, sha256 97421ce1…), Lemma 11, p.11 (PDF 12)

import Mathlib
import Definitions.Def_CNFEncComplexity_encWords

namespace CNFEncComplexity

/-- The truth table of `f : {0,1}ⁿ → {0,1}`: entry `v < 2ⁿ` is `f` at the binary expansion of `v`,
with `x₁` (index `0`) the most significant bit. -/
def truthTable {n : ℕ} (f : (Fin n → Bool) → Bool) : List Bool :=
  List.ofFn fun v : Fin (2 ^ n) => f fun i => v.val.testBit (n - 1 - i)

/-- **Input of the construction of Lemma 11.** Krapivin, Przybocki, Subercaseaux, *The CNF Encoding Complexity of Boolean Functions*, arXiv:2611.05614 (held version, sha256 97421ce1…), Lemma 11, p.11 (PDF 12): "such an encoding can be
obtained deterministically in time polynomial in 2ⁿ and b".

`encMassIn (n, T, b)` writes `n` in unary, the truth table `T` (`2ⁿ` bits, `truthTable`) and `b`
in unary, as words.

**Formalization Note.** The input length is `n + 2ⁿ + b + 4`, so polynomial in the input length is
polynomial in `2ⁿ` and `b`. -/
def encMassIn (x : ℕ × List Bool × ℕ) : List (Fin 3) :=
  encWords [unaryWord x.1, x.2.1, unaryWord x.2.2]

end CNFEncComplexity


