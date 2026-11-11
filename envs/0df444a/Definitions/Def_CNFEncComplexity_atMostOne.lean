-- Prove2me | Definitions.Def_CNFEncComplexity_atMostOne
-- name    : CNFEncComplexity_atMostOne
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:44.886102+00:00
-- url     : https://prove2.me/theorems/409a951d-ef14-4165-9905-3a716e8b5ca2
-- title:
--   The function $\mathrm{AtMostOne}(x_1,\dots,x_n)$
-- statement:
--   $\mathrm{AtMostOne}(x_1,\dots,x_n)$ is the boolean function on $n$ variables that evaluates to $1$ if and only if at most one of $x_1,\dots,x_n$ is $1$:
--   $$\mathrm{AtMostOne}(x)=1 \iff |\{\,i : x_i=1\,\}|\le 1 .$$
--
--   It is the building block of the sparse-function encoding (Lemma 13), where it forces exactly one row of a table to be selected.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614 (held version, sha256 97421ce1…), §3.3, p.12 (PDF 13)

import Mathlib

namespace CNFEncComplexity

/-- **The function AtMostOne(x₁, …, xₙ).** Krapivin, Przybocki, Subercaseaux, *The CNF Encoding Complexity of Boolean Functions*, arXiv:2611.05614 (held version, sha256 97421ce1…), §3.3, p.12 (PDF 13): "the function
AtMostOne(x₁, . . . , xₙ), which evaluates to 1 if and only if at most one of the variables
x₁, . . . , xₙ is 1." -/
def atMostOne (n : ℕ) : (Fin n → Bool) → Bool :=
  fun x => decide ((Finset.univ.filter fun i => x i = true).card ≤ 1)

end CNFEncComplexity


