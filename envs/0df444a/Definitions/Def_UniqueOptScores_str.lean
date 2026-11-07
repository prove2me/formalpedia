-- Prove2me | Definitions.Def_UniqueOptScores_str
-- name    : UniqueOptScores_str
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:05.01182+00:00
-- url     : https://prove2.me/theorems/f27b5dc3-8b4c-44b8-81f5-d8a69be6c9bb
-- title:
--   Length-lexicographic enumeration of binary strings
-- statement:
--   The binary strings are enumerated in **length-lexicographic order** $w_0 = \varepsilon, w_1 = 0, w_2 = 1, w_3 = 00, w_4 = 01, \dots$: $w_n$ is the binary expansion of $n + 1$ with its leading $1$ removed. This identifies an oracle $A \subseteq \{0,1\}^*$ with the binary sequence $(\mathbf 1[w_n \in A])_{n \ge 0}$, as in the paper's treatment of oracle Cantor space and of Turing degrees.
--
--   **Formalization Note** `Nat.bits` lists bits least significant first with the leading one last; `dropLast` removes it and `reverse` puts the most significant bit first.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 8, p.30 ("Identify oracle bits with a binary sequence in length-lexicographic order"); Appendix C, p.35

import Mathlib

namespace UniqueOptScores

/-- **The length-lexicographic enumeration of binary strings.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §8, p.30: "Identify oracle bits with a binary sequence in length-lexicographic order";
App. C, p.35: "Let (wj)j≥0 enumerate all binary strings in length-lexicographic order."

`str n` is the binary expansion of `n + 1` with its leading `1` removed (most significant bit
first): `str 0 = ε`, `str 1 = 0`, `str 2 = 1`, `str 3 = 00`, `str 4 = 01`, ….

**Formalization Note.** `Nat.bits` lists the bits least significant first, with the leading `1`
last; `dropLast` removes it and `reverse` puts the most significant bit first. -/
def str (n : ℕ) : List Bool :=
  ((Nat.bits (n + 1)).dropLast).reverse

end UniqueOptScores


