-- Prove2me | Definitions.Def_EvasivePatterns_occurs
-- name    : EvasivePatterns_occurs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:09.560781+00:00
-- url     : https://prove2.me/theorems/a6f3815d-a10a-4c98-bd00-2c2ad80e1340
-- title:
--   Occurrence of a binary pattern $P$ in a text $X\in\{0,1\}^n$
-- statement:
--   Let $P \in \{0,1\}^m$ be a pattern and $X \in \{0,1\}^n$ a text. The pattern **occurs** in $X$ when it appears as a contiguous block,
--   $$
--   X_{i+1} X_{i+2} \cdots X_{i+m} = P \qquad\text{for some } 0 \le i \le n-m .
--   $$
--   The Boolean function $f_{P,n}(X)$ of the paper is $1$ exactly when $P$ occurs in $X$; deciding its value is the task whose query complexity the mission studies.
--
--   **Formalization Note** Bits are `Bool` ($0 \mapsto$ `false`, $1 \mapsto$ `true`), the pattern is a list and the text a function on the positions $0,\dots,n-1$. Occurrence is the infix relation of lists, which is decidable. The empty pattern occurs in every text.
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), §1, p.1 (PDF p.2), lines 3–7; §2, p.4 (PDF p.5), line 110 (f_{P,n})

import Mathlib

namespace EvasivePatterns

/-- **Occurrence of a binary pattern in a text.** The pattern `P ∈ {0,1}^m` occurs in the text
`X ∈ {0,1}^n` when `P` is a contiguous factor of `X`: `X_{i+1} ⋯ X_{i+m} = P` for some
`0 ≤ i ≤ n − m`. The Boolean function `f_{P,n}(X)` of the paper is one exactly when this holds.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), §1, printed p. 1 (PDF p. 2), lines 3–7 ("whether a given word
occurs"), and §2, printed p. 4 (PDF p. 5), line 110: "Let f_{P,n}(X) be the Boolean function which is
one exactly when P occurs in X ∈ {0, 1}^n".

**Formalization Note** Binary symbols are `Bool` (`0 ↦ false`, `1 ↦ true`). The pattern is a
`List Bool`; the text is a function `Fin n → Bool` (positions `0, …, n − 1`), turned into a list by
`List.ofFn`. Occurrence is `List.IsInfix` (`P <:+: X`, i.e. `X = s ++ P ++ t` for some lists
`s`, `t`), which is decidable. The empty pattern occurs in every text. -/
def occurs (P : List Bool) {n : ℕ} (X : Fin n → Bool) : Prop :=
  P <:+: List.ofFn X

instance (P : List Bool) {n : ℕ} (X : Fin n → Bool) : Decidable (occurs P X) :=
  inferInstanceAs (Decidable (P <:+: List.ofFn X))

end EvasivePatterns


