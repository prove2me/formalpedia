-- Prove2me | Definitions.Def_KarpLiptonOM_Supplement_IsRowCert
-- name    : KarpLiptonOM_Supplement_IsRowCert
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:41:07.491001+00:00
-- url     : https://prove2.me/theorems/c98f8695-45cc-47da-a9b3-e106a1a558f6
-- title:
--   Row-side collectively irrefutable certificate for the matrix of a circuit
-- statement:
--   Let $V:\{0,1\}^a\times\{0,1\}^b\to\{0,1\}$ be a circuit, read as a Boolean matrix with rows $y\in\{0,1\}^a$ and columns $z\in\{0,1\}^b$. Row $y$ **beats** column $z$ if $V(y,z)=1$. A set $R$ of rows is a **row-side collectively irrefutable certificate** if every column is beaten by some row of $R$:
--
--   $$
--   R\subseteq\{0,1\}^a\quad\text{and}\quad\forall z\in\{0,1\}^b\;\exists y\in R\;\; V(y,z)=1 .
--   $$
--
--   This is the notion of Goldreich–Wigderson and Chakaravarthy–Roy used in the paper's Theorem A.5.2.
--
--   **Formalization Note** $V$ is a circuit with $a+b$ inputs and $V(y,z)$ is its value on the concatenation $yz$; the set $R$ is given as a list.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.5 ("Matrices [CR11, Def. 4.6]"), p.32

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit_eval

namespace KarpLiptonOM.Supplement

/-- A **row-side collectively irrefutable certificate** for the matrix of a circuit
`V : {0,1}^a × {0,1}^b → {0,1}` (§A.5, "Matrices [CR11, Def. 4.6]", Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.32): a set `R` of rows
such that every column is beaten by some `y ∈ R`, where row `y` beats column `z` iff `V(y, z) = 1`.

**Formalization Note** `V` is a circuit with `a + b` inputs and `V(y, z) = V.eval (y ++ z)`. Rows are
strings of length exactly `a`, columns strings of length exactly `b`; "every column" ranges over all
`z ∈ {0,1}^b`. The set `R` is given as a list. -/
def IsRowCert (a b : ℕ) (V : Circuit (a + b)) (R : List (List Bool)) : Prop :=
  (∀ y ∈ R, y.length = a) ∧
    ∀ z : List Bool, z.length = b → ∃ y ∈ R, V.eval (y ++ z) = true

end KarpLiptonOM.Supplement


