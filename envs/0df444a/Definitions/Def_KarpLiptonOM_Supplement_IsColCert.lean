-- Prove2me | Definitions.Def_KarpLiptonOM_Supplement_IsColCert
-- name    : KarpLiptonOM_Supplement_IsColCert
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:41:31.437192+00:00
-- url     : https://prove2.me/theorems/7e55e0d0-4c8c-45f1-b910-92899f6e63db
-- title:
--   Column-side collectively irrefutable certificate for the matrix of a circuit
-- statement:
--   Let $V:\{0,1\}^a\times\{0,1\}^b\to\{0,1\}$ be a circuit, read as a Boolean matrix with rows $y\in\{0,1\}^a$ and columns $z\in\{0,1\}^b$. Column $z$ **beats** row $y$ if $V(y,z)=0$. A set $T$ of columns is a **column-side collectively irrefutable certificate** if every row is beaten by some column of $T$:
--
--   $$
--   T\subseteq\{0,1\}^b\quad\text{and}\quad\forall y\in\{0,1\}^a\;\exists z\in T\;\; V(y,z)=0 .
--   $$
--
--   **Formalization Note** $V$ is a circuit with $a+b$ inputs and $V(y,z)$ is its value on $yz$; the set $T$ is given as a list.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.5 ("Matrices [CR11, Def. 4.6]"), p.32

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit_eval

namespace KarpLiptonOM.Supplement

/-- A **column-side collectively irrefutable certificate** for the matrix of a circuit
`V : {0,1}^a × {0,1}^b → {0,1}` (§A.5, "Matrices [CR11, Def. 4.6]", Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), p.32): a set `T` of columns
such that every row is beaten by some `z ∈ T`, where column `z` beats row `y` iff `V(y, z) = 0`.

**Formalization Note** `V(y, z) = V.eval (y ++ z)` for a circuit with `a + b` inputs. Columns are
strings of length exactly `b`; "every row" ranges over all `y ∈ {0,1}^a`. The set `T` is a list. -/
def IsColCert (a b : ℕ) (V : Circuit (a + b)) (T : List (List Bool)) : Prop :=
  (∀ z ∈ T, z.length = b) ∧
    ∀ y : List Bool, y.length = a → ∃ z ∈ T, V.eval (y ++ z) = false

end KarpLiptonOM.Supplement


