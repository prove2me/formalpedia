-- Prove2me | Definitions.Def_UniqueOptScores_supportOracle
-- name    : UniqueOptScores_supportOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:22.660957+00:00
-- url     : https://prove2.me/theorems/1e96636a-b709-4b30-9af0-162f80a29e4d
-- title:
--   The oracle of a support $S \subseteq X \cup Y$
-- statement:
--   Let $X, Y$ be finite sets of points and fix oracle answers $e(a)$ outside $X \cup Y$. A **support** $S \subseteq X \cup Y$ specifies the present points; its oracle answers
--   $$
--   O_S(a) = \begin{cases} [a \in S] & a \in X \cup Y,\\ e(a) & \text{otherwise.}\end{cases}
--   $$
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 6, p.22 ("fix arbitrary oracle answers outside X ∪ Y. For S ⊆ X ∪ Y")

import Mathlib

namespace UniqueOptScores

/-- **The oracle of a support.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §6, p.22: "Let X, Y be disjoint sets of size N, and fix arbitrary oracle answers outside
X ∪ Y. For S ⊆ X ∪ Y …"

For finite regions `X, Y`, exterior answers `e` and a support `S`, the oracle answers `a ∈ S` for
points `a ∈ X ∪ Y` and `e a` elsewhere. -/
def supportOracle {α : Type*} [DecidableEq α] (X Y : Finset α) (e : α → Bool) (S : Finset α)
    (a : α) : Bool :=
  if a ∈ X ∪ Y then decide (a ∈ S) else e a

end UniqueOptScores


