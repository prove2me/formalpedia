-- Prove2me | Definitions.Def_UniqueOptScores_HasUniqueMax
-- name    : UniqueOptScores_HasUniqueMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:05.167027+00:00
-- url     : https://prove2.me/theorems/0756bc5c-a39d-471c-9ee2-a8abab7dd7e6
-- title:
--   The predicate $U$: a unique maximizing candidate
-- statement:
--   $U$ holds for a family $(T_c)_{c\in C}$ and an oracle $O$ when **exactly one** candidate $c$ attains the maximum score: $\mathrm{eval}(T_c, O) = v$ for exactly one $c$.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 6, p.22 ("U(S) for the predicate that exactly one candidate attains it")

import Mathlib
import Definitions.Def_UniqueOptScores_QTree
import Definitions.Def_UniqueOptScores_maxScore

namespace UniqueOptScores

/-- **The predicate U: exactly one candidate attains the maximum.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §6, p.22: "U(S) for the predicate that exactly one candidate attains it". -/
def HasUniqueMax {ι α : Type*} [Fintype ι] (T : ι → QTree α ℕ) (O : α → Bool) : Prop :=
  ∃! c : ι, (T c).eval O = maxScore T O

end UniqueOptScores


