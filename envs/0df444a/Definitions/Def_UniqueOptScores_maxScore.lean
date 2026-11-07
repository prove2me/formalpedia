-- Prove2me | Definitions.Def_UniqueOptScores_maxScore
-- name    : UniqueOptScores_maxScore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:26:08.85717+00:00
-- url     : https://prove2.me/theorems/16efb38e-c5a6-4544-a899-931437714dc6
-- title:
--   The maximum score $v$
-- statement:
--   For a finite family of candidate evaluations $(T_c)_{c \in C}$ with natural-number scores and an oracle $O$, the **maximum score** is $v = \max_{c \in C} \mathrm{eval}(T_c, O)$. For a support $S$ this is the paper's $v(S)$, computed with the oracle $O_S$.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 6, p.22 ("Write v(S) for the maximum score")

import Mathlib
import Definitions.Def_UniqueOptScores_QTree

namespace UniqueOptScores

/-- **The maximum score v.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §6, p.22: "Write v(S) for the maximum score".

For a finite family of candidate evaluations `T : ι → QTree α ℕ` and an oracle `O`, `maxScore T O`
is the largest score `max_c eval (T c) O` (and `0` for an empty family). -/
def maxScore {ι α : Type*} [Fintype ι] (T : ι → QTree α ℕ) (O : α → Bool) : ℕ :=
  Finset.univ.sup fun c => (T c).eval O

end UniqueOptScores


