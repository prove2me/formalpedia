-- Prove2me | Definitions.Def_UniqueOptScores_Psi
-- name    : UniqueOptScores_Psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:21.152958+00:00
-- url     : https://prove2.me/theorems/9c62bf1a-68e7-465d-8144-99ae4d3ba7eb
-- title:
--   The predicate $\Psi_r$
-- statement:
--   For $r \ge 1$ and occupancies $a, b \ge 0$,
--   $$
--   \Psi_r(a, b) = [a = 1] \lor \big([a \le r] \land [b = 1]\big).
--   $$
--   It agrees with exact-one OR $[a = 1 \lor b = 1]$ whenever $a \le r$, and is the total predicate computed by the construction of Lemma 2.2.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Lemma 2.2 (restated), eq. (4), p.25

import Mathlib

namespace UniqueOptScores

/-- **The predicate Ψ_r of Lemma 2.2.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), Lemma 2.2 (restated), eq. (4), p.25: "Ψ_r(a, b) = [a = 1] ∨ ([a ≤ r] ∧ [b = 1])". -/
def Psi (r a b : ℕ) : Prop :=
  a = 1 ∨ (a ≤ r ∧ b = 1)

end UniqueOptScores


