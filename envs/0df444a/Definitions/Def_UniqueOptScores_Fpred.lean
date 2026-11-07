-- Prove2me | Definitions.Def_UniqueOptScores_Fpred
-- name    : UniqueOptScores_Fpred
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:24.619183+00:00
-- url     : https://prove2.me/theorems/158ff0a1-ca6f-4ae5-87fe-bec559573d5e
-- title:
--   The target predicate $F$ (exact-one OR)
-- statement:
--   For disjoint regions $X, Y$ and a support $S$,
--   $$
--   F(S) = \mathbf 1\big[\,|S \cap X| = 1 \ \lor\ |S \cap Y| = 1\,\big].
--   $$
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 6, p.22

import Mathlib

namespace UniqueOptScores

/-- **The target predicate F (exact-one OR).**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §6, p.22: "F(S) = 1[|S ∩ X| = 1 ∨ |S ∩ Y | = 1]". -/
def Fpred {α : Type*} [DecidableEq α] (X Y S : Finset α) : Prop :=
  (S ∩ X).card = 1 ∨ (S ∩ Y).card = 1

end UniqueOptScores


