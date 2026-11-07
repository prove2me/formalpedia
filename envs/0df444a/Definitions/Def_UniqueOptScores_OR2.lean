-- Prove2me | Definitions.Def_UniqueOptScores_OR2
-- name    : UniqueOptScores_OR2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:04.189245+00:00
-- url     : https://prove2.me/theorems/a50149db-93dc-40d0-9a20-8f9412d1c780
-- title:
--   Unions of two languages, $\mathrm{OR}_2(\mathcal C)$
-- statement:
--   For a class $\mathcal C$ of languages,
--   $$
--   \mathrm{OR}_2(\mathcal C) = \{L_1 \cup L_2 : L_1, L_2 \in \mathcal C\}.
--   $$
--   Membership in a language of $\mathrm{OR}_2(\mathrm{US}^A)$ is the disjunction of two exact-one tests on the same input.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 3.2, p.14

import Mathlib

namespace UniqueOptScores

/-- **Unions of two languages of a class.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §3.2, p.14: "For a class C of languages, we also write OR2(C) := {L1 ∪ L2 : L1, L2 ∈ C}." -/
def OR2 (C : Set (Set (List Bool))) : Set (Set (List Bool)) :=
  {L | ∃ L₁ ∈ C, ∃ L₂ ∈ C, L = L₁ ∪ L₂}

end UniqueOptScores


