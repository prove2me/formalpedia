-- Prove2me | Definitions.Def_UniqueOptScores_InPr
-- name    : UniqueOptScores_InPr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:22.708696+00:00
-- url     : https://prove2.me/theorems/6b575f93-fcc2-4bb8-8ed9-b73b5e336b06
-- title:
--   The occupancy promise $P_r$
-- statement:
--   A support $S$ satisfies the **occupancy promise** $P_r$ if $|S \cap X| \le r$ and $|S \cap Y| \le r$.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), Section 6, p.22 ("P_r = {S : |S ∩ X|, |S ∩ Y | ≤ r}")

import Mathlib

namespace UniqueOptScores

/-- **The occupancy promise P_r.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §6, p.22: "P_r = {S : |S ∩ X|, |S ∩ Y | ≤ r}". -/
def InPr {α : Type*} [DecidableEq α] (r : ℕ) (X Y S : Finset α) : Prop :=
  (S ∩ X).card ≤ r ∧ (S ∩ Y).card ≤ r

end UniqueOptScores


