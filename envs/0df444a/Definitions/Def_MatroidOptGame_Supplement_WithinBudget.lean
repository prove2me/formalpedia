-- Prove2me | Definitions.Def_MatroidOptGame_Supplement_WithinBudget
-- name    : MatroidOptGame_Supplement_WithinBudget
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:51:44.879809+00:00
-- url     : https://prove2.me/theorems/7791d1e2-ac99-477d-82f8-2abf166bf948
-- title:
--   Total query budget $s$ of an oracle player
-- statement:
--   An oracle player respects the **query budget** $s$ if it asks at most $s$ queries in the whole game: as soon as its transcript holds $s$ queries, it moves instead of querying. The transcript persists over the game, so queries made before the first move and between moves all count towards $s$.
--
--   **Formalization Note** The condition is imposed on every input (history, transcript); a player that respects the budget along play can be changed elsewhere without changing any play.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2, Theorem 11, p.13; Theorem 14, p.15

import Mathlib
import Definitions.Def_MatroidOptGame_Supplement_OraclePlayer

namespace MatroidOptGame.Supplement

/-- The oracle player `P` asks at most `s` queries over the whole game: once its transcript holds
`s` queries, it moves instead of querying.
Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2, Theorem 11, p.13 ("can generate queries F̃₁, …, F̃ₛ to Õ") and Theorem 14,
p.15 ("can generate at most s independence queries").
**Formalization Note.** The transcript persists over the whole game and only grows, so this is a
bound on the total number of queries, before the first move and between moves alike. The
condition is imposed on every input; a player respecting the budget on the inputs that occur in
play can be changed elsewhere without changing any play. -/
def WithinBudget {α : Type*} (s : ℕ) (P : OraclePlayer α) : Prop :=
  ∀ (h : List α) (tr : List (Finset α × ℤ)), s ≤ tr.length → ∃ e, P h tr = .move e

end MatroidOptGame.Supplement


