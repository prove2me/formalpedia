-- Prove2me | Definitions.Def_MatroidOptGame_HasTwoDisjointMinBases
-- name    : MatroidOptGame_HasTwoDisjointMinBases
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:52:50.518579+00:00
-- url     : https://prove2.me/theorems/4c9b36be-72ae-4dfb-aa34-15275e3394aa
-- title:
--   $M$ has two disjoint minimum-weight bases
-- statement:
--   A matroid $M$ with weights $w$ **has two disjoint minimum-weight bases** if there are minimum-weight bases $B_1, B_2$ of $M$ (with respect to $w$) with $B_1 \cap B_2 = \emptyset$.
--
--   This is the condition of Lemma 5, under which MIN can hold MAX's excess payoff to $0$.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 5, p.6

import Mathlib
import Definitions.Def_MatroidOptGame_IsMinWeightBase

namespace MatroidOptGame

/-- `M` has two disjoint minimum-weight bases with respect to `w`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 5, p.6 ("It can be decided efficiently if M has two disjoint minimum
weight bases"). -/
def HasTwoDisjointMinBases {α : Type*} (M : Matroid α) (w : α → ℕ) : Prop :=
  ∃ B₁ B₂ : Finset α, IsMinWeightBase M w B₁ ∧ IsMinWeightBase M w B₂ ∧ Disjoint B₁ B₂

end MatroidOptGame


