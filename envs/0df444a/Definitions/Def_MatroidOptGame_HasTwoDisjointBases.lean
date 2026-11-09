-- Prove2me | Definitions.Def_MatroidOptGame_HasTwoDisjointBases
-- name    : MatroidOptGame_HasTwoDisjointBases
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:44.996071+00:00
-- url     : https://prove2.me/theorems/d1775d66-7f9f-46c7-9eb9-34d2c2b5c2de
-- title:
--   $M$ has two disjoint bases
-- statement:
--   A matroid $M$ **has two disjoint bases** if there are bases $B_1, B_2$ of $M$ with $B_1 \cap B_2 = \emptyset$.
--
--   This is the condition separating the case $\Delta(M, w) = \infty$ from the rest of the game (Lemma 2).
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 2 and Lemma 4, p.5

import Mathlib

namespace MatroidOptGame

/-- `M` has two disjoint bases.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Lemma 2 and Lemma 4, p.5 ("M does not have two disjoint bases",
"decide if M has two disjoint bases"). -/
def HasTwoDisjointBases {α : Type*} (M : Matroid α) : Prop :=
  ∃ B₁ B₂ : Finset α, M.IsBase (B₁ : Set α) ∧ M.IsBase (B₂ : Set α) ∧ Disjoint B₁ B₂

end MatroidOptGame


