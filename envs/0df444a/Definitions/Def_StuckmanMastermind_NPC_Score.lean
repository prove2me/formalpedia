-- Prove2me | Definitions.Def_StuckmanMastermind_NPC_Score
-- name    : StuckmanMastermind_NPC_Score
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-31T00:51:19.174936+00:00
-- url     : https://prove2.me/theorems/7f53cc62-4e8c-445f-ac29-8e6b7444a5af
-- title:
--   Mastermind codes and black/white scores
-- statement:
--   A code is a length ℓ tuple over κ colors, with repetitions permitted. Black counts equal coordinates. A color's multiplicity is its coordinate count; totalMatches sums the minimum of the two multiplicities over all colors. The score is (black, totalMatches minus black). Zero-based positions and colors correspond to source indices plus one. This uses the intended coordinate counts in Definition 2.1, whose printed existential variable shadows the counted index (insight I2). The white component is nonnegative because, color by color, equal-coordinate matches are at most each multiplicity. Empty codes have score (0,0).
-- source:
--   Stuckman and Zhang, arXiv:cs/0512049v1, Definition 2.1, PDF p. 2 and explanation p. 3; https://arxiv.org/abs/cs/0512049v1

import Mathlib

namespace StuckmanMastermind.NPC

abbrev Code (κ ℓ : ℕ) := Fin ℓ → Fin κ

def black {κ ℓ : ℕ} (x y : Code κ ℓ) : ℕ :=
  (Finset.univ.filter fun i => x i = y i).card

def multiplicity {κ ℓ : ℕ} (x : Code κ ℓ) (j : Fin κ) : ℕ :=
  (Finset.univ.filter fun i => x i = j).card

def totalMatches {κ ℓ : ℕ} (x y : Code κ ℓ) : ℕ :=
  ∑ j : Fin κ, min (multiplicity x j) (multiplicity y j)

def score {κ ℓ : ℕ} (x y : Code κ ℓ) : ℕ × ℕ :=
  (black x y, totalMatches x y - black x y)

end StuckmanMastermind.NPC


