-- Prove2me | Definitions.Def_WhitneyMatroid_Fano_IsFano
-- name    : WhitneyMatroid_Fano_IsFano
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:28:58.054483+00:00
-- url     : https://prove2.me/theorems/67d61443-76a6-47cf-bf37-2715864c5185
-- title:
--   The seven-element matroid $M'$ of §16 (16.1)
-- statement:
--   Whitney's matroid $M'$ of §16 has seven elements, named $1,\dots,7$. Its bases are all sets of three elements except the seven sets
--
--   $$
--   124,\quad 135,\quad 167,\quad 236,\quad 257,\quad 347,\quad 456 \qquad (16.1).
--   $$
--
--   A matroid $M$ on $\{1,\dots,7\}$ **is the matroid $M'$** if every element belongs to $M$ and a set $B$ is a base of $M$ exactly when $B$ has three elements and is not one of the sets (16.1). The seven sets (16.1) are the lines of the projective plane of order two (the Fano plane); $M'$ is now called the Fano matroid.
--
--   **Formalization Note** The elements are `Fin 7`, Whitney's element $k$ being `k - 1`. After this shift the sets (16.1) are $\{0,1,3\},\{0,2,4\},\{0,5,6\},\{1,2,5\},\{1,4,6\},\{2,3,6\},\{3,4,5\}$. Existence of a matroid with these bases is not part of the definition; it is the first half of the mission's goal theorem.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 529, §16, (16.1)

import Mathlib

namespace WhitneyMatroid.Fano

/-- Whitney §16, (16.1) (p. 529): the seven exceptional triples
`124, 135, 167, 236, 257, 347, 456`. Whitney's element `k ∈ {1, …, 7}` is `k - 1 : Fin 7`, so the
triples read `{0,1,3}, {0,2,4}, {0,5,6}, {1,2,5}, {1,4,6}, {2,3,6}, {3,4,5}`. -/
def fanoLines : Set (Set (Fin 7)) :=
  {{0, 1, 3}, {0, 2, 4}, {0, 5, 6}, {1, 2, 5}, {1, 4, 6}, {2, 3, 6}, {3, 4, 5}}

/-- Whitney §16 (p. 529): `M` is the matroid `M′` of §16. It has the seven elements `1, …, 7`
(here `Fin 7`, the whole type being the ground set), and its bases are all sets of three elements
except the seven sets of (16.1). -/
def IsFano (M : Matroid (Fin 7)) : Prop :=
  M.E = Set.univ ∧ ∀ B : Set (Fin 7), M.IsBase B ↔ (B.ncard = 3 ∧ B ∉ fanoLines)

end WhitneyMatroid.Fano


