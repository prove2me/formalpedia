-- Prove2me | Definitions.Def_LocalSearchFL_KMedian_captures
-- name    : LocalSearchFL_KMedian_captures
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:09:49.717567+00:00
-- url     : https://prove2.me/theorems/2dffed8e-a615-402d-ae31-8f7ca6cfeff0
-- title:
--   Definition 3.1 — a facility $s$ captures $o$; good and bad facilities
-- statement:
--   Let $\sigma_S$ and $\sigma_O$ assign every client to a facility of a solution $S$ and of a solution $O$ respectively, and write $N_S(s) = \{j : \sigma_S(j) = s\}$, $N_O(o) = \{j : \sigma_O(j) = o\}$ and
--   $$N^o_s = N_O(o) \cap N_S(s).$$
--
--   1. A facility $s$ **captures** a facility $o$ if $s$ serves more than half of the clients served by $o$:
--   $$|N^o_s| > \tfrac12 |N_O(o)|.$$
--   2. A facility $s \in S$ is **bad** if it captures some $o \in O$, and **good** otherwise.
--
--   Capture is the combinatorial device of the analysis of single-swap local search: it decides which facilities of $S$ can be swapped against which facilities of $O$.
--
--   **Formalization Note** The strict inequality is stated in integers as $|N_O(o)| < 2|N^o_s|$. Capture is defined for arbitrary assignments; in the paper $\sigma_S$ and $\sigma_O$ are nearest-facility assignments.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 549, Definition 3.1 and the definition of bad/good facilities that follows it

import Mathlib
import Definitions.Def_LocalSearchFL_KMedian_kmCost

namespace LocalSearchFL.KMedian

/-- **Capture** (Definition 3.1, p. 549). Given the assignment `σS` of the clients to the
facilities of a solution `S` and the assignment `σO` to those of a solution `O`, the facility
`s` captures `o` if `s` serves more than half of the clients served by `o`:
`|N^o_s| > ½ |N_O(o)|` with `N^o_s = N_O(o) ∩ N_S(s)`, stated in integers as
`|N_O(o)| < 2 |N^o_s|`. -/
def captures {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (s o : Fa) : Prop :=
  (nbhd σO o).card < 2 * (nbhd σO o ∩ nbhd σS s).card

/-- A facility `s` is **good** (p. 549) if it captures no facility of `O`, and bad otherwise. -/
def IsGood {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (O : Finset Fa) (s : Fa) : Prop :=
  ∀ o ∈ O, ¬ captures σS σO s o

end LocalSearchFL.KMedian


