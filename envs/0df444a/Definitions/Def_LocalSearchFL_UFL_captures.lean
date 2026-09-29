-- Prove2me | Definitions.Def_LocalSearchFL_UFL_captures
-- name    : LocalSearchFL_UFL_captures
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:14:43.123097+00:00
-- url     : https://prove2.me/theorems/0d1001b9-4461-41ed-bded-7ee5fe62f611
-- title:
--   Capture (Definition 3.1), good facilities, and the refined mapping π of the proof of Lemma 4.2
-- statement:
--   Let $S$ and $O$ be two solutions with nearest-facility assignments $\sigma_S$ and $\sigma_O$, so that $N_S(s)$ and $N_O(o)$ are the sets of clients served by $s$ and by $o$, and let $N^o_s = N_O(o) \cap N_S(s)$.
--
--   1. **Capture** (Definition 3.1). A facility $s \in S$ captures $o \in O$ if $s$ serves more than half of the clients served by $o$:
--   $$|N^o_s| > \tfrac12 |N_O(o)|.$$
--   2. **Good and bad facilities.** $s \in S$ is *good* if it captures no $o \in O$, and *bad* otherwise.
--   3. **The mapping $\pi$.** A permutation $\pi$ of the clients is *admissible* for the proof of Lemma 4.2 if
--      1. it maps every $N_O(o)$ onto itself, i.e. it is a 1-1 and onto map of each $N_O(o)$;
--      2. (Property 3.1) if $s$ does not capture $o$, then $\pi(N^o_s) \cap N^o_s = \emptyset$;
--      3. if $s$ captures $o$, then every $j \in N^o_s$ with $\pi(j) \in N^o_s$ satisfies $\pi(j) = j$.
--
--   Capture and Property 3.1 are the combinatorial tools of §3.2 of the paper; the third condition is the refinement introduced at the start of the proof of Lemma 4.2.
--
--   **Formalization Note** Capture is stated in natural numbers as $|N_O(o)| < 2|N^o_s|$. The family of bijections of the sets $N_O(o)$ is encoded as one permutation of all clients preserving $\sigma_O$; since every client lies in exactly one $N_O(o)$, the two are equivalent.
-- source:
--   Arya, Garg, Khandekar, Meyerson, Munagala, Pandit, Local Search Heuristics for k-Median and Facility Location Problems, SIAM J. Comput. 33(3), 2004, p. 549, Definition 3.1 and Property 3.1; p. 555, proof of Lemma 4.2 (first paragraph) and the definition of good facilities

import Mathlib
import Definitions.Def_LocalSearchFL_UFL_uflCost

namespace LocalSearchFL.UFL

/-- **Capture** (Definition 3.1, p. 549). Given the assignment `σS` of the clients to the
facilities of a solution `S` and the assignment `σO` to those of a solution `O`, the facility
`s` captures `o` if `s` serves more than half of the clients served by `o`:
`|N^o_s| > ½ |N_O(o)|` with `N^o_s = N_O(o) ∩ N_S(s)`, stated in integers as
`|N_O(o)| < 2 |N^o_s|`. -/
def captures {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (s o : Fa) : Prop :=
  (nbhd σO o).card < 2 * (nbhd σO o ∩ nbhd σS s).card

instance {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (s o : Fa) : Decidable (captures σS σO s o) := by
  unfold captures; infer_instance

/-- A facility `s` is **good** (p. 549, recalled on p. 555) if it captures no facility of `O`,
and bad otherwise. -/
def IsGood {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (O : Finset Fa) (s : Fa) : Prop :=
  ∀ o ∈ O, ¬ captures σS σO s o

/-- The **mapping π of the proof of Lemma 4.2** (p. 555), as one permutation of all clients:
(i) `π` maps every `N_O(o)` onto itself (`σO (π j) = σO j`), i.e. it is a bijection of each
`N_O(o)`; (ii) Property 3.1 (p. 549): if `s` does not capture `o`, then `π(N^o_s) ∩ N^o_s = ∅`;
(iii) the refinement of p. 555: if `s` captures `o`, then every `j ∈ N^o_s` with `π(j) ∈ N^o_s`
satisfies `π(j) = j`. -/
def IsRefinedPi {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] [DecidableEq Fa]
    (σS σO : Cl → Fa) (π : Equiv.Perm Cl) : Prop :=
  (∀ j, σO (π j) = σO j) ∧
  (∀ s o : Fa, ¬ captures σS σO s o →
    ∀ j ∈ nbhd σO o ∩ nbhd σS s, π j ∉ nbhd σO o ∩ nbhd σS s) ∧
  (∀ s o : Fa, captures σS σO s o →
    ∀ j ∈ nbhd σO o ∩ nbhd σS s, π j ∈ nbhd σO o ∩ nbhd σS s → π j = j)

end LocalSearchFL.UFL


