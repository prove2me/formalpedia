-- Prove2me | Definitions.Def_FMMM_TSM_tsmRun
-- name    : FMMM_TSM_tsmRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:16:13.382775+00:00
-- url     : https://prove2.me/theorems/fc8c7b5b-7b36-481f-8314-3f79de6de144
-- title:
--   The online phase of the two suggested matchings algorithm
-- statement:
--   Let the blue and red edges of a TSM colouring be given, and let $\omega_0, \omega_1, \dots, \omega_{n-1}$ be the impression types that arrive, in order. The algorithm keeps, for every impression type $j$, the number $x_j$ of arrivals of type $j$ so far (initially $0$), and a set of assigned ads (initially empty). When an impression of type $j$ arrives:
--
--   1. if $x_j = 0$ and $j$ has a blue edge $(a', j)$, it tries $a'$;
--   2. if $x_j = 1$ and $j$ has a red edge $(a', j)$, it tries $a'$;
--   3. if $a'$ is not yet assigned, the impression is assigned to $a'$; otherwise, or if $x_j > 1$, nothing is assigned;
--   4. then $x_j$ increases by $1$.
--
--   The output is the set of assigned ads; its size is $\mathrm{ALG}$, the number of assigned impressions, since every assignment uses a new ad.
--
--   In words: the first time a type arrives it tries its blue edge, the second time its red edge, and later arrivals are discarded.
--
--   **Formalization Note** Under a TSM colouring every impression type has at most one blue and at most one red edge, so "the ad along $j$'s blue edge" is well defined; the Lean definition tries an ad only when the candidate set is a single ad. The improvement of footnote 7 (retrying the red edge when the blue one fails) is not part of the analysed algorithm.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.1, p. 7 (the TSM algorithm, counts x_i)

import Mathlib

namespace FMMM.TSM

/-- **The online phase of the two suggested matchings (TSM) algorithm.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.1, p. 7: "For each i ∈ I, the first time i arrives try the blue edge; the
second time i arrives try the red edge. More formally, for all i ∈ I maintain a count x_i of the
number of impressions i′ ∈ D(i) that have arrived so far. When i′ ∈ D(i) arrives: if x_i = 0, set
a′ to be the ad along i's blue edge (if i has a blue edge); if x_i = 1, set a′ to be the ad along
i's red edge (if i has a red edge). Now assign i to a′ if a′ is unassigned. If this a′ is already
assigned, or if x_i > 1, do not make an assignment."

`tsmRun blue red ω` processes the arrivals `ω 0, ω 1, …, ω (n−1)` in order with state (the counts
`x_j`, the set of assigned ads). On arrival of type `j`: if `x_j = 0` the candidate ads are those
`a` with `(a, j) ∈ blue`; if `x_j = 1`, those with `(a, j) ∈ red`; otherwise none. If there is
exactly one candidate `a′`, it is added to the assigned set (a no-op when `a′` is already
assigned). Then `x_j` is incremented. The result is the final set of assigned ads; `ALG` is its
cardinality, since every assignment uses a new ad.

**Formalization Note.** Under a TSM colouring every type has at most one blue and at most one red
edge, so "exactly one candidate" is "`j` has a blue (resp. red) edge". The improvement of
footnote 7 (retrying red after blue fails) is not part of the algorithm analysed. -/
def tsmRun {A J : Type} [DecidableEq A] [DecidableEq J] {n : ℕ}
    (blue red : Finset (A × J)) (ω : Fin n → J) : Finset A :=
  ((List.finRange n).foldl
    (fun (st : (J → ℕ) × Finset A) (t : Fin n) =>
      let j := ω t
      let cand : Finset A :=
        if st.1 j = 0 then (blue.filter (fun e => e.2 = j)).image Prod.fst
        else if st.1 j = 1 then (red.filter (fun e => e.2 = j)).image Prod.fst
        else ∅
      (Function.update st.1 j (st.1 j + 1), if cand.card = 1 then st.2 ∪ cand else st.2))
    (fun _ => 0, ∅)).2

end FMMM.TSM


