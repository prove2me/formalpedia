-- Prove2me | Definitions.Def_Timetabling_StableHalf_stableHalf
-- name    : Timetabling_StableHalf_stableHalf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:31:04.506171+00:00
-- url     : https://prove2.me/theorems/a3665628-e077-4235-ae0c-57c286bb5004
-- title:
--   Limited backtracking for a stable set of $|X|/2$ nodes
-- statement:
--   Let $G = (X, E)$ be a graph whose node set $X = \{x_1, \bar x_1, \dots, x_n, \bar x_n\}$ carries the perfect matching $\{x_j, \bar x_j\}$, with adjacency given by an oracle. The **limited backtracking algorithm** starts from the assignment in which every pair is open and repeats, one tick per round:
--
--   1. find the lowest open pair $j$; if there is none, output the choice $c$ with $c_j = b$ for every assignment $a_j = b$;
--   2. otherwise examine the decision $x_j$ and its reverse $\bar x_j$ together ($\mathsf{trialPair}$); if both fail, stop and report that no stable set of $n$ nodes exists; otherwise continue from the permanent assignment.
--
--   This is the algorithm of the proof of Proposition 2.4 in the generality of the Remark: it decides whether $G$ has a stable set of $|X|/2 = n$ nodes and finds one.
--
--   **Formalization Note** The output is `Option (Fin n → Bool)`: a choice $c$, read as the stable set $\{(j, c_j)\}$, or `none`. Every round assigns at least one open pair, so the fuel $n+1$ is never exhausted. The graph is touched only through the oracle.
-- source:
--   de Werra (1985), proof of Proposition 2.4 and Remark, p. 155, "The idea is to use a limited backtracking method which runs as follows". D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_StableHalf_trialPair
import Definitions.Def_Timetabling_StableHalf_firstOpen

namespace Timetabling.StableHalf

/-- **The limited backtracking algorithm of the Remark.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), proof of Proposition 2.4 and Remark,
p. 155: "The idea is to use a limited backtracking method [...]", and "there is an O(n^2)
algorithm to determine whether for a graph G = (X, E) with a perfect matching, there is a stable
set of |X|/2 nodes."

The graph has node set `Fin n × Bool` and is given by the adjacency oracle `adj`; the perfect
matching is `{(j, true), (j, false)}`, `j : Fin n`. Starting from the assignment with every pair
open, the algorithm repeats (one tick per round):

1. find the lowest open pair `j` (`firstOpen`); if there is none, return the choice
   `c j = b` for `a j = some b`;
2. otherwise examine the decision `(j, true)` and its reverse `(j, false)` (`trialPair`); if
   both fail return `none`, else continue from the permanent assignment.

**Formalization Note.** The output is a choice `c : Fin n → Bool`, read as the stable set
`{(j, c j)}` of `n = |X|/2` nodes. Each round assigns at least one open pair, so `n + 1` rounds
suffice and the fuel `n + 1` is never exhausted. Adjacency is touched only through `adj`. -/
def stableHalf {n : ℕ} (adj : Fin n × Bool → Fin n × Bool → StateM ℕ Bool) :
    StateM ℕ (Option (Fin n → Bool)) :=
  loop (n + 1) (fun _ => none)
where
  /-- One decision round per unit of fuel. -/
  loop : ℕ → (Fin n → Option Bool) → StateM ℕ (Option (Fin n → Bool))
    | 0, _ => pure none
    | f + 1, a => do
      Cost.tick
      let j? ← firstOpen a
      match j? with
      | none => pure (some fun j => (a j).getD true)
      | some j => do
        let r ← trialPair adj a j
        match r with
        | none => pure none
        | some a' => loop f a'

end Timetabling.StableHalf


