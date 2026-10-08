-- Prove2me | Definitions.Def_SnarkGen_Zhang_petersen
-- name    : SnarkGen_Zhang_petersen
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:04:33.228018+00:00
-- url     : https://prove2.me/theorems/6d862095-f313-4b4c-8f78-1e692c05ccb7
-- title:
--   The Petersen graph
-- statement:
--   The **Petersen graph** $P$ is the graph on the ten vertices $0,1,\dots,9$ with the $15$ edges
--
--   1. the outer $5$-cycle: $i \sim i+1 \pmod 5$ for $i = 0,\dots,4$;
--   2. the spokes: $i \sim i+5$ for $i = 0,\dots,4$;
--   3. the inner pentagram: $5+i \sim 5+\big((i+2) \bmod 5\big)$ for $i = 0,\dots,4$.
--
--   Explicitly the edge list is
--   $$
--   01,\ 12,\ 23,\ 34,\ 40,\ 05,\ 16,\ 27,\ 38,\ 49,\ 57,\ 68,\ 79,\ 85,\ 96.
--   $$
--   Up to isomorphism this is the Kneser graph $K(5,2)$: the vertices are the $2$-element subsets of a $5$-element set, adjacent when disjoint. The paper does not define the Petersen graph; this is the standard one.
--
--   The Petersen graph is the smallest snark and, as recalled in the paper, a permutation snark. Zhang conjectured that it is the only cyclically $5$-edge-connected permutation snark.
--
--   **Formalization Note** The graph lives on `Fin 10` and its adjacency is the symmetric closure of the explicit edge list (`SimpleGraph.fromRel`), with decidable adjacency so that finite checks about it can be computed.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 9, Section 4.2 (the Petersen graph, used without definition; standard)

import Mathlib

namespace SnarkGen.Zhang

/-- The 15 edges of the Petersen graph on `Fin 10`: the outer 5-cycle `i ~ i+1 (mod 5)`,
the spokes `i ~ i+5`, and the inner pentagram `5+i ~ 5+((i+2) mod 5)`. -/
def petersenEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
   (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
   (5, 7), (6, 8), (7, 9), (8, 5), (9, 6)]

/-- The Petersen graph: adjacency is the symmetric closure of `petersenEdges`. -/
def petersen : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel fun u v => (u, v) ∈ petersenEdges

instance : DecidableRel petersen.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ ((u, v) ∈ petersenEdges ∨ (v, u) ∈ petersenEdges)))

end SnarkGen.Zhang


