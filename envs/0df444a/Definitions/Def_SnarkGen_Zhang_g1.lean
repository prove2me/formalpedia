-- Prove2me | Definitions.Def_SnarkGen_Zhang_g1
-- name    : SnarkGen_Zhang_g1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:30.936518+00:00
-- url     : https://prove2.me/theorems/e9eebd96-ce4d-472f-a86b-3590c7cc217a
-- title:
--   The first cyclically 5-edge-connected permutation snark on 34 vertices of Appendix 8.6
-- statement:
--   Appendix 8.6 of the paper, "Counterexamples to Conjectures 4.1, 5.17, 5.20 and 5.21. The 12 cyclically 5-edge connected permutation snarks on 34 vertices", lists twelve graphs. Each list is an adjacency list where only higher-numbered neighbours are listed: first the neighbours of vertex $1$, then the higher-numbered neighbours of vertex $2$, and so on. The first list is
--   $$
--   \{9, 11, 17, 6, 10, 25, 8, 12, 31, 8, 9, 16, 21, 26, 27, 16, 27, 11, 23, 33, 23, 10, 12, 14, 18, 19, 24, 29, 22, 34, 16, 17, 29, 20, 22, 32, 20, 26, 30, 22, 31, 24, 34, 26, 28, 28, 33, 30, 32, 32, 34\}.
--   $$
--   Since the graph is cubic, vertex $v$ receives $3$ minus the number of its already listed lower neighbours entries. Decoded this way, and with the paper's vertex $i$ renamed $i-1$, the graph $G_1$ has vertex set $\{0,1,\dots,33\}$ and the $51$ edges
--   $$
--   \begin{aligned}
--   &(0,8)\,(0,10)\,(0,16)\,(1,5)\,(1,9)\,(1,24)\,(2,7)\,(2,11)\,(2,30)\,(3,7)\,(3,8)\,(3,15)\,(4,20)\,(4,25)\,(4,26)\,(5,15)\,(5,26)\\
--   &(6,10)\,(6,22)\,(6,32)\,(7,22)\,(8,9)\,(9,11)\,(10,13)\,(11,17)\,(12,18)\,(12,23)\,(12,28)\,(13,21)\,(13,33)\,(14,15)\,(14,16)\,(14,28)\\
--   &(16,19)\,(17,21)\,(17,31)\,(18,19)\,(18,25)\,(19,29)\,(20,21)\,(20,30)\,(22,23)\,(23,33)\,(24,25)\,(24,27)\,(26,27)\,(27,32)\,(28,29)\,(29,31)\,(30,31)\,(32,33).
--   \end{aligned}
--   $$
--   The paper asserts that this graph is a cyclically $5$-edge-connected permutation snark, and hence a counterexample to Zhang's Conjecture 4.1.
--
--   **Formalization Note** Vertices are `Fin 34`, 0-based: the paper's vertex $i$ is `i - 1`. Adjacency is the symmetric closure of the explicit edge list `g1Edges` (`SimpleGraph.fromRel`), with decidable adjacency.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 36, Appendix 8.6, first list; p. 29, Appendices preamble (list format)

import Mathlib

namespace SnarkGen.Zhang

/-- The 51 edges of the first graph of Appendix 8.6 (arXiv:1206.6690v3, p. 36), decoded from
the printed list of higher-numbered neighbours; the paper's vertex `i` is `i - 1 : Fin 34`. -/
def g1Edges : List (Fin 34 × Fin 34) :=
  [(0, 8), (0, 10), (0, 16), (1, 5), (1, 9), (1, 24), (2, 7), (2, 11), (2, 30),
   (3, 7), (3, 8), (3, 15), (4, 20), (4, 25), (4, 26), (5, 15), (5, 26),
   (6, 10), (6, 22), (6, 32), (7, 22), (8, 9), (9, 11), (10, 13), (11, 17),
   (12, 18), (12, 23), (12, 28), (13, 21), (13, 33), (14, 15), (14, 16), (14, 28),
   (16, 19), (17, 21), (17, 31), (18, 19), (18, 25), (19, 29), (20, 21), (20, 30),
   (22, 23), (23, 33), (24, 25), (24, 27), (26, 27), (27, 32), (28, 29), (29, 31),
   (30, 31), (32, 33)]

/-- The graph `G₁` on 34 vertices: adjacency is the symmetric closure of `g1Edges`. -/
def g1 : SimpleGraph (Fin 34) :=
  SimpleGraph.fromRel fun u v => (u, v) ∈ g1Edges

instance : DecidableRel g1.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ ((u, v) ∈ g1Edges ∨ (v, u) ∈ g1Edges)))

end SnarkGen.Zhang


