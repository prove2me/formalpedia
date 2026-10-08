-- Prove2me | Definitions.Def_SnarkGen_OddFactors_G81
-- name    : SnarkGen_OddFactors_G81
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:02:53.28217+00:00
-- url     : https://prove2.me/theorems/bc20bd67-075e-4857-806a-b8f477b48e39
-- title:
--   The 26-vertex graph $G_{8.1}$ of Appendix 8.1
-- statement:
--   The graph $G_{8.1}$ is the graph printed in Appendix 8.1 of the paper (p. 29), "A cubic graph where all 2-factors only consist of odd cycles". The appendices give a graph by listing, for the vertices $1, 2, \dots, n$ in turn, only their higher-numbered neighbours. For $G_{8.1}$ ($n = 26$) the list is
--   $$\{2, 3, 4, 5, 6, 7, 8, 9, 10, 7, 9, 8, 10, 11, 12, 13, 14, 15, 16, 15, 17, 18, 19, 18, 20, 18, 21, 22, 21, 23, 23, 24, 22, 24, 25, 26, 26, 25, 26\}.$$
--   Giving each vertex, in turn, as many entries as it still lacks neighbours (three minus the number of lower neighbours already assigned) decodes the list into 39 edges. In the paper's numbering $1, \dots, 26$ they are
--
--   $\{1,2\}, \{1,3\}, \{1,4\}, \{2,5\}, \{2,6\}, \{3,7\}, \{3,8\}, \{4,9\}, \{4,10\}, \{5,7\}, \{5,9\}, \{6,8\}, \{6,10\}, \{7,11\}, \{8,12\}, \{9,13\}, \{10,14\}, \{11,15\}, \{11,16\}, \{12,15\}, \{12,17\}, \{13,18\}, \{13,19\}, \{14,18\}, \{14,20\}, \{15,18\}, \{16,21\}, \{16,22\}, \{17,21\}, \{17,23\}, \{19,23\}, \{19,24\}, \{20,22\}, \{20,24\}, \{21,25\}, \{22,26\}, \{23,26\}, \{24,25\}, \{25,26\}$.
--
--   This is the graph that witnesses the refutation of Conjecture 4.11 (Observation 4.12).
--
--   **Formalization Note** The vertex type is `Fin 26`, with paper vertex $i$ represented by $i-1$, so the Lean list `G81Edges` is the list above with every label decreased by one. Adjacency is the symmetric closure of `G81Edges`, so it is decidable.
-- source:
--   G. Brinkmann, J. Goedgebeur, J. Hägglund, K. Markström, Generation and properties of snarks, arXiv:1206.6690v3, p. 29, Appendices (format of the lists) and Appendix 8.1

import Mathlib

namespace SnarkGen.OddFactors

/-- The 39 edges of the graph of Appendix 8.1 of arXiv:1206.6690v3 (p. 29), decoded from the
printed list of higher-numbered neighbours
`{2, 3, 4, 5, 6, 7, 8, 9, 10, 7, 9, 8, 10, 11, 12, 13, 14, 15, 16, 15, 17, 18, 19, 18, 20, 18, 21,
22, 21, 23, 23, 24, 22, 24, 25, 26, 26, 25, 26}`.
Vertex `i` of the paper (1-based) is `i - 1 : Fin 26`. -/
def G81Edges : List (Fin 26 × Fin 26) :=
  [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (2, 6), (2, 7), (3, 8), (3, 9), (4, 6), (4, 8),
   (5, 7), (5, 9), (6, 10), (7, 11), (8, 12), (9, 13), (10, 14), (10, 15), (11, 14), (11, 16),
   (12, 17), (12, 18), (13, 17), (13, 19), (14, 17), (15, 20), (15, 21), (16, 20), (16, 22),
   (18, 22), (18, 23), (19, 21), (19, 23), (20, 24), (21, 25), (22, 25), (23, 24), (24, 25)]

/-- The graph `G₈.₁` of Appendix 8.1 of arXiv:1206.6690v3 (p. 29), "a cubic graph where all
2-factors only consist of odd cycles", on the vertex set `Fin 26`: two vertices are adjacent iff
the (ordered) pair or its reverse is in `G81Edges`. -/
def G81 : SimpleGraph (Fin 26) where
  Adj a b := (a, b) ∈ G81Edges ∨ (b, a) ∈ G81Edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel G81.Adj := fun a b =>
  inferInstanceAs (Decidable ((a, b) ∈ G81Edges ∨ (b, a) ∈ G81Edges))

end SnarkGen.OddFactors


