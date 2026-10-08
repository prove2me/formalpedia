-- Prove2me | Definitions.Def_SteinbergFalse_Counterexample_G2
-- name    : SteinbergFalse_Counterexample_G2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:10:45.171708+00:00
-- url     : https://prove2.me/theorems/2b474de0-0b6b-471e-b530-c72ab3f820a3
-- title:
--   The graph $G_2$ of Figure 2: three copies of $G_1$ pasted together (42 vertices, 72 edges)
-- statement:
--   The graph $G_2$ is the graph drawn in Figure 2 of Cohen-Addad, Hebdige, Král', Li and Salgado. It has six named vertices: the three **contact vertices** $a$, $b$, $c$ (the corners of the outer triangle, drawn bold) and the inner triangle $d$, $e$, $f$. It consists of three copies of the graph $G_1$ of Figure 1 together with the triangle $def$. Each copy of $G_1$ is glued to the named vertices through its own contact vertices $a_1, b_1, c_1$ (we write $a_1, b_1, c_1$ for the contact vertices $a, b, c$ of $G_1$):
--
--   | copy | $a_1 \mapsto$ | $b_1 \mapsto$ | $c_1 \mapsto$ |
--   |---|---|---|---|
--   | 0 (between $a$ and $b$) | $d$ | $a$ | $b$ |
--   | 1 (between $a$ and $c$) | $f$ | $a$ | $c$ |
--   | 2 (between $b$ and $c$) | $e$ | $b$ | $c$ |
--
--   The twelve other vertices $d_1, \dots, o_1$ of each copy are new vertices, distinct from each other, from the named vertices, and from the vertices of the other copies. The edges of $G_2$ are the images of the $23$ edges of $G_1$ under each of the three copies, together with the three edges $de$, $ef$, $df$. Hence
--
--   $$
--   |V(G_2)| = 6 + 3\cdot 12 = 42, \qquad |E(G_2)| = 3 \cdot 23 + 3 = 72 .
--   $$
--
--   $G_2$ is the second gadget of the construction: Lemma 2 of the paper states its properties, and four copies of it make up the final graph $G$.
--
--   **Formalization Note** The vertex set is `Fin 42` with $a \mapsto 0$, $b \mapsto 1$, $c \mapsto 2$, $d \mapsto 3$, $e \mapsto 4$, $f \mapsto 5$. Copy $k \in \{0,1,2\}$ is the embedding `copy2 k : Fin 15 ↪ Fin 42` that sends $G_1$'s contact vertices as in the table and $G_1$'s vertex $v \in \{3, \dots, 14\}$ to $6 + 12k + (v - 3)$. The graph is `(⨆ k, G1.map (copy2 k)) ⊔ fromEdgeSet {de, ef, df}`, i.e. literally the union of the three images of $G_1$ and the triangle $def$. The abbreviations `G2.a`, `G2.b`, `G2.c` name the vertices $0, 1, 2$. A local check confirms the graph has exactly 72 edges.
-- source:
--   Cohen-Addad, Hebdige, Král', Li & Salgado, Steinberg's Conjecture is false, arXiv:1604.05108v2, p. 3, Figure 2 and proof of Lemma 2

import Mathlib
import Definitions.Def_SteinbergFalse_Counterexample_G1

namespace SteinbergFalse.Counterexample

/-- The vertex map of the `k`-th copy (`k = 0, 1, 2`) of `G₁` inside `G₂`.
`G₂` has vertex set `Fin 42` with a ↦ 0, b ↦ 1, c ↦ 2, d ↦ 3, e ↦ 4, f ↦ 5 (Figure 2, p. 3).
Copy 0 sends G₁'s a, b, c to d, a, b; copy 1 sends them to f, a, c; copy 2 sends them to
e, b, c. G₁'s remaining vertex `v ∈ {3, …, 14}` goes to the fresh vertex `6 + 12k + (v - 3)`. -/
def copy2Fun (k : Fin 3) (v : Fin 15) : Fin 42 :=
  if v = 0 then ![3, 5, 4] k        -- G₁'s a ↦ d, f, e
  else if v = 1 then ![0, 0, 1] k   -- G₁'s b ↦ a, a, b
  else if v = 2 then ![1, 2, 2] k   -- G₁'s c ↦ b, c, c
  else ⟨6 + 12 * k.val + (v.val - 3), by have := k.isLt; have := v.isLt; omega⟩

/-- `copy2Fun k` as an embedding `Fin 15 ↪ Fin 42`. -/
def copy2 (k : Fin 3) : Fin 15 ↪ Fin 42 :=
  ⟨copy2Fun k, by revert k; decide⟩

/-- The graph `G₂` of Figure 2 (p. 3): three copies of `G₁` pasted together along the
contact vertices as in `copy2`, plus the triangle `d e f` (edges 3–4, 4–5, 3–5).
It has 42 vertices and 72 edges. -/
def G2 : SimpleGraph (Fin 42) :=
  (⨆ k : Fin 3, G1.map (copy2 k)) ⊔
    SimpleGraph.fromEdgeSet {s(3, 4), s(4, 5), s(3, 5)}

namespace G2

/-- The contact vertex `a` of `G₂`. -/
abbrev a : Fin 42 := 0
/-- The contact vertex `b` of `G₂`. -/
abbrev b : Fin 42 := 1
/-- The contact vertex `c` of `G₂`. -/
abbrev c : Fin 42 := 2

end G2

end SteinbergFalse.Counterexample


