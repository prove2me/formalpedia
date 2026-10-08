-- Prove2me | Definitions.Def_SteinbergFalse_Counterexample_G
-- name    : SteinbergFalse_Counterexample_G
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:11:38.907013+00:00
-- url     : https://prove2.me/theorems/89b53394-2687-49ee-a895-7154efd314b0
-- title:
--   The graph $G$ of Figure 3: four copies of $G_2$ (166 vertices, 300 edges)
-- statement:
--   The graph $G$ is the graph drawn in Figure 3 of Cohen-Addad, Hebdige, Král', Li and Salgado, the counterexample to Steinberg's Conjecture. It has ten named vertices: the central vertex $a$, the bottom triangle $b, c, c'$, and the two inner triangles $d, e, f$ and $d', e', f'$. It consists of four copies of the graph $G_2$ of Figure 2 together with $12$ further edges. Each copy of $G_2$ is glued to the named vertices through its contact vertices $a_2, b_2, c_2$ (the contact vertices $a, b, c$ of $G_2$):
--
--   | copy | $a_2 \mapsto$ | $b_2 \mapsto$ | $c_2 \mapsto$ |
--   |---|---|---|---|
--   | 0 | $a$ | $c$ | $d$ |
--   | 1 | $a$ | $c$ | $f$ |
--   | 2 | $a$ | $c'$ | $d'$ |
--   | 3 | $a$ | $c'$ | $f'$ |
--
--   The $39$ other vertices of each copy are new vertices, distinct from each other, from the named vertices, and from the vertices of the other copies; the vertices $b$, $e$, $e'$ lie in no copy. The edges of $G$ are the images of the $72$ edges of $G_2$ under each of the four copies, together with the $12$ edges
--
--   $$
--   de,\ ef,\ df,\ ea,\ ab,\ bc,\ bc',\ cc',\ d'e',\ e'f',\ d'f',\ e'a .
--   $$
--
--   Hence $|V(G)| = 10 + 4\cdot 39 = 166$ and $|E(G)| = 4 \cdot 72 + 12 = 300$.
--
--   **Formalization Note** The vertex set is `Fin 166` with $a \mapsto 0$, $b \mapsto 1$, $c \mapsto 2$, $c' \mapsto 3$, $e \mapsto 4$, $e' \mapsto 5$, $d \mapsto 6$, $f \mapsto 7$, $d' \mapsto 8$, $f' \mapsto 9$. Copy $k \in \{0,1,2,3\}$ is the embedding `copyG k : Fin 42 ↪ Fin 166` that sends $G_2$'s contact vertices as in the table and $G_2$'s vertex $w \in \{3, \dots, 41\}$ to $10 + 39k + (w - 3)$. The graph is `(⨆ k, G2.map (copyG k)) ⊔ fromEdgeSet {the 12 edges}`. A local check confirms the graph has exactly 300 edges and coincides edge for edge with an independent machine-checked transcription of Figure 3.
-- source:
--   Cohen-Addad, Hebdige, Král', Li & Salgado, Steinberg's Conjecture is false, arXiv:1604.05108v2, p. 4, Figure 3; pp. 4–5, proof of Theorem 3

import Mathlib
import Definitions.Def_SteinbergFalse_Counterexample_G2

namespace SteinbergFalse.Counterexample

/-- The vertex map of the `k`-th copy (`k = 0, 1, 2, 3`) of `G₂` inside `G`.
`G` has vertex set `Fin 166` with a ↦ 0, b ↦ 1, c ↦ 2, c′ ↦ 3, e ↦ 4, e′ ↦ 5, d ↦ 6, f ↦ 7,
d′ ↦ 8, f′ ↦ 9 (Figure 3, p. 4). Copy k sends G₂'s contacts a, b, c to
a, c, d (k = 0); a, c, f (k = 1); a, c′, d′ (k = 2); a, c′, f′ (k = 3).
G₂'s remaining vertex `w ∈ {3, …, 41}` goes to the fresh vertex `10 + 39k + (w - 3)`. -/
def copyGFun (k : Fin 4) (w : Fin 42) : Fin 166 :=
  if w = 0 then ![0, 0, 0, 0] k       -- G₂'s a ↦ a
  else if w = 1 then ![2, 2, 3, 3] k  -- G₂'s b ↦ c, c, c′, c′
  else if w = 2 then ![6, 7, 8, 9] k  -- G₂'s c ↦ d, f, d′, f′
  else ⟨10 + 39 * k.val + (w.val - 3), by have := k.isLt; have := w.isLt; omega⟩

/-- `copyGFun k` as an embedding `Fin 42 ↪ Fin 166`. -/
def copyG (k : Fin 4) : Fin 42 ↪ Fin 166 :=
  ⟨copyGFun k, by revert k; decide⟩

/-- The graph `G` of Figure 3 (p. 4): four copies of `G₂` pasted together as in `copyG`,
with the additional vertices b, e, e′ and the 12 thick edges
d–e, e–f, d–f, e–a, a–b, b–c, b–c′, c–c′, d′–e′, e′–f′, d′–f′, e′–a.
It has 166 vertices and 300 edges. -/
def G : SimpleGraph (Fin 166) :=
  (⨆ k : Fin 4, G2.map (copyG k)) ⊔
    SimpleGraph.fromEdgeSet
      { s(6, 4), s(4, 7), s(6, 7),   -- triangle d e f
        s(4, 0),                     -- e a
        s(0, 1),                     -- a b
        s(1, 2), s(1, 3), s(2, 3),   -- triangle b c c′
        s(8, 5), s(5, 9), s(8, 9),   -- triangle d′ e′ f′
        s(5, 0) }                    -- e′ a

end SteinbergFalse.Counterexample


