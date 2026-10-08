-- Prove2me | Definitions.Def_SteinbergFalse_Counterexample_G1
-- name    : SteinbergFalse_Counterexample_G1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:10:16.159401+00:00
-- url     : https://prove2.me/theorems/39e4a75d-a611-4f95-baad-f5e84fb536b8
-- title:
--   The graph $G_1$ of Figure 1 (15 vertices, 23 edges)
-- statement:
--   The graph $G_1$ is the graph drawn in Figure 1 of Cohen-Addad, Hebdige, Král', Li and Salgado. It has the fifteen vertices $a, b, c, d, e, f, g, h, i, j, k, l, m, n, o$ and the following $23$ edges:
--
--   1. the triangle $afg$: $af$, $ag$, $fg$;
--   2. the triangle $bde$: $bd$, $be$, $de$;
--   3. the triangle $chi$: $ch$, $ci$, $hi$;
--   4. the triangle $efk$: $ef$, $ek$, $fk$;
--   5. the triangle $ghl$: $gh$, $gl$, $hl$;
--   6. the edges $dj$ and $ij$;
--   7. the edges $jm$, $kn$ and $lo$;
--   8. the triangle $mno$: $mn$, $no$, $mo$.
--
--   The vertices $a$, $b$, $c$ are the **contact vertices** (drawn bold in the figure). In the drawing, the outer boundary is the cycle $a\,f\,e\,b\,d\,j\,i\,c\,h\,g\,a$, and the triangle $mno$ sits in the middle, joined to $j$, $k$, $l$.
--
--   $G_1$ is the first of the three gadgets of the construction: Lemma 1 of the paper states its properties, and three copies of it make up the graph $G_2$.
--
--   **Formalization Note** The vertex set is `Fin 15` with $a \mapsto 0$, $b \mapsto 1$, $c \mapsto 2$, $d \mapsto 3$, $e \mapsto 4$, $f \mapsto 5$, $g \mapsto 6$, $h \mapsto 7$, $i \mapsto 8$, $j \mapsto 9$, $k \mapsto 10$, $l \mapsto 11$, $m \mapsto 12$, $n \mapsto 13$, $o \mapsto 14$; the abbreviations `G1.a`, `G1.b`, `G1.c` name the contact vertices $0, 1, 2$. The graph is `SimpleGraph.fromEdgeSet` of the 23 listed edges.
-- source:
--   Cohen-Addad, Hebdige, Král', Li & Salgado, Steinberg's Conjecture is false, arXiv:1604.05108v2, p. 2, Figure 1 (and Lemma 1)

import Mathlib

namespace SteinbergFalse.Counterexample

/-- The graph `G₁` of Figure 1 (Cohen-Addad et al., p. 2), on the vertex set `Fin 15`, with the
paper's labels encoded as a ↦ 0, b ↦ 1, c ↦ 2, d ↦ 3, e ↦ 4, f ↦ 5, g ↦ 6, h ↦ 7, i ↦ 8, j ↦ 9,
k ↦ 10, l ↦ 11, m ↦ 12, n ↦ 13, o ↦ 14. Its 23 edges are exactly those listed below. -/
def G1 : SimpleGraph (Fin 15) :=
  SimpleGraph.fromEdgeSet
    { s(0, 5), s(0, 6), s(5, 6),     -- triangle a f g
      s(1, 4), s(1, 3), s(3, 4),     -- triangle b e d
      s(2, 7), s(2, 8), s(7, 8),     -- triangle c h i
      s(4, 5), s(4, 10), s(5, 10),   -- triangle e f k
      s(6, 7), s(6, 11), s(7, 11),   -- triangle g h l
      s(3, 9), s(8, 9),              -- d j, i j
      s(9, 12), s(10, 13), s(11, 14), -- j m, k n, l o
      s(12, 13), s(13, 14), s(12, 14) } -- triangle m n o

namespace G1

/-- The contact vertex `a` of `G₁`. -/
abbrev a : Fin 15 := 0
/-- The contact vertex `b` of `G₁`. -/
abbrev b : Fin 15 := 1
/-- The contact vertex `c` of `G₁`. -/
abbrev c : Fin 15 := 2

end G1

end SteinbergFalse.Counterexample


