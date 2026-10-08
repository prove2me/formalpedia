-- Prove2me | Definitions.Def_StrongPerfectGraph_EvenPrism_Appearance
-- name    : StrongPerfectGraph_EvenPrism_Appearance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:07:56.007529+00:00
-- url     : https://prove2.me/theorems/d2583207-277e-4577-a279-ce4e8965e996
-- title:
--   Nondegenerate appearance of K4
-- statement:
--   A **subdivision of $K_4$** replaces each of its six edges by a track; the tracks have distinct internal vertices and together account for every vertex and edge of the resulting graph $H$. An **appearance** in $G$ is an induced copy of the line graph $L(H)$ for a bipartite such subdivision. It is **degenerate** precisely when a four-cycle of $H$ contains the four branch vertices:
--
--   $$\operatorname{Nondegenerate}(H)\iff \text{no four-cycle of }H\text{ contains all four branch vertices}. $$
--
--   The predicate records existence of a nondegenerate appearance in the ambient graph. It is the exclusion in Theorems 10.5 and 10.6, and does not impose an exclusion on the complement.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), https://doi.org/10.4007/annals.2006.164.51, p. 72, §5 definition of degenerate subdivision; pp. 74–75, §5 definitions of track, subdivision and appearance

import Definitions.Def_StrongPerfectGraph_EvenPrism_PathHole

namespace StrongPerfectGraph.EvenPrism

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Six internally disjoint tracks replace the edges of K₄, and give
exactly the vertices and edges of H. -/
def IsSubdivisionK4 (H : SimpleGraph W) (branch : Fin 4 → W)
    (R : Fin 4 → Fin 4 → List W) : Prop :=
  Function.Injective branch ∧
  (∀ i j, i < j → 2 ≤ (R i j).length ∧ (R i j).Nodup ∧
    (R i j).head? = some (branch i) ∧
    (R i j).getLast? = some (branch j)) ∧
  (∀ w : W, ∃ i j, i < j ∧ w ∈ R i j) ∧
  (∀ u v : W, H.Adj u v ↔ ∃ i j, i < j ∧ TrackEdge (R i j) u v) ∧
  (∀ i j k, i < j → branch k ∉ PathInterior (R i j)) ∧
  (∀ i j k l, i < j → k < l → (i, j) ≠ (k, l) →
    Disjoint (PathInterior (R i j)) {w | w ∈ R k l})

/-- The four branch vertices lie on a 4-cycle of the subdivision. -/
def IsDegenerateK4Subdivision (H : SimpleGraph W) (branch : Fin 4 → W) : Prop :=
  ∃ c : List W, IsHole H c ∧ c.length = 4 ∧ ∀ i, branch i ∈ c

/-- An induced line graph of a bipartite K₄-subdivision whose branch
vertices do not lie on a four-cycle. -/
def HasNondegenerateAppearanceK4 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∃ (n : ℕ) (H : SimpleGraph (Fin n))
    (branch : Fin 4 → Fin n) (R : Fin 4 → Fin 4 → List (Fin n)),
    IsSubdivisionK4 H branch R ∧ H.IsBipartite ∧
    ¬ IsDegenerateK4Subdivision H branch ∧
    Nonempty (H.lineGraph ↪g G)

end StrongPerfectGraph.EvenPrism


