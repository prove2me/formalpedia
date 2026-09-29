-- Prove2me | Definitions.Def_opg37271_star_edge_coloring
-- name    : opg37271_star_edge_coloring
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-07T06:28:30.028434+00:00
-- url     : https://prove2.me/theorems/58b54da8-840b-4a6e-90f7-8445a354ef58
-- title:
--   Star edge colorings and subcubic simple graphs
-- statement:
--   This module fixes the graph-theoretic language used for OPG-37271.
--
--   For a simple graph $G$ and a color type $K$, an edge coloring assigns a member of $K$ to every unordered edge. It is proper when distinct edges meeting at a vertex receive distinct colors. A forbidden four-edge path consists of five pairwise distinct consecutive vertices, and a forbidden four-cycle consists of four pairwise distinct cyclic vertices. In either configuration, bichromaticity is represented by equality of the two pairs of opposite-position edge colors.
--
--   A star edge coloring is a proper edge coloring with neither forbidden configuration. The proposition
--
--   $$
--   \operatorname{HasStarEdgeColoring}(G,k)
--   $$
--
--   means that such a coloring exists with palette $\operatorname{Fin}(k)$. Finally, $G$ is subcubic when every neighbor set has extended cardinality at most three. Paths are simple but are not required to be induced, and four-cycles are checked separately.
-- source:
--   Open Problem Garden, OPG-37271, https://www.openproblemgarden.org/comment/reply/37271; definition also stated in Lei--Shi--Song, Star chromatic index of subcubic multigraphs, J. Graph Theory 88 (2018), 566--576, https://arxiv.org/abs/1701.04105v3, Section 1

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Data.Set.Card

namespace OPG37271

universe u

/-- An edge coloring of a simple graph by colors in `K`. -/
abbrev EdgeColoring {V : Type u} (G : SimpleGraph V) (K : Type*) :=
  G.EdgeLabeling K

/-- A proper edge coloring: two distinct edges incident with one vertex
receive different colors. -/
def IsProperEdgeColoring {V : Type u} {G : SimpleGraph V} {K : Type*}
    (c : EdgeColoring G K) : Prop :=
  ∀ (v u w : V) (hvu : G.Adj v u) (hvw : G.Adj v w),
    u ≠ w → c.get v u hvu ≠ c.get v w hvw

/-- A simple path of four edges whose edge colors alternate between two colors. -/
def HasBicoloredPathFour {V : Type u} {G : SimpleGraph V} {K : Type*}
    (c : EdgeColoring G K) : Prop :=
  ∃ v₀ v₁ v₂ v₃ v₄ : V,
    [v₀, v₁, v₂, v₃, v₄].Nodup ∧
    ∃ (h₀₁ : G.Adj v₀ v₁) (h₁₂ : G.Adj v₁ v₂)
      (h₂₃ : G.Adj v₂ v₃) (h₃₄ : G.Adj v₃ v₄),
      c.get v₀ v₁ h₀₁ = c.get v₂ v₃ h₂₃ ∧
      c.get v₁ v₂ h₁₂ = c.get v₃ v₄ h₃₄

/-- A cycle of four edges whose edge colors alternate between two colors. -/
def HasBicoloredCycleFour {V : Type u} {G : SimpleGraph V} {K : Type*}
    (c : EdgeColoring G K) : Prop :=
  ∃ v₀ v₁ v₂ v₃ : V,
    [v₀, v₁, v₂, v₃].Nodup ∧
    ∃ (h₀₁ : G.Adj v₀ v₁) (h₁₂ : G.Adj v₁ v₂)
      (h₂₃ : G.Adj v₂ v₃) (h₃₀ : G.Adj v₃ v₀),
      c.get v₀ v₁ h₀₁ = c.get v₂ v₃ h₂₃ ∧
      c.get v₁ v₂ h₁₂ = c.get v₃ v₀ h₃₀

/-- A star edge coloring is proper and has no bichromatic simple path or cycle
of four edges. Paths need not be induced. -/
def IsStarEdgeColoring {V : Type u} {G : SimpleGraph V} {K : Type*}
    (c : EdgeColoring G K) : Prop :=
  IsProperEdgeColoring c ∧
    ¬ HasBicoloredPathFour c ∧
    ¬ HasBicoloredCycleFour c

/-- Existence of a star edge coloring using a palette of `k` labeled colors. -/
def HasStarEdgeColoring {V : Type u} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : EdgeColoring G (Fin k), IsStarEdgeColoring c

/-- A simple graph is subcubic when every vertex has at most three neighbors. -/
def IsSubcubic {V : Type u} (G : SimpleGraph V) : Prop :=
  ∀ v : V, (G.neighborSet v).encard ≤ 3

end OPG37271


