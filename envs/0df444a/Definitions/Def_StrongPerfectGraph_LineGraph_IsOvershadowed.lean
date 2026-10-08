-- Prove2me | Definitions.Def_StrongPerfectGraph_LineGraph_IsOvershadowed
-- name    : StrongPerfectGraph_LineGraph_IsOvershadowed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:47:47.124451+00:00
-- url     : https://prove2.me/theorems/a53abbf1-4486-4434-839a-bdf8668eb566
-- title:
--   Overshadowed appearance
-- statement:
--   For a vertex $v$ of $H$ write $\delta_H(v)$ for the set of edges of $H$ incident with $v$; in $L(H)$ it is a clique. An appearance $L(H)$ of $J$ in $G$ is **overshadowed** if there is a branch $B$ of $H$ of odd length at least $3$, with ends $b_1, b_2$, such that some vertex of $G$ is nonadjacent in $G$ to at most one vertex of $\delta_H(b_1)$ and to at most one vertex of $\delta_H(b_2)$.
--
--   For instance an appearance is overshadowed if some vertex is major and some branch has odd length at least $3$.
--
--   **Formalization Note** The appearance is given by the induced embedding $e : L(H) \hookrightarrow G$; "some vertex of $G$" ranges over all of $V(G)$, as on the page.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 85, §6, definition of overshadowed

import Mathlib
import Definitions.Def_StrongPerfectGraph_LineGraph_IsSubdivision

namespace StrongPerfectGraph.LineGraph

/-- The appearance `L(H)`, embedded in `G` by `e`, is **overshadowed** (p. 85): some branch `B` of
`H` has odd length `≥ 3` and ends `b₁, b₂` such that some vertex `x` of `G` is nonadjacent in `G` to
at most one vertex of `δ_H(b₁)` and to at most one vertex of `δ_H(b₂)`. -/
def IsOvershadowed {U V : Type*} (H : SimpleGraph U) (G : SimpleGraph V)
    (e : H.lineGraph ↪g G) : Prop :=
  ∃ B : List U, IsBranch H B ∧ Odd (B.length - 1) ∧ 3 ≤ B.length - 1 ∧
    ∃ b₁ b₂ : U, B.head? = some b₁ ∧ B.getLast? = some b₂ ∧
      ∃ x : V,
        {f : H.edgeSet | f.1 ∈ H.incidenceSet b₁ ∧ ¬ G.Adj x (e f)}.Subsingleton ∧
        {f : H.edgeSet | f.1 ∈ H.incidenceSet b₂ ∧ ¬ G.Adj x (e f)}.Subsingleton

/-- There is an **overshadowed appearance** of `J` in `G`. -/
def HasOvershadowedAppearance {W V : Type*} (J : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ, ∃ H : SimpleGraph (Fin n), IsSubdivision J H ∧ H.IsBipartite ∧
    ∃ e : H.lineGraph ↪g G, IsOvershadowed H G e

end StrongPerfectGraph.LineGraph


