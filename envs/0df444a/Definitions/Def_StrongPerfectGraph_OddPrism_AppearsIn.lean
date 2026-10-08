-- Prove2me | Definitions.Def_StrongPerfectGraph_OddPrism_AppearsIn
-- name    : StrongPerfectGraph_OddPrism_AppearsIn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T05:22:01.913261+00:00
-- url     : https://prove2.me/theorems/0f540b15-cf99-44cd-9df8-9e481ee5166c
-- title:
--   Subdivisions and appearances of a graph; $K_4$
-- statement:
--   A **track** in a graph $H$ is a (not necessarily induced) subgraph which is a path in the ordinary sense. Starting from a graph $J$ and repeatedly subdividing edges replaces each edge $uv$ of $J$ by a track joining $u$ and $v$, these tracks being pairwise disjoint except for their ends; the resulting graph $H$ is a **subdivision** of $J$ (and $V(J)\subseteq V(H)$).
--
--   A graph $J$ **appears** in a graph $G$ if there is a bipartite subdivision $H$ of $J$ such that the line graph $L(H)$ is isomorphic to an induced subgraph of $G$; $L(H)$ is then an **appearance** of $J$ in $G$. Here $L(H)$ has vertex set $E(H)$, two edges being adjacent when they share an end.
--
--   The hypothesis "there is no appearance of $K_4$ in $G$" excludes every appearance of the complete graph $K_4$, degenerate or not. It is the standing assumption of Sections 11–13 of the paper.
--
--   **Formalization Note** A subdivision is given by an injection $\varphi:V(J)\to V(H)$ and, for each edge $uv$ of $J$, a list of distinct vertices of $H$ from $\varphi(u)$ to $\varphi(v)$ with consecutive entries adjacent; the tracks meet only in $\varphi$-images, their interiors avoid the image of $\varphi$, and every vertex and every edge of $H$ lies on a track. $H$ lives on `Fin n`; "isomorphic to an induced subgraph" is a graph embedding `H.lineGraph ↪g G`, which reflects adjacency. `K4` is the complete graph on `Fin 4`.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), pp. 74–75, definitions of track, subdivision and appearance

import Mathlib

namespace StrongPerfectGraph.OddPrism

/-- `H` is a **subdivision** of `J` (p. 74): it is obtained from `J` by replacing each edge `uv`
by a track (a not necessarily induced path) of `H` joining `u` and `v`, these tracks being
disjoint except for their ends. Here `φ` places the vertices of `J` in `H` and `t u v` is the
track replacing the edge `uv`, listed from `φ u` to `φ v` (`t v u` is its reverse). The tracks
are internally disjoint, their interiors avoid the image of `φ`, every vertex of `H` is either
an original vertex or lies on a track, and every edge of `H` lies on a track. -/
def IsSubdivision {W U : Type*} (J : SimpleGraph W) (H : SimpleGraph U) : Prop :=
  ∃ (φ : W ↪ U) (t : W → W → List U),
    (∀ u v, J.Adj u v → t v u = (t u v).reverse) ∧
    (∀ u v, J.Adj u v →
      (t u v).head? = some (φ u) ∧ (t u v).getLast? = some (φ v) ∧
        (t u v).Nodup ∧ (t u v).IsChain H.Adj) ∧
    (∀ u v, J.Adj u v → ∀ x ∈ t u v, x ≠ φ u → x ≠ φ v → x ∉ Set.range φ) ∧
    (∀ u v u' v', J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ x ∈ t u v, x ∈ t u' v' → x ∈ Set.range φ) ∧
    (∀ x : U, x ∈ Set.range φ ∨ ∃ u v, J.Adj u v ∧ x ∈ t u v) ∧
    (∀ x y : U, H.Adj x y → ∃ u v, J.Adj u v ∧ [x, y] <:+: t u v)

/-- `J` **appears** in `G` (p. 75): for some bipartite subdivision `H` of `J`, the line graph
`L(H)` is isomorphic to an induced subgraph of `G` (a graph embedding `L(H) ↪g G` preserves and
reflects adjacency). Both degenerate and nondegenerate appearances count. -/
def AppearsIn {W V : Type*} (J : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ n : ℕ, ∃ H : SimpleGraph (Fin n),
    IsSubdivision J H ∧ H.IsBipartite ∧ Nonempty (H.lineGraph ↪g G)

/-- `K₄`, the complete graph on four vertices. -/
abbrev K4 : SimpleGraph (Fin 4) := ⊤

end StrongPerfectGraph.OddPrism


