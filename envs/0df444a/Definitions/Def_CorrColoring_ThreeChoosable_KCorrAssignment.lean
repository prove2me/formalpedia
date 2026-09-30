-- Prove2me | Definitions.Def_CorrColoring_ThreeChoosable_KCorrAssignment
-- name    : CorrColoring_ThreeChoosable_KCorrAssignment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:00:18.840158+00:00
-- url     : https://prove2.me/theorems/26ac4629-2387-40f6-9ddc-81343004893d
-- title:
--   $k$-correspondence assignments and $C$-colorings
-- statement:
--   Let $G$ be a simple graph and $k \ge 0$, and write $[k]$ for a set of $k$ colours. A **$k$-correspondence assignment** $C$ for $G$ assigns to every edge $uv$ of $G$ a partial matching $C_{uv}$ between $\{u\} \times [k]$ and $\{v\} \times [k]$; we write $(u,c)(v,d) \in E(C_{uv})$ for its edges. Concretely:
--
--   1. correspondences exist only along edges of $G$;
--   2. $C_{uv}$ and $C_{vu}$ are the same matching;
--   3. each $(u,c)$ is matched to at most one $(v,d)$, and each $(v,d)$ to at most one $(u,c)$.
--
--   A **$C$-coloring** of $G$ is a map $\varphi : V(G) \to [k]$ such that
--
--   $$(u, \varphi(u))(v, \varphi(v)) \notin E(C_{uv}) \quad \text{for every edge } uv \in E(G),$$
--
--   and $G$ is **$C$-colorable** if a $C$-coloring exists.
--
--   Correspondence colouring (also called DP-colouring) generalizes list colouring: taking $C_{uv}$ to match equal colours recovers ordinary colouring from the lists $[k]$, and renaming colours at each vertex makes the lists irrelevant.
--
--   **Formalization Note** The paper's colour set $[k] = \{1, \dots, k\}$ is encoded as `Fin k` $= \{0, \dots, k-1\}$; renaming colours makes the choice immaterial. The matching is a relation `M u c v d`; the fields `adj`, `symm` and `unique` say respectively that it lives on edges, is symmetric, and is a partial matching.
-- source:
--   Dvořák, Postle, Correspondence coloring and its application to list-coloring planar graphs without cycles of lengths 4 to 8, arXiv:1508.03437v2, pp. 3-5, Definition 1 and Definition 2 (k-correspondence assignment, C-coloring, C-colorable)

import Mathlib

namespace CorrColoring.ThreeChoosable

/-- A `k`-correspondence assignment for `G` (Dvořák–Postle, Definition 2, colour set
`[k]` encoded as `Fin k`). `M u c v d` says that `(u, c)(v, d)` is an edge of the matching
`C_{uv}`. Correspondences live only on edges of `G` (`adj`), `C_{uv}` and `C_{vu}` are the same
matching (`symm`), and each `(u, c)` is matched to at most one colour at `v` (`unique`; with
`symm` this makes `C_{uv}` a partial matching on both sides). -/
structure KCorrAssignment {V : Type*} (G : SimpleGraph V) (k : ℕ) where
  /-- `M u c v d`: `(u, c)(v, d) ∈ E(C_{uv})` -/
  M : V → Fin k → V → Fin k → Prop
  adj : ∀ {u : V} {c : Fin k} {v : V} {d : Fin k}, M u c v d → G.Adj u v
  symm : ∀ {u : V} {c : Fin k} {v : V} {d : Fin k}, M u c v d → M v d u c
  unique : ∀ {u : V} {c : Fin k} {v : V} {d d' : Fin k}, M u c v d → M u c v d' → d = d'

/-- A `C`-colouring: a colour `φ v ∈ [k]` for every vertex such that for every edge `uv`,
the vertices `(u, φ u)` and `(v, φ v)` are not adjacent in `C_{uv}`. -/
def IsCColoring {V : Type*} {G : SimpleGraph V} {k : ℕ} (C : KCorrAssignment G k)
    (φ : V → Fin k) : Prop :=
  ∀ u v, G.Adj u v → ¬ C.M u (φ u) v (φ v)

end CorrColoring.ThreeChoosable


