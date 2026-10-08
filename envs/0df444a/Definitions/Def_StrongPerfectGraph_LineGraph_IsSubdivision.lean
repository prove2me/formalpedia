-- Prove2me | Definitions.Def_StrongPerfectGraph_LineGraph_IsSubdivision
-- name    : StrongPerfectGraph_LineGraph_IsSubdivision
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:33:07.961059+00:00
-- url     : https://prove2.me/theorems/03bd7efb-060a-49bf-901f-fafbd7710ce9
-- title:
--   Subdivisions, 3-connected and cyclically 3-connected graphs
-- statement:
--   A graph $H$ is a **subdivision** of a graph $J$ if it is obtained from $J$ by replacing each edge $uv$ of $J$ by a track of $H$ joining $u$ and $v$, where these tracks are disjoint except for their ends. Concretely: there is an injection $\varphi : V(J) \to V(H)$ and, for each edge $uv$ of $J$, a track $P_{uv}$ of $H$ from $\varphi(u)$ to $\varphi(v)$ ($P_{vu}$ being $P_{uv}$ reversed), such that the internal vertices of $P_{uv}$ lie outside $\varphi(V(J))$ and outside every other track, and every vertex and every edge of $H$ lies on $\varphi(V(J))$ or on one of the tracks.
--
--   A graph $J$ is **3-connected** if it has more than $3$ vertices (the paper's convention: a $k$-connected graph has more than $k$ vertices) and remains connected after deleting any set of at most $2$ vertices. A graph is **cyclically 3-connected** if it is a subdivision of some 3-connected graph.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 74, §5, definitions of subdivision, k-connected (convention), cyclically 3-connected

import Mathlib
import Definitions.Def_StrongPerfectGraph_LineGraph_IsTrack

namespace StrongPerfectGraph.LineGraph

/-- `H` is a **subdivision** of `J` (p. 74) witnessed by `φ` and `P`: `φ` embeds `V(J)` into `V(H)`,
and each edge `uv` of `J` is replaced by the track `P u v` of `H` from `φ u` to `φ v`
(`P v u` is the same track reversed). The internal vertices of each track avoid `φ(V(J))` and
every other track, and the tracks cover all vertices and all edges of `H`. -/
def IsSubdivisionVia {W V : Type*} (J : SimpleGraph W) (H : SimpleGraph V) (φ : W → V)
    (P : W → W → List V) : Prop :=
  Function.Injective φ ∧
  (∀ u v, J.Adj u v →
    IsTrack H (P u v) ∧ (P u v).head? = some (φ u) ∧ (P u v).getLast? = some (φ v) ∧
      P v u = (P u v).reverse ∧ ∀ z ∈ (P u v).tail.dropLast, z ∉ Set.range φ) ∧
  (∀ u v w x, J.Adj u v → J.Adj w x → s(u, v) ≠ s(w, x) →
    ∀ z ∈ (P u v).tail.dropLast, z ∉ P w x) ∧
  (∀ z : V, z ∈ Set.range φ ∨ ∃ u v, J.Adj u v ∧ z ∈ P u v) ∧
  (∀ a b, H.Adj a b → ∃ u v, J.Adj u v ∧ s(a, b) ∈ trackEdges (P u v))

/-- `H` is a **subdivision** of `J` (p. 74): obtained from `J` by replacing each edge by a track
joining the same pair of vertices, the tracks disjoint except for their ends. -/
def IsSubdivision {W V : Type*} (J : SimpleGraph W) (H : SimpleGraph V) : Prop :=
  ∃ (φ : W → V) (P : W → W → List V), IsSubdivisionVia J H φ P

/-- `J` is **3-connected** (p. 74, with the paper's convention that a `k`-connected graph has more
than `k` vertices): `J` has at least four vertices and stays connected after deleting any set of at
most two vertices. -/
def IsThreeConnected {W : Type*} (J : SimpleGraph W) : Prop :=
  3 < Nat.card W ∧ ∀ S : Set W, S.ncard ≤ 2 → (J.induce Sᶜ).Connected

/-- `H` is **cyclically 3-connected** (p. 74): a subdivision of some 3-connected graph. -/
def IsCyclicallyThreeConnected {V : Type*} (H : SimpleGraph V) : Prop :=
  ∃ m : ℕ, ∃ J : SimpleGraph (Fin m), IsThreeConnected J ∧ IsSubdivision J H

end StrongPerfectGraph.LineGraph


