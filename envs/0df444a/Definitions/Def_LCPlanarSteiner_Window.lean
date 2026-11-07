-- Prove2me | Definitions.Def_LCPlanarSteiner_Window
-- name    : LCPlanarSteiner_Window
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:03:22.634213+00:00
-- url     : https://prove2.me/theorems/b1096fb9-30df-490b-9e91-a4cebe9b5094
-- title:
--   Rooted windows: a connected contraction and deletions
-- statement:
--   A **window** of a set $F^\star$ of arcs is described by a set $Z$ of vertices contracted to a root $\rho$, a set $V$ of retained vertices, a set $A \subseteq F^\star$ of retained arcs, and possibly a free pendant arc $\rho \to v_0$. It is **valid** when
--   1. $Z$ and $V$ are disjoint sets of vertices and $A \subseteq F^\star$;
--   2. every arc of $A$ has both ends in $Z \cup V$ and not both in $Z$ (loops at $\rho$ are deleted);
--   3. $Z$ is weakly connected through arcs of $F^\star$ inside $Z$ (a connected contraction);
--   4. a pendant arc occurs only when $Z = \emptyset$ (then $\rho$ is a new vertex), and its head is retained.
--
--   In the window, an arc of $A$ joins the images of its ends, a vertex of $Z$ having image $\rho$. Its cost is $c(M) = c(A)$: the pendant arc is free and has length $0$. Removing $\rho$ leaves the original subgraph on $V$.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), Lemma 4.2 and its proof, p.12

import Mathlib
import Definitions.Def_LCPlanarSteiner_Net

namespace LCPlanarSteiner

/-- **A rooted window graph `M`, obtained by a connected contraction and deletions.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), Lemma 4.2, p.12: "There is a planar rooted graph M … Every assigned witness is unchanged in
M − {ρ}, which is an original subgraph … The graph is obtained by connected contractions and
deletions; a free pendant root is allowed for the first window." Proof, p.12: "If j > 0, contract
the connected C_{j−1} to ρ; if j = 0, instead add the free zero-length edge ρ → v₀ … Delete loops at
the contracted root. Keep parallel edges with their original labels, costs and lengths."

A window is described by a set `Z` of original vertices contracted to the root `ρ`, the set `V` of
retained original vertices, the set `A` of retained original arcs, and an optional free pendant
arc `ρ → v₀`. In `M`, an arc `e ∈ A` joins the images of its tail and head, the image of a vertex
of `Z` being `ρ`.

`Window.Valid G F W`: `Z` and `V` are disjoint sets of vertices; `A ⊆ F`; every arc of `A` is an arc
of `G` with both ends in `Z ∪ V`, not both in `Z` (loops at `ρ` are deleted); `Z` is weakly
connected through arcs of `F` with both ends in `Z` (a connected contraction); a pendant arc
`ρ → v₀` occurs only when `Z = ∅` (the first window, `ρ` a new vertex) and then `v₀ ∈ V`.

**Formalization Note.** `M − {ρ}` is then the original subgraph with vertices `V` and the arcs of `A`
with both ends in `V`. The cost `c(M)` is `pcost G A`; the pendant arc is free and has length `0`. -/
structure Window where
  /-- original vertices contracted to the root `ρ` -/
  Z : Finset ℕ
  /-- retained original vertices -/
  V : Finset ℕ
  /-- retained original arcs -/
  A : Finset ℕ
  /-- head `v₀` of the free pendant arc `ρ → v₀`, if present -/
  pend : Option ℕ

/-- Validity of a window of the arc set `F`. -/
def Window.Valid (G : Net) (F : Finset ℕ) (W : Window) : Prop :=
  (∀ u ∈ W.Z, u < G.n) ∧ (∀ u ∈ W.V, u < G.n) ∧ Disjoint W.Z W.V ∧ W.A ⊆ F ∧
  (∀ e ∈ W.A, e < G.arcs.length ∧ (G.tl e ∈ W.Z ∨ G.tl e ∈ W.V) ∧
    (G.hd e ∈ W.Z ∨ G.hd e ∈ W.V) ∧ ¬ (G.tl e ∈ W.Z ∧ G.hd e ∈ W.Z)) ∧
  (∀ u ∈ W.Z, ∀ v ∈ W.Z, Relation.ReflTransGen
    (fun a b => a ∈ W.Z ∧ b ∈ W.Z ∧ ∃ e ∈ F, e < G.arcs.length ∧
      ((G.tl e = a ∧ G.hd e = b) ∨ (G.tl e = b ∧ G.hd e = a))) u v) ∧
  ∀ v₀, W.pend = some v₀ → W.Z = ∅ ∧ v₀ ∈ W.V

/-- The image in `M` of an original vertex: `none` (the root `ρ`) for a contracted vertex. -/
def Window.img (W : Window) (u : ℕ) : Option ℕ := if u ∈ W.Z then none else some u

end LCPlanarSteiner


