-- Prove2me | Definitions.Def_KColoringFaster_ListBootstrap_Normalization
-- name    : KColoringFaster_ListBootstrap_Normalization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:48.291197+00:00
-- url     : https://prove2.me/theorems/e08e88a7-9a4c-49ab-b6f6-f39b8960dfb3
-- title:
--   Lemma 3.2 — rule (N) and singleton propagation
-- statement:
--   The two operations of the normalization lemma (Lemma 3.2, p. 8).
--
--   **Rule (i).** For a graph $G$ with lists $L$, one step deletes an edge $uv$ with $L(u)\cap L(v)=\emptyset$. The process **(N)** repeats this as long as such an edge exists; $\mathrm{norm}_L(G)$ is $G$ with all such edges deleted. Lists are not changed.
--
--   **Rule (ii).** A propagation state is a set $S$ of remaining vertices together with current lists $L'$; initially $S=V(G)$ and $L'=L$. From a state in which no remaining vertex has an empty list, one step chooses a remaining vertex $v$ with $L'(v)=\{c\}$, deletes $v$ from $S$, and removes $c$ from $L'(u)$ for every remaining neighbour $u$ of $v$. A state is **final** if some remaining vertex has an empty list or no remaining vertex has a singleton list. The **residual instance** of a state is the induced subgraph $G[S]$ with the lists $L'$; a map $\varphi$ is a coloring of it if $\varphi(v)\in L'(v)$ for $v\in S$ and $\varphi(u)\ne\varphi(v)$ for every edge $uv$ inside $S$. The outcome of a final state is encoded as $[0]$ if an empty list was produced, and otherwise as $1$ followed, for each vertex in order, by $0$ if it was deleted or by $1$ and its current list if it remains.
--
--   **Formalization Note** The list of a deleted vertex is kept in the state; it is the singleton of the color fixed at that vertex and plays no role in the residual instance.
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 8, Lemma 3.2

import Mathlib
import Definitions.Def_KColoringFaster_ListBootstrap_Instances

open Classical

namespace KColoringFaster.ListBootstrap

/-! # The two normalization operations of Lemma 3.2 (p. 8)

**Formalization Note.**
* Rule (i) only deletes edges; the lists `L` are a fixed parameter of it. `NStep L G G'` deletes one
  edge whose endpoints have disjoint lists; `normGraph L G` deletes all of them at once.
* Rule (ii) is described on a *propagation state*: the set `S` of vertices not yet deleted and the
  current lists. One step picks a remaining vertex `v` whose list is a singleton `{c}`, deletes `v`
  and removes `c` from the lists of the remaining neighbours of `v`. The process stops when a
  remaining list is empty (no step is taken from such a state). The list of a deleted vertex is kept
  (it is the singleton of its fixed color); it plays no role in the residual instance.
* The residual instance of a state is the induced subgraph `G[S]` with the current lists on `S`;
  `IsResidualColoringOf G s φ` says that `φ`, read on `S`, is a list coloring of it. -/

/-- One application of rule (i): delete an edge `uv` with `L u ∩ L v = ∅`. -/
def NStep {n : ℕ} (L : Fin n → Finset ℕ) (G G' : SimpleGraph (Fin n)) : Prop :=
  ∃ u v, G.Adj u v ∧ Disjoint (L u) (L v) ∧ G' = G.deleteEdges {s(u, v)}

/-- The result of rule (N): every edge whose endpoints have disjoint lists is deleted. -/
def normGraph {n : ℕ} (L : Fin n → Finset ℕ) (G : SimpleGraph (Fin n)) : SimpleGraph (Fin n) :=
  G.deleteEdges {e | ∃ u v, e = s(u, v) ∧ Disjoint (L u) (L v)}

/-- A state of the singleton propagation of rule (ii): remaining vertices and current lists. -/
structure PropState (n : ℕ) where
  S : Finset (Fin n)
  L : Fin n → Finset ℕ

/-- The initial state: all vertices remain, the lists are the instance's. -/
def PropState.init {n : ℕ} (L : Fin n → Finset ℕ) : PropState n := ⟨Finset.univ, L⟩

/-- Some remaining vertex has an empty list. -/
def PropState.HasEmpty {n : ℕ} (s : PropState n) : Prop := ∃ v ∈ s.S, s.L v = ∅

/-- Some remaining vertex has a singleton list. -/
def PropState.HasSingleton {n : ℕ} (s : PropState n) : Prop := ∃ v ∈ s.S, ∃ c, s.L v = {c}

/-- One step of rule (ii) in the graph `G`: from a state with no empty list, fix a singleton
`L v = {c}` at a remaining vertex, delete `v`, and delete `c` from the lists of the remaining
neighbours of `v`. -/
def PropStep {n : ℕ} (G : SimpleGraph (Fin n)) (s t : PropState n) : Prop :=
  ¬ s.HasEmpty ∧ ∃ v ∈ s.S, ∃ c, s.L v = {c} ∧ t.S = s.S.erase v ∧
    t.L = fun u => if u ∈ s.S ∧ G.Adj v u then s.L u \ {c} else s.L u

/-- `t` is reached from `s` by exactly `m` steps of rule (ii). -/
def PropReach {n : ℕ} (G : SimpleGraph (Fin n)) (s : PropState n) : ℕ → PropState n → Prop
  | 0, t => t = s
  | m + 1, t => ∃ u, PropReach G s m u ∧ PropStep G u t

/-- The process has stopped: an empty list was produced, or no singleton list remains. -/
def PropState.IsTerminal {n : ℕ} (s : PropState n) : Prop := s.HasEmpty ∨ ¬ s.HasSingleton

/-- `φ`, read on the remaining vertices, is a list coloring of the residual instance `G[S]` with the
current lists. -/
def IsResidualColoringOf {n : ℕ} (G : SimpleGraph (Fin n)) (s : PropState n)
    (φ : Fin n → ℕ) : Prop :=
  (∀ v ∈ s.S, φ v ∈ s.L v) ∧ ∀ u ∈ s.S, ∀ v ∈ s.S, G.Adj u v → φ u ≠ φ v

/-- Output encoding of the outcome of rule (ii): `[0]` if an empty list was produced (infeasible);
otherwise `1`, then for each vertex in order `0` if it was deleted, or `1` followed by its current
list (`encFinset`) if it remains. -/
noncomputable def encOutcome {n : ℕ} (s : PropState n) : List ℤ :=
  if s.HasEmpty then [0]
  else 1 :: (List.finRange n).flatMap fun v => if v ∈ s.S then 1 :: encFinset (s.L v) else [0]

end KColoringFaster.ListBootstrap


