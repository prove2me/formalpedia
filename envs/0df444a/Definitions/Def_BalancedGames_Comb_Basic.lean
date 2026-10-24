-- Prove2me | Definitions.Def_BalancedGames_Comb_Basic
-- name    : BalancedGames_Comb_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:38.418399+00:00
-- url     : https://prove2.me/theorems/5dba206d-ed51-45fe-bf18-8654038c4c0c
-- title:
--   §2, pp. 3–4, §5.2, p. 11, §5.4, pp. 17–18 — games, G+(n), BG+(n), families 𝒟, adjacency graph, hypercube, Hamilton-connected, Definition 1
-- statement:
--   This file fixes the objects of the mission. Throughout, $N=\{1,\dots,n\}$ is the set of players and a **coalition** is a subset $S\subseteq N$.
--
--   1. **Games.** A (TU-)game is a function $v:2^N\to\mathbb R$; the games considered satisfy $v(\varnothing)=0$.
--   2. **$\mathcal G_+(n)$.** The set of games with $v(\varnothing)=0$, $v(S)\ge 0$ for every coalition $S$, and $v(N)=1$.
--   3. **Core and balancedness.** The core of $v$ is
--   $$C(v)=\{x\in\mathbb R^n : x(S)\ge v(S)\ \text{for all } S\subseteq N,\ x(N)=v(N)\},\qquad x(S)=\sum_{i\in S}x_i .$$
--   A game is **balanced** when $C(v)\neq\varnothing$ (by the Bondareva–Shapley theorem this is the balancedness condition of the paper).
--   4. **$\mathcal{BG}_+(n)$.** The balanced games of $\mathcal G_+(n)$.
--   5. **0-1-valued** vectors: every coordinate is $0$ or $1$.
--   6. **The game of a family.** For a family $\mathcal D$ of coalitions, $v_{\mathcal D}(S)=1$ if $S=N$ or $S\in\mathcal D$, and $v_{\mathcal D}(S)=0$ otherwise; $v_\varnothing=u_N=\delta_N$ is the unanimity game. Conversely, the family of a game $v$ is $\mathcal D(v)=\{S\in 2^N\setminus\{\varnothing,N\} : v(S)=1\}$.
--   7. **Polytopes and their graphs.** A polytope is the convex hull of finitely many points. Its vertices are its extreme points; two distinct vertices are **adjacent** when the segment joining them is a face (an edge). The **adjacency graph** has the vertices as nodes and the adjacent pairs as edges.
--   8. **Hypercube.** $Q_d$ is the graph on $\{0,1\}^d$ in which two vectors are adjacent when they differ in exactly one coordinate; a graph *is a hypercube* when it is isomorphic to some $Q_d$, $d\ge 0$.
--   9. **Hamilton-connected.** A graph in which any two distinct nodes are joined by a Hamiltonian path (a path through every node exactly once).
--   10. **Definition 1 (combinatorial polytope).** A polytope $P$ is combinatorial when all its vertices are 0-1-valued, and for any two distinct non-adjacent vertices $v_1,v_2$ there are two other different vertices $v_3,v_4$ (so $v_3\neq v_4$ and $v_3,v_4\notin\{v_1,v_2\}$) with
--   $$v_1+v_2=v_3+v_4 .$$
--
--   These are the objects of Theorem 12: $\mathcal{BG}_+(n)$ is a combinatorial polytope whose adjacency graph is Hamilton-connected.
--
--   **Formalization Note** Players are `Fin n` (player $i$ of the paper is $i-1$), coalitions are `Finset (Fin n)`, and a game is a vector `Finset (Fin n) → ℝ`; its $\varnothing$ coordinate is pinned to $0$ by $\mathcal G_+(n)$ (the paper works in $\mathbb R^{2^N\setminus\{\varnothing\}}$, an affine copy). The core is the published `Supermodularity.Cooperative.Core Finset.univ v`, and adjacency is the published `Hirsch.Adj`. Decidable equality on the vertex type (needed to count visits of a walk) is classical.
-- source:
--   Garcia-Segador, Grabisch, Miranda, On the set of balanced games, arXiv:2501.14341v1, pp. 3–4 (games, G+(n), core, (4)); p. 11 (family 𝒟 of a vertex); p. 12 (Theorem 9, game of a family); pp. 17–18, Definition 1; p. 21 (adjacency graph)

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_Hirsch_model

namespace BalancedGames.Comb

open Classical

/-- A TU-game on the player set `N = {0, …, n-1}` (`Fin n`; player `i` of the paper is `i - 1`):
a real number for every coalition `S ⊆ N`. The `∅` coordinate is part of the type and is pinned
to `0` by `Gplus` (p. 3: "v : 2^N → ℝ satisfying v(∅) = 0"). -/
abbrev Game (n : ℕ) := Finset (Fin n) → ℝ

/-- `G+(n)` (p. 3): games with `v(∅) = 0`, `v(S) ≥ 0` for every coalition `S`, and `v(N) = 1`. -/
def Gplus (n : ℕ) : Set (Game n) :=
  {v | v ∅ = 0 ∧ (∀ S, 0 ≤ v S) ∧ v Finset.univ = 1}

/-- A game is **balanced** when its core
`C(v) = {x ∈ ℝⁿ : x(S) ≥ v(S) ∀ S, x(N) = v(N)}` (p. 3) is nonempty
(p. 4: "the set of games having a nonempty core"; Theorem 1, Bondareva–Shapley). -/
def IsBalanced {n : ℕ} (v : Game n) : Prop :=
  (Supermodularity.Cooperative.Core Finset.univ v).Nonempty

/-- `BG+(n)` (p. 4, (4)): the balanced games of `G+(n)`. -/
def BGplus (n : ℕ) : Set (Game n) :=
  {v | v ∈ Gplus n ∧ IsBalanced v}

/-- A vector is **0-1-valued** when every coordinate is `0` or `1`. -/
def IsZeroOne {ι : Type*} (v : ι → ℝ) : Prop :=
  ∀ i, v i = 0 ∨ v i = 1

/-- The game `v_𝒟` defined by a family `𝒟` of coalitions (p. 11, Theorem 9):
`v_𝒟(S) = 1` if `S = N` or `S ∈ 𝒟`, and `v_𝒟(S) = 0` otherwise. `gameOf ∅` is the unanimity
game `u_N = δ_N` (p. 12). Theorem 9 states its own hypothesis that the members of `𝒟` are proper
nonempty coalitions. -/
noncomputable def gameOf {n : ℕ} (D : Finset (Finset (Fin n))) : Game n :=
  fun S => if S = Finset.univ ∨ S ∈ D then 1 else 0

/-- The family `𝒟` associated with a game `v` (p. 11): the coalitions
`S ∈ 2^N ∖ {∅, N}` with `v(S) = 1`. -/
noncomputable def coalitions {n : ℕ} (v : Game n) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun S => S ≠ ∅ ∧ S ≠ Finset.univ ∧ v S = 1)

/-- A **polytope**: the convex hull of a finite set of points (Minkowski–Weyl: equivalently, a
bounded polyhedron). -/
def IsPolytope {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) : Prop :=
  ∃ s : Finset E, P = convexHull ℝ (s : Set E)

/-- The **adjacency graph** of a convex set `P` (p. 21): its nodes are the vertices
(extreme points) of `P`, and two of them are joined when they are adjacent, i.e. the segment
between them is a face of `P` (`Hirsch.Adj`, p. 17: "two vertices are adjacent if they both
belong to the same edge"). -/
def adjGraph {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E) :
    SimpleGraph (Set.extremePoints ℝ P) where
  Adj u v := Hirsch.Adj P (u : E) (v : E)
  symm := ⟨fun _ _ h => ⟨fun e => h.1 e.symm, by rw [segment_symm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The hypercube graph `Q_d`: vertex set `{0,1}^d` (as `Fin d → Bool`), two vertices adjacent
when they differ in exactly one coordinate. `Q_0` is a single vertex. -/
def hypercubeGraph (d : ℕ) : SimpleGraph (Fin d → Bool) where
  Adj x y := hammingDist x y = 1
  symm := ⟨fun x y h => by rw [hammingDist_comm]; exact h⟩
  loopless := ⟨fun x h => by rw [hammingDist_self] at h; exact absurd h (by decide)⟩

/-- A graph **is a hypercube** when it is isomorphic to `Q_d` for some `d`. -/
def IsHypercube {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ d : ℕ, Nonempty (G ≃g hypercubeGraph d)

/-- A graph is **Hamilton-connected** when any two distinct vertices are joined by a Hamiltonian
path: a walk from `u` to `v` visiting every vertex exactly once. (Decidable equality on the
vertex type, needed by `Walk.IsHamiltonian`, is classical.) -/
def IsHamiltonConnected {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → ∃ p : G.Walk u v, p.IsHamiltonian

/-- **Definition 1** (p. 18, after Naddef–Pulleyblank [14]). A set `P ⊆ ℝ^ι` is
**combinatorial** when
1. all its vertices (extreme points) are 0-1-valued, and
2. for any two distinct vertices `v₁, v₂` that are not adjacent there are two other different
   vertices `v₃, v₄` (`v₃ ≠ v₄`, both outside `{v₁, v₂}`) with `v₁ + v₂ = v₃ + v₄`.
That `P` is a polytope is stated separately (`IsPolytope`). -/
def IsCombinatorial {ι : Type*} (P : Set (ι → ℝ)) : Prop :=
  (∀ v ∈ Set.extremePoints ℝ P, IsZeroOne v) ∧
  ∀ v₁ ∈ Set.extremePoints ℝ P, ∀ v₂ ∈ Set.extremePoints ℝ P, v₁ ≠ v₂ →
    ¬ Hirsch.Adj P v₁ v₂ →
    ∃ v₃ ∈ Set.extremePoints ℝ P, ∃ v₄ ∈ Set.extremePoints ℝ P,
      v₃ ≠ v₄ ∧ v₃ ≠ v₁ ∧ v₃ ≠ v₂ ∧ v₄ ≠ v₁ ∧ v₄ ≠ v₂ ∧ v₁ + v₂ = v₃ + v₄

end BalancedGames.Comb


