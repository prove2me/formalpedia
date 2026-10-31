-- Prove2me | Definitions.Def_SplitPMSGame_IsCoreAlloc
-- name    : SplitPMSGame_IsCoreAlloc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:32.373841+00:00
-- url     : https://prove2.me/theorems/7dcada62-ff4c-4325-ba16-be0f895d91c7
-- title:
--   Core allocation, core and total balancedness of a cost game
-- statement:
--   Let $M$ be a set of players and $G:2^M\to\mathbb R$ the characteristic function of a cooperative **cost** game. For a coalition $S\subseteq M$, a cost allocation vector $x\in\mathbb R^M$ is a **core allocation of the subgame** $(S,G)$ when it is efficient and coalitionally rational:
--   $$
--   \sum_{i\in S}x_i=G(S),\qquad \sum_{i\in T}x_i\le G(T)\quad\text{for every }T\subseteq S.
--   $$
--   The **core** $\mathbb C(M,G)$ is the set of core allocations of the grand coalition $M$. The game is **balanced** when its core is nonempty, and **totally balanced** when the core of every subgame $(S,G)$, $S\subseteq M$, is nonempty.
--
--   These are the notions in which the mission's goal is stated: total balancedness of the parallel machines scheduling game.
--
--   **Formalization Note** The constraints are $\le$ (cost game). The vector $x$ is indexed by all of $M$; only its coordinates in $S$ are constrained. At $S=\emptyset$ total balancedness requires $G(\emptyset)=0$, which holds for every game of the paper.
-- source:
--   Alon, Anily, The Basic Core of a Parallel Machines Scheduling Game, MSOM 25(6) (2023), doi:10.1287/msom.2021.0337, §3, pp.2236–2237 (PDF pp.5–6)

import Mathlib

namespace SplitPMSGame

/-- **Core allocation of a subgame of a cost game** (Alon, Anily, *The Basic Core of a Parallel
Machines Scheduling Game*, MSOM 25(6) (2023), §3, pp.2236–2237). For a cooperative cost game
`(M, G)` with characteristic function `G : 2^M → ℝ` and a coalition `S ⊆ M`, the cost allocation
vector `x` lies in the core of the subgame `(S, G)` when it is efficient, `∑_{i∈S} xᵢ = G(S)`,
and satisfies coalitional rationality, `∑_{i∈T} xᵢ ≤ G(T)` for every `T ⊆ S`.

**Formalization Note** This is a *cost* game: the rationality constraints are `≤`. The vector
`x` is defined on all of `M`; only its coordinates in `S` are constrained. The constraint at
`T = S` is implied by efficiency and the one at `T = ∅` reads `0 ≤ G(∅)`, which holds for the
paper's games (`G(∅) = 0`). -/
def IsCoreAlloc {M : Type*} (G : Finset M → ℝ) (S : Finset M) (x : M → ℝ) : Prop :=
  ∑ i ∈ S, x i = G S ∧ ∀ T ⊆ S, ∑ i ∈ T, x i ≤ G T

/-- **The core** `ℂ(M, G)` of a cost game `(M, G)` (MSOM 2023, §3, p.2237, after Gillies 1953):
the efficient cost allocation vectors `x` (`∑_{i∈M} xᵢ = G(M)`) with `∑_{i∈S} xᵢ ≤ G(S)` for
every coalition `S ⊆ M`. -/
def coreSet {M : Type*} [Fintype M] (G : Finset M → ℝ) : Set (M → ℝ) :=
  {x | IsCoreAlloc G Finset.univ x}

/-- **Totally balanced cost game** (MSOM 2023, §3, p.2237): "A cooperative game whose core is
nonempty is said to be balanced, and if its core and the cores of all its subgames are
nonempty, the game is totally balanced." For every coalition `S ⊆ M` the subgame `(S, G)`
has a core allocation.

**Formalization Note** The quantifier ranges over every coalition `S`, including `M` itself
(balancedness) and `∅`, where the condition reads `G(∅) = 0`, as for every game of the paper. -/
def TotallyBalanced {M : Type*} (G : Finset M → ℝ) : Prop :=
  ∀ S : Finset M, ∃ x : M → ℝ, IsCoreAlloc G S x

end SplitPMSGame


