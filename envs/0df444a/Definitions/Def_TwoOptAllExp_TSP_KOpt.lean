-- Prove2me | Definitions.Def_TwoOptAllExp_TSP_KOpt
-- name    : TwoOptAllExp_TSP_KOpt
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:59:51.059701+00:00
-- url     : https://prove2.me/theorems/e2b3c454-06f5-4785-af75-4dece008255c
-- title:
--   Tours as edge sets, $k$-swaps and the TSP with the $k$-opt neighborhood
-- statement:
--   A **tour** of a graph $G$ is a Hamiltonian cycle of $G$, recorded here by its edge set. The **weight** of an edge set is the sum of the weights of its edges.
--
--   For two edge sets $\tau,\sigma$, the tour $\sigma$ is obtained from $\tau$ by a **$k$-swap** if there are edge sets $E_1,E_2$ with $|E_1|=|E_2|\le k$ and $E_1\subseteq\tau$ such that $\sigma=(\tau\setminus E_1)\cup E_2$.
--
--   The **TSP with the $k$-opt neighborhood on $G$ with weights $c$** has the tours of $G$ as its solutions and the tour weight as its objective, to be minimized; the neighbors of a tour are the tours obtained from it by a $k$-swap.
--
--   A **TSP instance** is a complete graph on $N$ vertices with a weight $c(e)\in\mathbb N$ on every edge. Its **size** is
--   $$N+\sum_{e}\bigl(\mathrm{bitlength}(c(e))+1\bigr),$$
--   the sum running over all $\binom N2$ edges, so that every weight of the complete graph counts with its binary length. The local-search problem **TSP with the $k$-opt neighborhood** has these instances.
--
--   **Formalization Note** The vertices of an instance are `Fin N`, and a weight function is a function on `Sym2 (Fin N)` whose values on the diagonal are not edge weights: they enter neither a tour weight nor the size. A tour has at least three vertices, so an instance with $N<3$ has no tours. A swap with $E_1=E_2=\emptyset$ gives the tour itself, which is not an improving move.
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, §2.2, p. 7

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_LocalSearch

namespace TwoOptAllExp.TSP

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `H` is (the edge set of) a tour of the graph `G`: a Hamiltonian cycle of `G` (§2.2, p. 7). -/
def IsTourOf (G : SimpleGraph V) (H : Finset (Sym2 V)) : Prop :=
  ∃ (v : V) (w : G.Walk v v), w.IsHamiltonianCycle ∧ w.edges.toFinset = H

/-- The weight of an edge set, the sum of the edge weights (§2.2, p. 7). -/
def edgeSetWeight (c : Sym2 V → ℕ) (H : Finset (Sym2 V)) : ℕ :=
  ∑ e ∈ H, c e

/-- `σ` is obtained from `τ` by a `k`-swap `(E₁, E₂)` (§2.2, p. 7): `|E₁| = |E₂| ≤ k`, `E₁ ⊆ τ`, and
`σ` is `τ` with `E₁` removed and `E₂` added. -/
def IsKSwap (k : ℕ) (τ σ : Finset (Sym2 V)) : Prop :=
  ∃ E₁ E₂ : Finset (Sym2 V), E₁.card = E₂.card ∧ E₁.card ≤ k ∧ E₁ ⊆ τ ∧ σ = (τ \ E₁) ∪ E₂

/-- The search space of the TSP with the `k`-opt neighborhood on the graph `G` with weights `c`
(§2.2, p. 7): the solutions are the tours of `G`, the objective is the tour weight and is
minimized, and the neighbors of a tour `τ` are the tours obtained from `τ` by a `k`-swap. -/
def tspSpace (k : ℕ) (G : SimpleGraph V) (c : Sym2 V → ℕ) : SearchSpace where
  Sol := {H : Finset (Sym2 V) // IsTourOf G H}
  sol_finite := inferInstance
  obj := fun τ => (edgeSetWeight c τ.1 : ℤ)
  Nbr := fun τ => {σ | IsKSwap k τ.1 σ.1}
  minimize := true

/-- A TSP instance (§2.2, p. 7): the complete undirected graph on `N` vertices with a weight
`c e ∈ ℕ` on every edge. The values of `c` on the diagonal of `Sym2 (Fin N)` are not edge weights;
they enter neither a tour weight nor the size. -/
structure TSPInstance where
  /-- The number of vertices. -/
  N : ℕ
  /-- The edge weights. -/
  c : Sym2 (Fin N) → ℕ

/-- The binary encoding size of a TSP instance: the number of vertices plus, for each of the
`N(N-1)/2` edges of the complete graph, the bit length of its weight plus one. -/
def TSPInstance.size (I : TSPInstance) : ℕ :=
  I.N + ∑ e ∈ (Finset.univ : Finset (Sym2 (Fin I.N))).filter (fun e => ¬ e.IsDiag),
    (Nat.size (I.c e) + 1)

/-- The local-search problem TSP with the `k`-opt neighborhood (§2.2, p. 7). -/
def tspKOpt (k : ℕ) : LocalSearchProblem where
  Inst := TSPInstance
  size := TSPInstance.size
  space := fun I => tspSpace k (⊤ : SimpleGraph (Fin I.N)) I.c

end TwoOptAllExp.TSP


