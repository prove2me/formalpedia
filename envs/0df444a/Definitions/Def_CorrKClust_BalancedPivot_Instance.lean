-- Prove2me | Definitions.Def_CorrKClust_BalancedPivot_Instance
-- name    : CorrKClust_BalancedPivot_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:43:19.815818+00:00
-- url     : https://prove2.me/theorems/f6782278-714c-4e68-8df7-a2f964ab78c6
-- title:
--   Finite graphs, clusterings, disagreement costs and optima
-- statement:
--   A finite simple graph $G=(V,E)$ records positive pairs as edges and negative pairs as non-edges. A clustering is a map $f:V\to L$ to cluster labels. Each unordered pair of distinct vertices contributes one disagreement exactly when its adjacency disagrees with equality of its cluster labels:
--   $$\operatorname{Cost}_G(f)=\#\{\{u,v\}:u\ne v,\ (uv\in E\land f(u)\ne f(v))\lor(uv\notin E\land f(u)=f(v))\}.$$
--   For positive $k$, $\operatorname{OPT}_k(G)$ is the minimum over all maps $V\to\{0,\ldots,k-1\}$. Empty clusters are allowed. The unconstrained optimum $\operatorname{OPT}_{CC}(G)$ is the minimum over all maps $V\to V$. The module also gives the nonempty blocks and their size multiset, the predicate that a graph is a union of exactly those cliques, the graph obtained by completing each block and deleting crossing edges, and the unordered counts $e_m,e_c$ of missing within-block edges and crossing edges.
--
--   These are the shared objective and partition interfaces for the entire mission. Natural-number infima are taken over nonempty sets whenever used: a constant k-label assignment exists for $k>0$, and the identity map exists for unconstrained clustering, even when $V$ is empty.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), §2; Definition 7.1; §7.3.4, pp. 6–43, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/302.pdf

import Mathlib

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot

/-- §2, p. 6: an instance is an arbitrary finite simple positive graph. -/
abbrev Instance (V : Type*) := SimpleGraph V

/-- Count unordered distinct pairs once. -/
def pairCount {V : Type*} [Fintype V] (P : V → V → Prop) : ℕ :=
  ((Finset.univ : Finset (Sym2 V)).filter
    (fun e => ∃ u v, e = s(u, v) ∧ u ≠ v ∧ P u v)).card

/-- §2: disagreement cost of an arbitrary labelled partition. -/
def cost {V L : Type*} [Fintype V] (G : SimpleGraph V) (f : V → L) : ℕ :=
  pairCount (fun u v => (G.Adj u v ∧ f u ≠ f v) ∨ (¬ G.Adj u v ∧ f u = f v))

/-- Minimum over ALL assignments to k labels; used only with k ≥ 1. -/
def optK {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : ℕ :=
  sInf {a : ℕ | ∃ f : V → Fin k, cost G f = a}

/-- Unrestricted optimum, including the empty vertex type. Every partition has vertex labels. -/
def optCC {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sInf {a : ℕ | ∃ f : V → V, cost G f = a}

/-- Nonempty blocks of a labelled partition, independent of unused labels. -/
def blocks {V L : Type*} [Fintype V] (f : V → L) : Finset (Finset V) :=
  Finset.univ.image (fun v => Finset.univ.filter (fun u => f u = f v))

def blockSizes {V L : Type*} [Fintype V] (f : V → L) : Multiset ℕ :=
  (blocks f).val.map Finset.card

/-- The graph consists exactly of the disjoint nonempty blocks of Q. -/
def IsCliquePartition {V : Type*} (G : SimpleGraph V) (Q : V → V) : Prop :=
  ∀ u v, u ≠ v → (G.Adj u v ↔ Q u = Q v)

/-- Definition 7.1: add inside edges, delete crossing edges, for the given partition. -/
def cliqueGraph {V L : Type*} (Q : V → L) : SimpleGraph V where
  Adj u v := u ≠ v ∧ Q u = Q v
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

def missingEdges {V L : Type*} [Fintype V] (G : SimpleGraph V) (Q : V → L) : ℕ :=
  pairCount (fun u v => Q u = Q v ∧ ¬ G.Adj u v)

def crossingEdges {V L : Type*} [Fintype V] (G : SimpleGraph V) (Q : V → L) : ℕ :=
  pairCount (fun u v => Q u ≠ Q v ∧ G.Adj u v)

end CorrKClust.BalancedPivot


