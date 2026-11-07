-- Prove2me | Definitions.Def_HyperCheeger_Hypergraph
-- name    : HyperCheeger_Hypergraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:59.239207+00:00
-- url     : https://prove2.me/theorems/09939450-b394-433b-b16d-52428c4e5a18
-- title:
--   Weighted hypergraph, degree $d_H$, volume, rank $\Upsilon_H$, connectedness, 2-graphs
-- statement:
--   A **hypergraph** is a triple $H=(V_H,E_H,w_H)$: a finite vertex set $V_H$, a set of hyperedges $E_H\subseteq 2^{V_H}$ with no hyperedge of size one, and a weight $w_H(e)\in[0,\infty)$ on each hyperedge. From these,
--
--   1. the **degree** of $u$ is $d_H(u)=\sum_{e\in E_H:\,u\in e}w_H(e)$;
--   2. the **volume** of $S\subseteq V_H$ is $\mathrm{vol}_H(S)=\sum_{v\in S}d_H(v)$;
--   3. the **rank** $\Upsilon_H$ is the maximum cardinality of a hyperedge;
--   4. $H$ is **connected** if for all $u,v\in V_H$ there are hyperedges $e_1,\dots,e_\ell$ with $\ell\ge1$, $u\in e_1$, $v\in e_\ell$ and $e_i\cap e_{i+1}\ne\emptyset$ for $1\le i<\ell$;
--   5. $H$ is a **2-graph** if every hyperedge has size two.
--
--   All later objects of the mission are built on this structure, and a 2-graph is the same structure, so no separate graph layer is needed.
--
--   **Formalization Note.** The weight is a total function on subsets and only its values on $E_H$ are read. Weights may vanish: a zero-weight hyperedge still counts for connectedness and for the rank. The empty hyperedge is not excluded, as on the page, and it enters no sum.
-- source:
--   Kamal, Bagchi, A Cheeger Inequality for Hypergraphs and Its Applications, STOC 2027 submission, arXiv:2609.16286 (manuscript sha256 e0942b89…), §3.1, p.6

import Mathlib

namespace HyperCheeger

/-- A **hypergraph** `H = (V_H, E_H, w_H)`: a finite vertex type `V`, a set of hyperedges
`E_H ⊆ 2^V`, no hyperedge of size one, and a weight in `[0, ∞)` on each hyperedge.

Kamal, Bagchi, *A Cheeger Inequality for Hypergraphs and Its Applications*, STOC 2027 submission,
arXiv:2609.16286 (manuscript sha256 e0942b89…), §3.1, p.6.

**Formalization Note.** `edges` is a `Finset`, so there are no parallel hyperedges, as printed.
The weight `w` is total on `Finset V`, and only its values on `edges` are ever read. The empty
hyperedge is allowed (the page bans only size one); no vertex lies in it, so it contributes to no
degree, boundary or pair sum. Weights may vanish: no positivity of weights or degrees is assumed. -/
structure Hypergraph (V : Type) where
  /-- The hyperedge set `E_H`. -/
  edges : Finset (Finset V)
  /-- The weight function; only its values on `edges` are read. -/
  w : Finset V → ℝ
  /-- `w_H : E_H → [0, ∞)`. -/
  w_nonneg : ∀ e ∈ edges, 0 ≤ w e
  /-- No hyperedges of size one. -/
  card_ne_one : ∀ e ∈ edges, e.card ≠ 1

namespace Hypergraph

variable {V : Type} [DecidableEq V]

/-- The degree `d_H(u)`: the sum of the weights of all hyperedges containing `u` (§3.1, p.6). -/
noncomputable def degree (H : Hypergraph V) (u : V) : ℝ :=
  ∑ e ∈ H.edges with u ∈ e, H.w e

/-- The volume `vol_H(S) = ∑_{v ∈ S} d_H(v)` (§3.1, p.6). -/
noncomputable def vol (H : Hypergraph V) (S : Finset V) : ℝ :=
  ∑ v ∈ S, H.degree v

/-- The rank `Υ_H`: the maximum cardinality of a hyperedge (§3.1, p.6). A zero-weight hyperedge
still counts. -/
def rank (H : Hypergraph V) : ℕ :=
  H.edges.sup Finset.card

/-- `H` is **connected**: for all `u, v ∈ V` (including `u = v`) there is a sequence of hyperedges
`e_1, …, e_ℓ`, `ℓ ≥ 1`, with `u ∈ e_1`, `v ∈ e_ℓ` and `e_i ∩ e_{i+1} ≠ ∅` for `1 ≤ i < ℓ`
(§3.1, p.6). Weights play no role. The sequence is indexed from `1`, as on the page. -/
def IsConnected (H : Hypergraph V) : Prop :=
  ∀ u v : V, ∃ (ℓ : ℕ) (e : ℕ → Finset V), 1 ≤ ℓ ∧ (∀ i, 1 ≤ i → i ≤ ℓ → e i ∈ H.edges) ∧
    u ∈ e 1 ∧ v ∈ e ℓ ∧ ∀ i, 1 ≤ i → i < ℓ → (e i ∩ e (i + 1)).Nonempty

/-- `H` is a **2-graph**: every hyperedge has size two, i.e. `Υ_H = κ_H = 2` (§3.1, p.6).
The paper's `φ_g`, `∂_g` for a 2-graph are `φ_h`, `∂_h` on such a hypergraph. -/
def IsTwoGraph (H : Hypergraph V) : Prop :=
  ∀ e ∈ H.edges, e.card = 2

end Hypergraph

end HyperCheeger


