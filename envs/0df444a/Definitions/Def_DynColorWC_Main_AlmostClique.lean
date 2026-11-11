-- Prove2me | Definitions.Def_DynColorWC_Main_AlmostClique
-- name    : DynColorWC_Main_AlmostClique
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:46:22.523511+00:00
-- url     : https://prove2.me/theorems/df18145b-27e2-488b-aeb7-58f70f150deb
-- title:
--   Sparsity, ε-almost-cliques, anti- and external neighborhoods, z(C), z̃(v), ε-friends and ε-connected sets
-- statement:
--   Let $G$ be a graph with degree bound $\Delta$. A vertex $v$ is **$z$-sparse** (Definition 3.1) if $G[N(v)]$ has at most $\binom{\Delta}{2}-z\Delta$ edges; the sparsity of $v$ is the largest such $z$, i.e. $\big(\binom\Delta2-e(G[N(v)])\big)/\Delta$ (the published `DynBrooks.sparsity`). A set $C$ is an **$\varepsilon$-almost-clique** (Definition 3.2) if $|C|\le(1+\varepsilon)\Delta$ and every $v\in C$ has at least $(1-\varepsilon)\Delta$ neighbors in $C$. For a vertex $v$ with cluster $C$: the **anti-neighborhood** $A(v)=C\setminus N[v]$ and the **external neighborhood** $E(v)=N(v)\setminus C$, and
--   $$z(C)=\max\{0,\Delta-|C|\}+\frac1{|C|}\sum_{v\in C}\big(|A(v)|+|E(v)|\big),\qquad \tilde z(v)=\max\{0,\Delta-|C|\}+|A(v)|+|E(v)|.$$
--   Two vertices $u,v$ are **$\varepsilon$-friends** (Definition 4.6) if $|N(u)\cap N(v)|\ge(1-\varepsilon)\Delta$; $F_\varepsilon(v)$ is the set of neighbors of $v$ that are its $\varepsilon$-friends, and $V_\varepsilon=\{v:|F_\varepsilon(v)|\ge(1-\varepsilon)\Delta\}$. A set $S\subseteq V_\varepsilon$ is **$\varepsilon$-connected** (Definition 4.8) if every pair $u,v\in S$ is joined by a path in $G[V_\varepsilon]$ all of whose edges join $\varepsilon$-friends.
--
--   **Formalization Note.** "$z$-sparse" is the inequality on the published `DynBrooks.nbrEdges`, so $\Delta=0$ needs no case. $z(\emptyset)$ is undefined in the paper; Lean's $1/0=0$ gives $\max\{0,\Delta\}$, and every statement that uses $z(C)$ for a cluster that may be empty says so. $\varepsilon$-connectivity is reachability in the graph of $\varepsilon$-friendly edges of $G[V_\varepsilon]$ (a walk contains a path).
-- source:
--   Flin and Ghaffari (2026), Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time, STOC 2027 submission, supplied PDF sha256 93ebb2ffd4839b5e525b4550a6569cf5234550ee4a44351aedab3ea3154300e3, Definitions 3.1 and 3.2 and §3.1, pp. 13–14 (PDF 15–16); Eq. (1), p. 18 (PDF 20); Definitions 4.6 and 4.8, pp. 18–19 (PDF 20–21)

import Mathlib
import Definitions.Def_DynBrooks_Sparsity

namespace DynColorWC.Main

/-! # Sparsity, almost-cliques, anti- and external neighborhoods, ε-friends

Flin and Ghaffari (2026), *Dynamic (Δ+1)-Coloring with Polylogarithmic Worst-Case Update Time*,
STOC 2027 submission, supplied PDF sha256 93ebb2ff…3154300e3: Definitions 3.1 and 3.2 and the
quantity `z(C)` of §3.1, pp. 13–14 (PDF 15–16); `z̃(v)` of Eq. (1), p. 18 (PDF 20);
Definitions 4.6 and 4.8, pp. 18–19 (PDF 20–21).

* `Δ` is the degree bound of the (dynamic) graph, not its current maximum degree.
* `v` is **`z`-sparse** (Definition 3.1) when `G[N(v)]` has at most `C(Δ,2) − zΔ` edges. The edge
  count is the published `DynBrooks.nbrEdges`; the sparsity of `v` (the largest such `z`) is the
  published `DynBrooks.sparsity Δ G v = (C(Δ,2) − nbrEdges G v)/Δ`. "`z`-sparse" is stated as the
  inequality, so `Δ = 0` needs no case.
* For a vertex set `C` (the cluster of `v`): `A(v) = C \ N[v]`, `E(v) = N(v) \ C`.
* `z(C) = max{0, Δ − |C|} + (1/|C|) Σ_{v∈C} (|A(v)| + |E(v)|)`; for `C = ∅` the paper leaves it
  undefined and Lean's `1/0 = 0` gives `max{0, Δ}`. `z̃(v) = max{0, Δ − |C|} + |A(v)| + |E(v)|`. -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Definition 3.1: `v` is `z`-sparse in `G` (relative to the degree bound `Δ`): `G[N(v)]` has at most
`C(Δ,2) − zΔ` edges. -/
noncomputable def IsSparse (Δ : ℕ) (G : SimpleGraph V) (v : V) (z : ℝ) : Prop :=
  (DynBrooks.nbrEdges G v : ℝ) ≤ (Δ.choose 2 : ℝ) - z * Δ

open Classical in
/-- Definition 3.2: `C` is an `ε`-almost-clique: `|C| ≤ (1+ε)Δ`, and every `v ∈ C` has at least
`(1−ε)Δ` neighbors in `C`. -/
def IsAlmostClique (ε : ℝ) (Δ : ℕ) (G : SimpleGraph V) (C : Finset V) : Prop :=
  (C.card : ℝ) ≤ (1 + ε) * Δ ∧ ∀ v ∈ C, (1 - ε) * (Δ : ℝ) ≤ ((G.neighborFinset v ∩ C).card : ℝ)

open Classical in
/-- The anti-neighborhood `A(v) = C \ N[v]` of `v` with respect to the vertex set `C`. -/
noncomputable def antiNbhd (G : SimpleGraph V) (C : Finset V) (v : V) : Finset V :=
  C \ insert v (G.neighborFinset v)

open Classical in
/-- The external neighborhood `E(v) = N(v) \ C` of `v` with respect to the vertex set `C`. -/
noncomputable def extNbhd (G : SimpleGraph V) (C : Finset V) (v : V) : Finset V :=
  G.neighborFinset v \ C

/-- `z(C) = max{0, Δ − |C|} + (1/|C|) Σ_{v∈C} (|A(v)| + |E(v)|)` (§3.1, p. 14). -/
noncomputable def zC (Δ : ℕ) (G : SimpleGraph V) (C : Finset V) : ℝ :=
  max 0 ((Δ : ℝ) - C.card) +
    (1 / (C.card : ℝ)) * ∑ v ∈ C, (((antiNbhd G C v).card : ℝ) + (extNbhd G C v).card)

/-- `z̃(v) = max{0, Δ − |C|} + |A(v)| + |E(v)|` for `v` with cluster `C` (Eq. (1), p. 18). -/
noncomputable def zTilde (Δ : ℕ) (G : SimpleGraph V) (C : Finset V) (v : V) : ℝ :=
  max 0 ((Δ : ℝ) - C.card) + (antiNbhd G C v).card + (extNbhd G C v).card

open Classical in
/-- Definition 4.6: `u` and `v` are `ε`-friends: `|N(u) ∩ N(v)| ≥ (1−ε)Δ`. -/
def AreFriends (ε : ℝ) (Δ : ℕ) (G : SimpleGraph V) (u v : V) : Prop :=
  (1 - ε) * (Δ : ℝ) ≤ ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ)

open Classical in
/-- Definition 4.6: `F_ε(v)`, the neighbors of `v` that are `ε`-friends of `v`. -/
noncomputable def friendSet (ε : ℝ) (Δ : ℕ) (G : SimpleGraph V) (v : V) : Finset V :=
  (G.neighborFinset v).filter fun u => AreFriends ε Δ G u v

open Classical in
/-- Definition 4.6: `V_ε = {v : |F_ε(v)| ≥ (1−ε)Δ}`. -/
noncomputable def Veps (ε : ℝ) (Δ : ℕ) (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter fun v => (1 - ε) * (Δ : ℝ) ≤ ((friendSet ε Δ G v).card : ℝ)

/-- The graph of `ε`-friendly edges of `G[V_ε]`: edges of `G` with both endpoints in `V_ε` whose
endpoints are `ε`-friends. -/
def friendlyGraph (ε : ℝ) (Δ : ℕ) (G : SimpleGraph V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ Veps ε Δ G ∧ y ∈ Veps ε Δ G ∧ AreFriends ε Δ G x y
  symm := by
    constructor
    intro x y h
    refine ⟨h.1.symm, h.2.2.1, h.2.1, ?_⟩
    have := h.2.2.2
    unfold AreFriends at *
    rwa [Finset.inter_comm]
  loopless := by
    constructor
    intro x h
    exact G.irrefl h.1

/-- Definition 4.8: `S ⊆ V_ε` is `ε`-connected: every pair `u, v ∈ S` is joined by a path in
`G[V_ε]` all of whose edges are `ε`-friendly (a walk in `friendlyGraph`; a walk contains a path). -/
def IsEpsConnected (ε : ℝ) (Δ : ℕ) (G : SimpleGraph V) (S : Finset V) : Prop :=
  S ⊆ Veps ε Δ G ∧ ∀ u ∈ S, ∀ v ∈ S, (friendlyGraph ε Δ G).Reachable u v

end DynColorWC.Main


