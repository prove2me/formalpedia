-- Prove2me | Definitions.Def_LPCommunity_MinBisect_Setting
-- name    : LPCommunity_MinBisect_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:11.716869+00:00
-- url     : https://prove2.me/theorems/29559d8b-a2fb-440d-b175-0ef0f9cfecf7
-- title:
--   §2, pp. 3–5 — bisections, the planted bisection, d_in, d_out, cut cost, minimum-bisection recovery and the edge sets R, S, T
-- statement:
--   Let $G=(V,E)$ be a simple graph on the vertex set $V=\{1,\dots,n\}$. A **bisection** of $V$ is a partition of $V$ into two sets of equal cardinality $n/2$; it exists only when $n$ is even. A bisection is recorded by one of its two sides $V_1$, the other side being $V_2 = V\setminus V_1$. The **cost** of the bisection is the number of edges with one end in each side,
--   $$\operatorname{cut}_G(V_1) = \bigl|\{(i,j)\in E : i<j,\ i,j \text{ on different sides}\}\bigr|,$$
--   and the **minimum bisection problem** asks for a bisection of minimum cost.
--
--   A fixed, **planted** bisection $V_1, V_2$ is given. Write $G[V_1]$, $G[V_2]$ for the induced subgraphs and $G_0=(V,E_0)$ with $E_0 = E\setminus(E(G[V_1])\cup E(G[V_2]))$ for the bipartite graph of edges across. Then
--
--   1. $d_{\mathrm{in}}$ is the minimum degree of the nodes of $G[V_1]\cup G[V_2]$, i.e. the minimum over $v\in V$ of the number of neighbours of $v$ on its own side;
--   2. $d_{\mathrm{out}}$ is the maximum degree of the nodes of $G_0$, i.e. the maximum over $v$ of the number of neighbours of $v$ on the other side.
--
--   The minimum bisection problem **recovers the planted bisection** if its unique optimal solution corresponds to the planted bisection: every bisection whose cost is at most $\operatorname{cut}_G(V_1)$ is the partition $\{V_1,V_2\}$ itself, i.e. its recorded side is $V_1$ or $V_2$.
--
--   For the proof of Theorem 1 the paper compares the planted bisection with a second bisection $\tilde V_1, \tilde V_2$ and sets $U_1 = V_1\cap\tilde V_1$, $U_2 = V_2\cap \tilde V_2$, $W_1 = V_1\cap\tilde V_2$, $W_2 = V_2\cap\tilde V_1$. For disjoint vertex sets $A, B$, let $e(A,B)$ be the number of edges with one endnode in $A$ and one in $B$. The edge sets $R_1, R_2, S_1, S_2, T_1, T_2$ of p. 5 have cardinalities
--   $$|R| = e(U_1,W_2)+e(W_1,U_2),\quad |S| = e(U_1,W_1)+e(U_2,W_2),\quad |T| = e(U_1,U_2)+e(W_1,W_2),$$
--   where $R = R_1\cup R_2$, $S = S_1\cup S_2$, $T = T_1\cup T_2$.
--
--   These are the objects of §2 of the paper; Theorem 1 and the three steps of its proof are stated in terms of them.
--
--   **Formalization Note** The vertex set is `Fin n` (0-based). A bisection is a `Finset` `V1` with `2 * V1.card = n`; the second side is `V1ᶜ`, and the paper's $\tilde V_1$ is a second bisection `W` (so $\tilde V_2$ = `Wᶜ`). `dIn` is `0` when $n=0$ (empty minimum); `dOut` is the `Finset.sup` over all vertices. Since the four sets $U_1,U_2,W_1,W_2$ are pairwise disjoint, the six edge sets are pairwise disjoint and $|R| = |R_1|+|R_2|$ etc., which is how `Rcard`, `Scard`, `Tcard` are defined. Recovery is stated for unordered partitions (`S = V1 ∨ S = V1ᶜ`), because $V_1$ and $V_2$ have the same cost.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, pp. 3–5, §2 (bisection, cost, planted bisection, recovery, d_in, d_out) and §2.1, proof of Theorem 1 (U1, U2, W1, W2, R1, R2, S1, S2, T1, T2)

import Mathlib

namespace LPCommunity.MinBisect

open Finset
open scoped Classical

/-- §2, p. 3: a bisection of `V = Fin n` (the paper's `{1, …, n}`, here 0-based) is a set
`V1` with `|V1| = n / 2`; the other side is `V1ᶜ`. -/
def IsBisection (n : ℕ) (S : Finset (Fin n)) : Prop := 2 * S.card = n

/-- `i` and `j` lie on the same side of the partition `V1, V1ᶜ`. -/
def sameSide {n : ℕ} (V1 : Finset (Fin n)) (i j : Fin n) : Prop := (i ∈ V1 ↔ j ∈ V1)

/-- Degree of `v` in `G[V1] ∪ G[V2]`: neighbours of `v` on the same side as `v`. -/
noncomputable def inDeg {n : ℕ} (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n)) (v : Fin n) : ℕ :=
  (univ.filter fun u => G.Adj v u ∧ sameSide V1 v u).card

/-- Degree of `v` in `G0 = (V, E0)`, `E0 = E \ (E1 ∪ E2)`: neighbours on the other side. -/
noncomputable def outDeg {n : ℕ} (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n)) (v : Fin n) : ℕ :=
  (univ.filter fun u => G.Adj v u ∧ ¬ sameSide V1 v u).card

/-- §2, p. 4: `d_in`, the minimum degree of the nodes of `G[V1] ∪ G[V2]` (`0` when `n = 0`). -/
noncomputable def dIn {n : ℕ} (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n)) : ℕ :=
  if h : (univ : Finset (Fin n)).Nonempty then univ.inf' h (inDeg G V1) else 0

/-- §2, p. 4: `d_out`, the maximum degree of the nodes of `G0`. -/
noncomputable def dOut {n : ℕ} (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n)) : ℕ :=
  univ.sup (outDeg G V1)

/-- §2, p. 3: the cost of the partition `S, Sᶜ`, the number of edges `(i, j)`, `i < j`,
connecting the two sets. -/
noncomputable def cutCost {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ :=
  (univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ ¬ sameSide S p.1 p.2).card

/-- §2, p. 4: the minimum bisection problem recovers the planted bisection `V1, V1ᶜ`: every
bisection of cost at most that of `V1` is the same unordered partition, i.e. the unique optimal
solution corresponds to the planted bisection. -/
def MinBisectRecovers {n : ℕ} (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), IsBisection n S → cutCost G S ≤ cutCost G V1 → S = V1 ∨ S = V1ᶜ

/-- Number of edges `(i, j)`, `i < j`, with one endnode in `A` and one endnode in `B`
(for disjoint `A`, `B`). -/
noncomputable def edgesBetween {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)) : ℕ :=
  (univ.filter fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ ((p.1 ∈ A ∧ p.2 ∈ B) ∨ (p.1 ∈ B ∧ p.2 ∈ A))).card

/-- §2.1, p. 4, with `W` the paper's `Ṽ1` (so `Ṽ2 = Wᶜ`): `U1 := V1 ∩ Ṽ1`. -/
def U1 {n : ℕ} (V1 W : Finset (Fin n)) : Finset (Fin n) := V1 ∩ W

/-- `U2 := V2 ∩ Ṽ2`. -/
def U2 {n : ℕ} (V1 W : Finset (Fin n)) : Finset (Fin n) := V1ᶜ \ W

/-- `W1 := V1 ∩ Ṽ2`. -/
def W1 {n : ℕ} (V1 W : Finset (Fin n)) : Finset (Fin n) := V1 \ W

/-- `W2 := V2 ∩ Ṽ1`. -/
def W2 {n : ℕ} (V1 W : Finset (Fin n)) : Finset (Fin n) := V1ᶜ ∩ W

/-- §2.1, p. 5: `|R| = |R1| + |R2|`, `R1` the edges between `U1` and `W2`, `R2` between `W1`
and `U2`. -/
noncomputable def Rcard {n : ℕ} (G : SimpleGraph (Fin n)) (V1 W : Finset (Fin n)) : ℕ :=
  edgesBetween G (U1 V1 W) (W2 V1 W) + edgesBetween G (W1 V1 W) (U2 V1 W)

/-- §2.1, p. 5: `|S| = |S1| + |S2|`, `S1` the edges between `U1` and `W1`, `S2` between `U2`
and `W2`. -/
noncomputable def Scard {n : ℕ} (G : SimpleGraph (Fin n)) (V1 W : Finset (Fin n)) : ℕ :=
  edgesBetween G (U1 V1 W) (W1 V1 W) + edgesBetween G (U2 V1 W) (W2 V1 W)

/-- §2.1, p. 5: `|T| = |T1| + |T2|`, `T1` the edges between `U1` and `U2`, `T2` between `W1`
and `W2`. -/
noncomputable def Tcard {n : ℕ} (G : SimpleGraph (Fin n)) (V1 W : Finset (Fin n)) : ℕ :=
  edgesBetween G (U1 V1 W) (U2 V1 W) + edgesBetween G (W1 V1 W) (W2 V1 W)

end LPCommunity.MinBisect


