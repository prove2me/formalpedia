-- Prove2me | Definitions.Def_LPCommunity_SBMRecovery_Factors
-- name    : LPCommunity_SBMRecovery_Factors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:49.475005+00:00
-- url     : https://prove2.me/theorems/647eac1c-e968-413d-8840-8635094ce7ec
-- title:
--   §5.1–§5.2 — b-factors, N(U, U′), minimum and maximum degree, node connectivity κ(G), and Tutte's odd-component count
-- statement:
--   Let $G=(V,E)$ be a finite simple graph and write $d(v)$ for the degree of $v$.
--
--   1. Given $b\in\mathbb Z_{\ge 0}^V$, a **$b$-factor** of $G$ is a set $F\subseteq E$ such that exactly $b_v$ edges of $F$ are incident to $v$, for every $v\in V$. For $U\subseteq V$ write $b(U):=\sum_{v\in U}b_v$. An $f$-factor is the same notion with $f$ in place of $b$.
--   2. For $U,U'\subseteq V$, $N(U,U')$ is the number of edges of $G$ with one endpoint in $U$ and one endpoint in $U'$; in particular $N(U,U)$ is the number of edges inside $U$.
--   3. $d_{\max}$ and $d_{\min}$ are the maximum and minimum node degrees of $G$.
--   4. The **node connectivity** $\kappa(G)$ is the minimum number of nodes whose deletion disconnects $G$, or the total number of nodes when $G$ is complete.
--   5. For $U\subseteq V$, $G-U$ is the graph obtained by deleting the nodes of $U$ and all edges incident to them. For disjoint $S,T\subseteq V$ and $f\in\mathbb Z_{\ge0}^V$, $\widetilde Q(S,T)$ is the number of connected components $C$ of $G-(S\cup T)$ with
--   $$
--   f(C)+N(C,T)\equiv 1 \pmod 2 .
--   $$
--
--   These are the objects of the factor theorems (Propositions 5 and 7) and of the random-graph degree and connectivity statements (Propositions 6, 8, 9) used to prove Propositions 3 and 4.
--
--   **Formalization Note** A $b$-factor is encoded as a spanning subgraph $F\le G$ with $\deg_F(v)=b_v$. $N(U,U')$ counts edges of $G$ (each once) of the form $\{u,u'\}$ with $u\in U$, $u'\in U'$. On an empty vertex set $d_{\max}=d_{\min}=0$. $\kappa(G)$ is the least $|S|$ such that $G-S$ is not connected, where the graph on no vertices counts as not connected (Mathlib's convention); deleting all nodes therefore always qualifies, and for a complete graph it is the only option, giving $\kappa(K_n)=n$ exactly as the paper stipulates (the usual convention is $n-1$).
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 20 (§5.1, b-factor, b(U), N(U, U′)) and p. 24 (§5.2, G − U, Proposition 7's Q̃(S, T), κ(G))

import Mathlib

open Finset
open scoped Classical

namespace LPCommunity.SBMRecovery

/-! The graph-factor layer of §5.1 (p. 20) and §5.2 (p. 24) of Del Pia, Khajavirad, Kunisky,
*Linear Programming and Community Detection* (arXiv:2006.03213v2), for a finite simple graph
`G = (V, E)`: b-factors (= f-factors), the edge count `N(U, U′)`, the maximum and minimum degree,
the node connectivity `κ(G)`, and the odd-component count `Q̃(S, T)` of Tutte's f-factor theorem. -/

variable {V : Type*} [Fintype V]

/-- `G` has a `b`-factor (p. 20): a set `F ⊆ E` of edges such that exactly `b v` edges of `F` are
incident to `v`, for every `v`. `F` is encoded as a spanning subgraph of `G`. The same notion is
called an f-factor on p. 24. -/
def HasFactor (G : SimpleGraph V) (b : V → ℕ) : Prop :=
  ∃ F : SimpleGraph V, F ≤ G ∧ ∀ v, F.degree v = b v

/-- `N(U, U′)` (p. 20): the number of edges of `G` with one endpoint in `U` and one in `U′`. Each
edge is counted once; for `U = U′` this is the number of edges inside `U`. -/
noncomputable def edgeCount (G : SimpleGraph V) (U U' : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => ∃ u ∈ U, ∃ u' ∈ U', e = s(u, u')).card

/-- The maximum node degree `d_max` of `G` (`0` for an empty vertex set). -/
noncomputable def dMax (G : SimpleGraph V) : ℕ := univ.sup fun v => G.degree v

/-- The minimum node degree `d_min` of `G` (`0` for an empty vertex set). -/
noncomputable def dMin (G : SimpleGraph V) : ℕ :=
  if h : (univ : Finset V).Nonempty then univ.inf' h (fun v => G.degree v) else 0

/-- The node connectivity `κ(G)` (p. 24): the minimum number of nodes whose deletion disconnects
`G`. Mathlib's `Connected` requires a nonempty vertex type, so deleting every node always
disconnects and the minimum exists; for a complete graph this is the only disconnecting deletion,
so `κ(K_n) = n`, "the total number of nodes for G a complete graph" as on p. 24. -/
noncomputable def kappa (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset V, S.card = k ∧ ¬ (G.induce ((↑S : Set V)ᶜ)).Connected}

/-- The vertex set, as a subset of `V`, of a connected component `C` of `G − U`
(`G − U` is `G` with the nodes of `U` and their incident edges removed, p. 24). -/
noncomputable def compVerts (G : SimpleGraph V) (U : Finset V)
    (C : (G.induce ((↑U : Set V)ᶜ)).ConnectedComponent) : Finset V :=
  univ.filter fun v => ∃ h : v ∈ ((↑U : Set V)ᶜ),
    (G.induce ((↑U : Set V)ᶜ)).connectedComponentMk ⟨v, h⟩ = C

/-- `Q̃(S, T)` (p. 24): the number of connected components `C` of `G − (S ∪ T)` with
`f(C) + N(C, T) ≡ 1 (mod 2)`, where `f(C) = ∑_{v ∈ C} f v`. -/
noncomputable def oddComps (G : SimpleGraph V) (f : V → ℕ) (S T : Finset V) : ℕ :=
  (univ.filter fun C : (G.induce ((↑(S ∪ T) : Set V)ᶜ)).ConnectedComponent =>
    Odd ((∑ v ∈ compVerts G (S ∪ T) C, f v) + edgeCount G (compVerts G (S ∪ T) C) T)).card

end LPCommunity.SBMRecovery


