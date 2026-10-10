-- Prove2me | Definitions.Def_TaitTobin_Planar_Setting
-- name    : TaitTobin_Planar_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T11:46:56.035334+00:00
-- url     : https://prove2.me/theorems/280911a0-0aa6-42c1-b427-aa248be5ab02
-- title:
--   §1.2 and §3, pp. 3–11 — graph join, K₂ + Pₙ₋₂, planar spectral maximizers, e(X) and e(X, Y), the sets L and S, the vertex w of Lemma 11
-- statement:
--   This file fixes the objects of Section 3 of Tait and Tobin. Graphs are finite simple graphs; an $n$-vertex graph has vertex set $\{0,\dots,n-1\}$. For a graph $G$, $\lambda_1(G)$ denotes the largest eigenvalue of its adjacency matrix (the published spectral radius `specRad`), and a graph is *planar* if it has a crossing-free drawing in the plane by simple arcs (the published `IsPlanar`).
--
--   Items 1–3 below are defined once in the shared module `TaitTobin.Outerplanar.Setting` (as `join`, `IsSpecMax`, `eIn`, `eBetween`) and imported here; items 4–6 are defined in this file.
--
--   1. **Join.** For graphs $G$ on $\alpha$ and $H$ on $\beta$, the join $G + H$ is the graph on the disjoint union $\alpha \sqcup \beta$ that keeps the edges of $G$ and of $H$ and adds every edge between a vertex of $G$ and a vertex of $H$.
--   2. **Spectral maximizers.** For a property $P$ of graphs on $n$ vertices, $G$ is a spectral maximizer for $P$ if $G$ has $P$ and
--   $$\lambda_1(G') \le \lambda_1(G) \quad\text{for every graph } G' \text{ on the same } n \text{ vertices with } P.$$
--   3. **Edge counts.** For vertex sets $X, Y$, $e(X)$ is the number of edges with both ends in $X$, and $e(X,Y)$ is the number of edges with one end in $X$ and the other in $Y$, each edge counted once.
--   4. **The graph $K_2 + P_{n-2}$** (Figure 2; written $P_2 + P_{n-2}$ in Conjecture 1): an edge joined to every vertex of a path on $n-2$ vertices.
--   5. **Large and small entries.** For $\varepsilon \in \mathbb R$ and a vector $\mathbf v$ indexed by the vertices,
--   $$L = \{z : \mathbf v_z > \varepsilon\}, \qquad S = V(G) \setminus L = \{z : \mathbf v_z \le \varepsilon\}.$$
--   6. **The second hub.** Given $G$, $\varepsilon$, $\mathbf v$ and a vertex $x$, a vertex $w$ is a *second hub* if $w \in L$, $w \ne x$, $\mathbf v_w > 1 - 24\varepsilon$ and $|\{y \in S : y \not\sim w\}| \le 94\varepsilon n$. This is exactly the conclusion of Lemma 11, and is how Lemmas 12–14 refer to "the vertex $w$ from Lemma 11".
--
--   These are the objects in terms of which the Boots–Royle / Cao–Vince conjecture and all lemmas of Section 3 are stated.
--
--   **Formalization Note** $K_2 + P_{n-2}$ lives on the vertex type $\mathrm{Fin}\,2 \sqcup \mathrm{Fin}(n-2)$, so "$G$ is $K_2 + P_{n-2}$" is expressed elsewhere as a graph isomorphism; $n - 2$ is natural-number subtraction, used only for $n \ge 2$. The paper's $e(X,Y)$ is used for disjoint $X$, $Y$, where the definition agrees with it. The paper writes $L := \{\mathbf v_z \in V(G) : \mathbf v_z > \varepsilon\}$, meaning the set of vertices $z$; the definition uses vertices.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, pp. 3–4, §1.2 (notation); p. 8, §3 (Figure 2, the sets L and S); p. 10, Lemma 11; p. 11 ("let w be the vertex from Lemma 11")

import Mathlib
import Definitions.Def_WangKangXue_SpectralTuran_specRad
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_TaitTobin_Outerplanar_Setting

namespace TaitTobin.Planar

open WangKangXue.SpectralTuran

/-- `K₂ + Pₙ₋₂` (Figure 2, p. 8; written `P₂ + Pₙ₋₂` in Conjecture 1): an edge joined to every
vertex of a path on `n - 2` vertices. -/
def bookPath (n : ℕ) : SimpleGraph (Fin 2 ⊕ Fin (n - 2)) :=
  TaitTobin.Outerplanar.join (⊤ : SimpleGraph (Fin 2)) (SimpleGraph.pathGraph (n - 2))

open Classical in
/-- `L = {z : v_z > ε}` (p. 8): the vertices of large eigenvector entry. -/
noncomputable def Lset {n : ℕ} (ε : ℝ) (v : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun z => ε < v z)

open Classical in
/-- `S = V(G) \ L = {z : v_z ≤ ε}` (p. 8): the vertices of small eigenvector entry. -/
noncomputable def Sset {n : ℕ} (ε : ℝ) (v : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun z => v z ≤ ε)

open Classical in
/-- The conclusion of Lemma 11 (p. 10) for the vertex `w`: `w ∈ L`, `w ≠ x`, `v_w > 1 - 24ε` and
`|{y ∈ S : y ≁ w}| ≤ 94εn`. Lemmas 12–14 take "let `w` be the vertex from Lemma 11" as this
hypothesis. -/
def IsSecondHub {n : ℕ} (G : SimpleGraph (Fin n)) (ε : ℝ) (v : Fin n → ℝ) (x w : Fin n) : Prop :=
  w ∈ Lset ε v ∧ w ≠ x ∧ 1 - 24 * ε < v w ∧
    (((Sset ε v).filter (fun y => ¬ G.Adj y w)).card : ℝ) ≤ 94 * ε * n

end TaitTobin.Planar


