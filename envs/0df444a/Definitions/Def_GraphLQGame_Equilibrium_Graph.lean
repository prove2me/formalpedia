-- Prove2me | Definitions.Def_GraphLQGame_Equilibrium_Graph
-- name    : GraphLQGame_Equilibrium_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:24:47.078587+00:00
-- url     : https://prove2.me/theorems/56c84a4b-5df4-4850-8f13-72474ba400cc
-- title:
--   Random-walk Laplacian $L_G = D_G^{-1}A_G - I$, vertex transitivity (Definition 2.3), no isolated vertices, and the automorphism matrices $R_\varphi$
-- statement:
--   Let $G$ be a finite simple graph on the vertex set $V=\{1,\dots,n\}$, with adjacency matrix $A_G$ and degree matrix $D_G=\mathrm{diag}(\deg_G(1),\dots,\deg_G(n))$.
--
--   1. The **random-walk Laplacian** is
--   $$L_G := D_G^{-1}A_G - I,\qquad (L_G)_{ij} = \frac{\mathbf 1\{i\sim j\}}{\deg_G(i)} - \mathbf 1\{i=j\}.$$
--   2. $G$ is **(vertex) transitive** if for all vertices $u,v$ there is a graph automorphism $\varphi\in\mathrm{Aut}(G)$ with $\varphi(u)=v$.
--   3. $G$ has **no isolated vertices** if $\deg_G(v)>0$ for every $v$.
--   4. For $\varphi\in\mathrm{Aut}(G)$, $R_\varphi$ is the permutation matrix with $R_\varphi e_i = e_{\varphi(i)}$, i.e. $(R_\varphi)_{ki} = \mathbf 1\{k=\varphi(i)\}$.
--
--   The matrix $L_G$ is negative semidefinite for regular graphs; it governs both the terminal cost of the game and the explicit equilibrium.
--
--   **Formalization Note** Vertices are `Fin n` (the paper's $1,\dots,n$ become $0,\dots,n-1$). The Lean matrix is not Mathlib's `lapMatrix` ($D-A$). The paper defines $L_G$ only without isolated vertices; the formula is total and gives the row $-e_i$ at an isolated vertex $i$, a value no statement uses.
-- source:
--   Lacker, Soret, A case study on stochastic games on large graphs in mean field and sparse regimes, arXiv:2005.14102v2 (2021), §2.2, pp. 5–6 (Definition 2.3, L_G); §4.1, p. 23 (R_φ)

import Mathlib

namespace GraphLQGame.Equilibrium

/-- The random-walk Laplacian `L_G = D_G⁻¹ A_G − I` of a finite simple graph on `Fin n`
(Lacker–Soret, arXiv:2005.14102v2, §2.2, p. 6).

Formalization Note: this is *not* Mathlib's `SimpleGraph.lapMatrix` (= `D − A`). The paper defines
`L_G` only when `G` has no isolated vertices; the formula here is total, and at an isolated vertex
`i` its row is `−e_i`, a value no statement uses. Vertices `1, …, n` of the paper are `Fin n`. -/
noncomputable def lap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (if G.Adj i j then ((G.degree i : ℝ))⁻¹ else 0) - if i = j then 1 else 0

/-- Vertex transitivity (Definition 2.3, p. 5): for all vertices `u, v` some graph automorphism
maps `u` to `v`. -/
def IsTransitive {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ u v : Fin n, ∃ φ : G ≃g G, φ u = v

/-- `G` has no isolated vertices: every degree is positive (§2.2, p. 6). -/
def NoIsolated {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  ∀ v : Fin n, 0 < G.degree v

/-- The permutation matrix `R_φ` of an automorphism, defined by `R_φ e_i = e_{φ(i)}`
(§4.1, p. 23): its `(k, i)` entry is `1` if `k = φ i` and `0` otherwise. -/
def autMatrix {n : ℕ} {G : SimpleGraph (Fin n)} (φ : G ≃g G) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun k i => if k = φ i then 1 else 0

end GraphLQGame.Equilibrium


