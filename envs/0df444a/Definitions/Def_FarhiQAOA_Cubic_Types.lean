-- Prove2me | Definitions.Def_FarhiQAOA_Cubic_Types
-- name    : FarhiQAOA_Cubic_Types
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:29:54.284407+00:00
-- url     : https://prove2.me/theorems/67c66bbb-1f62-4c7e-8059-3a1514b44902
-- title:
--   §II, fig. (18), (23)–(24), p. 5; §V, fig. (31), p. 8 — subgraph types g₄, g₅, g₆, f_g, crossed squares, isolated triangles
-- statement:
--   This file defines the combinatorial objects of the $p=1$ analysis of MaxCut on 3-regular graphs (§II, p. 5, and §V, p. 8).
--
--   1. **Subgraph types.** For an edge $\langle jk\rangle$ of a 3-regular graph, the $p=1$ subgraph $g(j,k)$ consists of the edge and the edges adjacent to it. Figure (18) shows its three possible shapes; with $j=0$, $k=1$:
--      - $g_4$ on 4 vertices, edges $\{0,1\},\{0,2\},\{0,3\},\{1,2\},\{1,3\}$ ($j,k$ have two common neighbours);
--      - $g_5$ on 5 vertices, edges $\{0,1\},\{0,2\},\{0,3\},\{1,2\},\{1,4\}$ (one common neighbour);
--      - $g_6$ on 6 vertices, edges $\{0,1\},\{0,2\},\{0,3\},\{1,4\},\{1,5\}$ (no common neighbour).
--   2. **Subgraph functions.** For each type $g$, as in (23)–(24) at $p=1$,
--   $$f_g(\gamma,\beta) = \langle s,g|\,U^\dagger(C_g,\gamma)\,U^\dagger(B_g,\beta)\,C_{\langle 01\rangle}\,U(B_g,\beta)\,U(C_g,\gamma)\,|s,g\rangle,$$
--   the expectation of the clause of the edge $\langle 01\rangle$ in the $p=1$ QAOA state of the graph $g$ alone: the phase operator is the cut objective $C_g$ of $g$ (19), the mixer $B_g$ acts on the qubits of $g$ (21), and $|s,g\rangle$ is the uniform superposition on those qubits.
--   3. **Common neighbours.** For vertices $j,k$, the number of vertices adjacent to both.
--   4. **Crossed squares.** A crossed square of $G$ is a set of 4 vertices spanning exactly 5 edges of $G$: a 4-cycle with one diagonal ($K_4$ minus an edge). In a 3-regular graph the two vertices off the diagonal each have one edge leaving the set. A 4-set spanning all 6 edges ($K_4$) is not a crossed square.
--   5. **Isolated triangles.** An isolated triangle is a set of 3 pairwise adjacent vertices such that the edges leaving it end on distinct vertices: if $u\ne v$ in the triangle have neighbours $x,y$ outside it, then $x\ne y$.
--   6. **Counts.** $S$ is the number of crossed squares and $T$ the number of isolated triangles of $G$.
--
--   These are the quantities in terms of which (32) expresses $F_1$ and the maximum cut is bounded.
--
--   **Formalization Note** The three subgraphs are given by explicit edge lists, so their adjacency is decidable. Crossed squares and isolated triangles are finite sets of vertex sets, filtered from all 4-element and 3-element subsets of the vertex set; $S$ and $T$ are their cardinalities.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, p. 5, Section II, figure (18), (19)–(24); p. 8, Section V, figure (31)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_FarhiQAOA_Cubic_Setting

namespace FarhiQAOA.Cubic

open QAlgorithms

/-- Farhi–Goldstone–Gutmann p. 5, figure (18), first picture: the subgraph type `g₄` of an edge
`⟨jk⟩` (`j = 0`, `k = 1`) of a 3-regular graph whose endpoints have two common neighbours `2, 3`.
Edges: `{0,1}, {0,2}, {0,3}, {1,2}, {1,3}` (4 vertices, 5 edges). -/
def gFour : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun u v =>
    (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)] : List (ℕ × ℕ))

/-- Farhi–Goldstone–Gutmann p. 5, figure (18), second picture: the subgraph type `g₅` of an edge
`⟨jk⟩` (`j = 0`, `k = 1`) whose endpoints have one common neighbour `2`; `j` has the further
neighbour `3` and `k` the further neighbour `4`. Edges: `{0,1}, {0,2}, {0,3}, {1,2}, {1,4}`
(5 vertices, 5 edges). -/
def gFive : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun u v =>
    (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 3), (1, 2), (1, 4)] : List (ℕ × ℕ))

/-- Farhi–Goldstone–Gutmann p. 5, figure (18), third picture: the subgraph type `g₆` of an edge
`⟨jk⟩` (`j = 0`, `k = 1`) whose endpoints have no common neighbour; `j` has the further neighbours
`2, 3` and `k` the further neighbours `4, 5`. Edges: `{0,1}, {0,2}, {0,3}, {1,4}, {1,5}`
(6 vertices, 5 edges). -/
def gSix : SimpleGraph (Fin 6) :=
  SimpleGraph.fromRel fun u v =>
    (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 3), (1, 4), (1, 5)] : List (ℕ × ℕ))

instance : DecidableRel gFour.Adj := fun u v => by unfold gFour; infer_instance
instance : DecidableRel gFive.Adj := fun u v => by unfold gFive; infer_instance
instance : DecidableRel gSix.Adj := fun u v => by unfold gSix; infer_instance

/-- Farhi–Goldstone–Gutmann pp. 5–6, (23)–(24) at `p = 1`: `f_{g₄}(γ, β)`, the expectation of
`C_⟨jk⟩` (`j = 0`, `k = 1`) in the `p = 1` QAOA state of the subgraph `g₄` alone, whose phase operator
is the cut objective `C_{g₄}` of `g₄` (19) and whose mixer acts on the qubits of `g₄` (21). -/
noncomputable def fg4 (γ β : ℝ) : ℝ := edgeTerm1 gFour γ β 0 1

/-- `f_{g₅}(γ, β)`: as `fg4`, for the subgraph type `g₅`. -/
noncomputable def fg5 (γ β : ℝ) : ℝ := edgeTerm1 gFive γ β 0 1

/-- `f_{g₆}(γ, β)`: as `fg4`, for the subgraph type `g₆`. -/
noncomputable def fg6 (γ β : ℝ) : ℝ := edgeTerm1 gSix γ β 0 1

/-- The number of common neighbours of `j` and `k` in `G`. For an edge `⟨jk⟩` of a 3-regular graph it
is `2`, `1` or `0`, and it tells the three pictures of figure (18) apart. -/
def commonNbrCount {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (j k : Fin n) : ℕ :=
  (Finset.univ.filter fun u => G.Adj j u ∧ G.Adj k u).card

/-- The edges of `G` inside the vertex set `Q`, each counted once as an ordered pair `u < v`. -/
def edgesWithin {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (Q : Finset (Fin n)) :
    Finset (Fin n × Fin n) :=
  (Q ×ˢ Q).filter fun e => e.1 < e.2 ∧ G.Adj e.1 e.2

/-- Farhi–Goldstone–Gutmann p. 8, figure (31), right: the crossed squares of `G`, the 4-vertex sets
spanning exactly 5 edges (a 4-cycle with one diagonal, i.e. `K₄` minus an edge, as an induced
subgraph). In a 3-regular graph the two vertices off the diagonal each have one edge leaving the set.
A 4-set spanning all 6 edges (the case where "the two edges that leave the crossed square are in
fact the same edge", i.e. `K₄`) is not a crossed square. -/
def crossedSquares {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard 4).filter fun Q => (edgesWithin G Q).card = 5

/-- The vertex set `R` spans a complete subgraph: any two distinct vertices of `R` are adjacent.
For a 3-element `R` this says `R` is a triangle. -/
def SpansClique {n : ℕ} (G : SimpleGraph (Fin n)) (R : Finset (Fin n)) : Prop :=
  ∀ u ∈ R, ∀ v ∈ R, u ≠ v → G.Adj u v

/-- Farhi–Goldstone–Gutmann p. 8: the edges leaving `R` end on distinct vertices. If `u ≠ v` in `R`
have neighbours `x, y` outside `R` (in the complement `Rᶜ`), then `x ≠ y`. -/
def LeavingEndsDistinct {n : ℕ} (G : SimpleGraph (Fin n)) (R : Finset (Fin n)) : Prop :=
  ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ∀ x ∈ Rᶜ, ∀ y ∈ Rᶜ, G.Adj u x → G.Adj v y → x ≠ y

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    DecidablePred (SpansClique G) := fun R => by unfold SpansClique; infer_instance

instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    DecidablePred (LeavingEndsDistinct G) := fun R => by unfold LeavingEndsDistinct; infer_instance

/-- Farhi–Goldstone–Gutmann p. 8, figure (31), left: the isolated triangles of `G`, the 3-vertex sets
`R` that span a triangle and whose 3 leaving edges end on distinct vertices
("To say that the triangle is isolated is to say that the 3 edges that leave the triangle end on
distinct vertices"). -/
def isolatedTriangles {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard 3).filter fun R : Finset (Fin n) =>
    SpansClique G R ∧ LeavingEndsDistinct G R

/-- `S`: the number of crossed squares of `G` (p. 8). -/
def S {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ := (crossedSquares G).card

/-- `T`: the number of isolated triangles of `G` (p. 8). -/
def T {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ := (isolatedTriangles G).card

end FarhiQAOA.Cubic


