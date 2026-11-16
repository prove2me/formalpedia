-- Prove2me | Definitions.Def_WeightedEdgeColor_Supplement_RatGraph
-- name    : WeightedEdgeColor_Supplement_RatGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:37:36.460014+00:00
-- url     : https://prove2.me/theorems/ee224705-ed1a-4ef6-81ba-9a0c0e8eb983
-- title:
--   Algorithm input: rational-weighted loopless multigraph with an explicit edge list, its memory encoding and correct outputs
-- statement:
--   An **input** to the paper's algorithms is a loopless multigraph with rational edge weights in $(0,1]$ and an explicitly listed edge set: a vertex count $N$ (vertices $0,\dots,N-1$) and a list of $m$ edges, edge $i$ given by its endpoints $u_i\ne v_i$ and its weight $p_i/q_i$ with positive integers $p_i\le q_i$. Parallel edges are listed separately.
--
--   It determines:
--   1. the weighted multigraph $G_I$ with vertex set $\{0,\dots,N-1\}$, edge set $\{0,\dots,m-1\}$, endpoints $\{u_i,v_i\}$ and weights $p_i/q_i$;
--   2. the initial machine memory, holding $N,m$ and then $u_i,v_i,p_i,q_i$ for each edge in order;
--   3. the input length $L$, the number of these cells plus the total bit length of their contents;
--   4. the correctness predicate for a color bound $X$: a final memory is correct if, reading cell $i$ as the color of edge $i$, there is $k\le X$ such that all colors are below $k$ and the coloring is a proper weighted coloring of $G_I$.
--
--   This is the input/output convention for the running-time clauses of Theorems B.2, D.3, E.4, E.10, F.1 and F.6.
--
--   **Formalization Note** The paper fixes no encoding; this is one standard choice. Weights are unreduced fractions, so every rational weight in $(0,1]$ has an encoding.
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), Theorems F.1 and F.6, pp.71, 77 ("For rational weights and explicitly listed edges"); Theorems B.2, D.3, E.4, E.10, pp.31, 60, 64, 70

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsProperColoring
import Definitions.Def_TimeSpaceMA_RAM

set_option autoImplicit false

namespace WeightedEdgeColor

namespace Supplement

/-- An algorithm input: a loopless multigraph with rational edge weights in `(0, 1]` and an
explicitly listed edge set. The vertices are `0, …, N - 1`; edge `i < m` joins `u i ≠ v i` and has
weight `p i / q i` with `0 < p i ≤ q i`. Parallel edges are listed separately.

Source: Gajjala, Khan, *Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing*,
preprint of November 2, 2026 (arXiv:2611.03190, version not stamped), Theorems F.1 and F.6,
pp.71, 77 ("For rational weights and explicitly listed edges"); Theorems B.2, D.3, E.4, E.10,
pp.31, 60, 64, 70.

**Formalization Note.** The paper fixes no encoding. Weights are given as unreduced fractions of
positive naturals; every rational in `(0, 1]` has such a form. The associated weighted graph is
`toWGraph`, the input memory `mem`, the input length `bits`, and the correctness predicate on
the final memory `GoodOutput`. -/
structure RatGraph where
  /-- Number of vertices. -/
  N : ℕ
  /-- Number of edges. -/
  m : ℕ
  /-- First endpoint of each edge. -/
  u : Fin m → Fin N
  /-- Second endpoint of each edge. -/
  v : Fin m → Fin N
  /-- Weight numerators. -/
  p : Fin m → ℕ
  /-- Weight denominators. -/
  q : Fin m → ℕ
  uv_ne : ∀ i, u i ≠ v i
  p_pos : ∀ i, 0 < p i
  p_le_q : ∀ i, p i ≤ q i

namespace RatGraph

/-- The weighted multigraph `G = (V, E)` described by the input: `V = Fin N`, `E = Fin m`, edge
`i` has endpoints `{u i, v i}` and weight `w_i = p i / q i ∈ (0, 1]`. -/
noncomputable def toWGraph (I : RatGraph) : WGraph (Fin I.N) (Fin I.m) where
  ends i := s(I.u i, I.v i)
  loopless i := by
    rw [Sym2.mk_isDiag_iff]
    exact I.uv_ne i
  w i := (I.p i : ℝ) / (I.q i : ℝ)
  w_pos i := by
    have hp : (0 : ℝ) < I.p i := by exact_mod_cast I.p_pos i
    have hq : (0 : ℝ) < I.q i := by exact_mod_cast lt_of_lt_of_le (I.p_pos i) (I.p_le_q i)
    exact div_pos hp hq
  w_le_one i := by
    have hq : (0 : ℝ) < I.q i := by exact_mod_cast lt_of_lt_of_le (I.p_pos i) (I.p_le_q i)
    rw [div_le_one hq]
    exact_mod_cast I.p_le_q i

/-- The memory cells of the input: `N`, `m`, then for each edge `i` in order the four cells
`u i, v i, p i, q i`. -/
def cells (I : RatGraph) : List ℕ :=
  [I.N, I.m] ++ (List.finRange I.m).flatMap fun i => [(I.u i : ℕ), (I.v i : ℕ), I.p i, I.q i]

/-- The initial memory of the machine: the input cells from address `0` on, zero elsewhere. -/
def mem (I : RatGraph) : ℕ → ℕ := TimeSpaceMA.memOf I.cells

/-- The input length `L`: the number of cells plus the total bit length of their contents. -/
def bits (I : RatGraph) : ℕ := I.cells.length + (I.cells.map Nat.size).sum

/-- Correctness of an output memory `out` for the color bound `X`: cell `i` (for `i < m`) holds
the color of edge `i`; there is `k ≤ X` with every color below `k`, and the decoded coloring
`E → Fin k` is a proper weighted coloring of `toWGraph`. -/
def GoodOutput (I : RatGraph) (X : ℝ) (out : ℕ → ℕ) : Prop :=
  ∃ k : ℕ, (k : ℝ) ≤ X ∧ ∃ h : ∀ i : Fin I.m, out i < k,
    I.toWGraph.IsProperColoring (fun i => (⟨out i, h i⟩ : Fin k))

end RatGraph

end Supplement

end WeightedEdgeColor


