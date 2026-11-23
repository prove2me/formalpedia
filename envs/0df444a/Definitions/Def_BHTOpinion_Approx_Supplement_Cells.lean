-- Prove2me | Definitions.Def_BHTOpinion_Approx_Supplement_Cells
-- name    : BHTOpinion_Approx_Supplement_Cells
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:53:50.338874+00:00
-- url     : https://prove2.me/theorems/bede0c8f-09eb-4619-b343-fa4c4a18afc1
-- title:
--   Appendix A: cells X_G, frozen Laplacian dynamics (A.1), the recursive construction, and nonproblematic switches
-- statement:
--   Fix $n$ agents. For a simple undirected graph $G$ on the agents with edge set $E$, the **cell** $X_G\subseteq\mathbb R^n$ is the set of profiles $x$ with
--   $$
--   |x_i-x_j|<1 \text{ if } \{i,j\}\in E,\qquad |x_i-x_j|>1 \text{ if } i\neq j,\ \{i,j\}\notin E .
--   $$
--   On $X_G$ the system (2.1) becomes the linear system (A.1)
--   $$
--   \dot x_i=\sum_{j:\{i,j\}\in E}(x_j-x_i),\qquad\text{i.e.}\qquad \dot x=-L_Gx ,
--   $$
--   where $L_G=D_G-A_G$ is the Laplacian matrix of $G$.
--
--   **Recursive construction.** An infinite run from an initial profile $\tilde x$ consists of graphs $G_0,G_1,\dots$, times $0=t_0<t_1<t_2<\cdots$ and a trajectory $x$ such that
--   1. $\tilde x\in X_{G_0}$ and $x(0)=\tilde x$;
--   2. on each interval $[t_k,t_{k+1}]$, $x$ solves $\dot x=-L_{G_k}x$ starting from $x(t_k)$;
--   3. $x(s)\in X_{G_k}$ for $t_k<s<t_{k+1}$ and $x(t_{k+1})\in\partial X_{G_k}$, so $t_{k+1}$ is the first time after $t_k$ at which the frozen solution reaches the boundary of its cell;
--   4. the construction continues from $x(t_{k+1})$ with the next graph $G_{k+1}$.
--
--   Only the values of $x$ on the union of the intervals $[t_k,t_{k+1}]$ are part of the run.
--
--   **Nonproblematic switch.** A transition from $X_G$ to $X_{G'}$ at the boundary point $p$ is nonproblematic when $p$ belongs to the closures of both $X_G$ and $X_{G'}$ and to the closure of no other cell, the graphs $G$ and $G'$ differ in exactly one edge $\{i,j\}$, and
--   $$
--   (L_Gp)_i-(L_Gp)_j\neq0
--   $$
--   for the incoming graph $G$. A boundary point at which $(L_Gp)_i-(L_Gp)_j=0$, or which is incident to more than two cells, is **problematic**.
--
--   These objects are the setting of Lemma 4, the step of the proof of Theorem 1 that rules out an accumulation of switching times.
--
--   **Formalization Note** Graphs are `SimpleGraph (Fin n)` and $L_G$ is Mathlib's `SimpleGraph.lapMatrix ℝ`, with classical decidability. Step 2 is encoded as a derivative within the closed interval $[t_k,t_{k+1}]$ at every point, so $x$ is the (unique) solution of the linear system on that interval. The boundary is the topological frontier; since $X_G$ is open, item 3 makes $t_{k+1}$ the first boundary time. Divergence of the times $t_k$ is deliberately not part of the run.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, Continuous-time average-preserving opinion dynamics with opinion-dependent communications, SIAM J. Control Optim. 48 (2010), DOI 10.1137/090766188, pp. 5234–5235 (PDF 21–22), Appendix A: definition of X_G, (A.1), the recursive construction, and the problematic boundary points

import Mathlib

namespace BHTOpinion.Approx.Supplement

/-- The cell `X_G ⊆ ℝⁿ` of a simple undirected graph `G` on the agents (Appendix A, p. 5234):
the profiles `x` with `|x_i − x_j| < 1` for every edge `{i, j}` of `G` and `|x_i − x_j| > 1` for
every pair of distinct agents that is not an edge. -/
def cell {n : ℕ} (G : SimpleGraph (Fin n)) : Set (Fin n → ℝ) :=
  {x | ∀ i j : Fin n, i ≠ j →
    (G.Adj i j → |x i - x j| < 1) ∧ (¬ G.Adj i j → 1 < |x i - x j|)}

open Classical in
/-- The frozen-graph vector field of (A.1) (p. 5234): `ẋ = −L_G x`, i.e.
`ẋ_i = ∑_{j : {i,j} ∈ E} (x_j − x_i)`, where `L_G = D − A` is the (unweighted) Laplacian matrix
of `G` (`SimpleGraph.lapMatrix`). -/
noncomputable def frozenField {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → ℝ) : Fin n → ℝ :=
  -((G.lapMatrix ℝ).mulVec x)

/-- An infinite run of the recursive construction of Appendix A (pp. 5234–5235) from the initial
profile `x₀`: graphs `G k`, times `0 = t 0 < t 1 < t 2 < ⋯` and a trajectory `x` such that
1. `x₀ ∈ X_{G 0}` and `x(0) = x₀`;
2. on each `[t k, t (k+1)]`, `x` is the solution of the frozen linear system `ẋ = −L_{G k} x`
   started from `x(t k)` (a derivative within the closed interval at every point);
3. `x(s) ∈ X_{G k}` for `t k < s < t (k+1)`, and `x(t (k+1))` lies on the boundary `∂X_{G k}`,
   so `t (k+1)` is the first boundary time after `t k` (the cell is open);
4. the construction continues from the same point with the next graph `G (k+1)`.
Only the values of `x` on the union of the intervals `[t k, t (k+1)]` are constrained; nothing is
assumed about whether the times `t k` diverge. -/
structure IsCellRun {n : ℕ} (x₀ : Fin n → ℝ) (G : ℕ → SimpleGraph (Fin n)) (t : ℕ → ℝ)
    (x : ℝ → Fin n → ℝ) : Prop where
  start_time : t 0 = 0
  start_value : x 0 = x₀
  start_cell : x₀ ∈ cell (G 0)
  increasing : StrictMono t
  flow : ∀ k : ℕ, ∀ s ∈ Set.Icc (t k) (t (k + 1)),
    HasDerivWithinAt x (frozenField (G k) (x s)) (Set.Icc (t k) (t (k + 1))) s
  inside : ∀ k : ℕ, ∀ s ∈ Set.Ioo (t k) (t (k + 1)), x s ∈ cell (G k)
  hits_boundary : ∀ k : ℕ, x (t (k + 1)) ∈ frontier (cell (G k))

open Classical in
/-- A nonproblematic transition from the cell of `G` to the cell of `G'` at the boundary point `p`
(Appendix A, pp. 5234–5235): `p` belongs to the closures of both `X_G` and `X_{G'}` and of no other cell,
the graphs differ in exactly one edge `{i, j}` (`i ≠ j`), and `(L_G p)_i − (L_G p)_j ≠ 0` for the
incoming graph `G`. A boundary point violating one of these is "problematic". -/
def IsNonproblematicSwitch {n : ℕ} (G G' : SimpleGraph (Fin n)) (p : Fin n → ℝ) : Prop :=
  p ∈ closure (cell G) ∧ p ∈ closure (cell G') ∧
    (∀ H : SimpleGraph (Fin n), p ∈ closure (cell H) → H = G ∨ H = G') ∧
    ∃ i j : Fin n, i ≠ j ∧ symmDiff G.edgeSet G'.edgeSet = {s(i, j)} ∧
      (G.lapMatrix ℝ).mulVec p i - (G.lapMatrix ℝ).mulVec p j ≠ 0

end BHTOpinion.Approx.Supplement


