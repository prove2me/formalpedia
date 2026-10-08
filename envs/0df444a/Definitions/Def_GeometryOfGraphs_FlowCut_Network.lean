-- Prove2me | Definitions.Def_GeometryOfGraphs_FlowCut_Network
-- name    : GeometryOfGraphs_FlowCut_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:08:13.622974+00:00
-- url     : https://prove2.me/theorems/68b813aa-5e01-4fe5-937d-883945c0e40d
-- title:
--   Multicommodity flow network, Cap(S) and Dem(S) (Section 4, p. 226)
-- statement:
--   A **multicommodity flow network** consists of a finite vertex set $V$, **capacities** $C_{i,j} \ge 0$ for $i, j \in V$ with $C_{i,j} = C_{j,i}$ and $C_{i,i} = 0$, and $k$ **commodities**: for $\mu = 1, \dots, k$ a source $s_\mu \in V$, a sink $t_\mu \in V$ and a **demand** $D_\mu \ge 0$. The underlying undirected graph is implicit: $\{i,j\}$ is an edge when $C_{i,j} > 0$, and, as in the paper, $C_{i,j} = 0$ for every non-edge.
--
--   For $S \subseteq V$ the **capacity** and the **demand** of the cut $(S, \bar S)$ are
--   $$\mathrm{Cap}(S) = \sum_{i \in S}\sum_{j \notin S} C_{i,j},\qquad \mathrm{Dem}(S) = \sum_{\mu \,:\, |S \cap \{s_\mu, t_\mu\}| = 1} D_\mu .$$
--   So $\mathrm{Cap}(S)$ is the total capacity of the edges joining $S$ to its complement, each edge counted once, and $\mathrm{Dem}(S)$ is the total demand of the source–sink pairs that $S$ separates.
--
--   These are the objects of Section 4 of the paper; the sparsity $\mathrm{Cap}(S)/\mathrm{Dem}(S)$ is what Theorem 4.1 bounds.
--
--   **Formalization Note** The network is a structure with fields `C`, `k`, `s`, `t`, `D` and the side conditions as fields. Commodities are indexed by `Fin k`. Pairs with $s_\mu = t_\mu$ and repeated pairs are allowed; such a pair is never separated. `Cap` and `Dem` take a `Finset V`.
-- source:
--   N. Linial, E. London, Y. Rabinovich, The geometry of graphs and some of its algorithmic applications, Combinatorica 15 (1995), p. 226, Section 4, first two paragraphs

import Mathlib

set_option autoImplicit false

namespace GeometryOfGraphs.FlowCut

/-- A multicommodity flow network (Linial–London–Rabinovich, Combinatorica 15 (1995), §4, p. 226):
an undirected graph on the vertex set `V`, given by symmetric nonnegative capacities `C i j`
(`C i j = 0` for non-edges and on the diagonal), and `k` commodities, the `μ`-th with source `s μ`,
sink `t μ` and demand `D μ ≥ 0`. -/
structure Network (V : Type*) where
  /-- capacity of the undirected edge `{i, j}`; zero for non-edges -/
  C : V → V → ℝ
  C_nonneg : ∀ i j, 0 ≤ C i j
  C_symm : ∀ i j, C i j = C j i
  C_self : ∀ i, C i i = 0
  /-- number of source–sink pairs (commodities) -/
  k : ℕ
  /-- source of commodity `μ` -/
  s : Fin k → V
  /-- sink of commodity `μ` -/
  t : Fin k → V
  /-- demand of commodity `μ` -/
  D : Fin k → ℝ
  D_nonneg : ∀ μ, 0 ≤ D μ

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Cap(S)`: the sum of the capacities of the edges connecting `S` and its complement; each
undirected edge across the cut is counted once. -/
noncomputable def Network.Cap (N : Network V) (S : Finset V) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, N.C i j

/-- `Dem(S)`: the sum of the demands of the source–sink pairs separated by `S`, i.e. those with
`|S ∩ {s μ, t μ}| = 1`. -/
noncomputable def Network.Dem (N : Network V) (S : Finset V) : ℝ :=
  ∑ μ ∈ Finset.univ.filter
      (fun μ => (N.s μ ∈ S ∧ N.t μ ∉ S) ∨ (N.s μ ∉ S ∧ N.t μ ∈ S)), N.D μ

end GeometryOfGraphs.FlowCut


