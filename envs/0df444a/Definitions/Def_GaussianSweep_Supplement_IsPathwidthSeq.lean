-- Prove2me | Definitions.Def_GaussianSweep_Supplement_IsPathwidthSeq
-- name    : GaussianSweep_Supplement_IsPathwidthSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:38:13.708294+00:00
-- url     : https://prove2.me/theorems/1cca4b4e-5963-451e-b5c5-02907af14e77
-- title:
--   Pathwidth sequence
-- statement:
--   A sequence $a = (a_d)_{d\ge3}$ of reals is a **pathwidth sequence** if there is a function $\rho(n) = o(n)$ such that every graph $G$ satisfies
--   $$
--   \mathrm{pw}(G) \le \sum_{d \ge 3} a_d\, n_d(G) + \rho(n).
--   $$
--   Vertices of degree at most $2$ add nothing; a vertex of degree $d \ge 3$ adds $a_d$.
--
--   **Formalization Note** $\rho : \mathbb N \to \mathbb R$ with $\rho(n)/n \to 0$ is chosen before the graph, and every finite simple graph on any finite vertex type is covered (no degree bound). The sum is written over $3 \le d \le n$; since every degree is at most $n-1$, nothing is lost.
-- source:
--   Gaspers, Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 9.1, p.56 (PDF p.58)

import Mathlib
import Definitions.Def_GaussianSweep_pathwidth
import Definitions.Def_GaussianSweep_Supplement_numDeg
open Filter Topology

namespace GaussianSweep.Supplement

/-- A **pathwidth sequence** (Gaspers, *Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*, arXiv:2611.05146 (held version, sha256 e0ed039f…9eac), Definition 9.1, p.56 (PDF p.58)): a
sequence `a = (a_d)_{d≥3}` of reals such that there is a function `ρ(n) = o(n)` with
`pw(G) ≤ Σ_{d≥3} a_d n_d + ρ(n)` for every graph `G`.

**Formalization Note** `ρ : ℕ → ℝ` with `ρ(n)/n → 0` is chosen before the graph (the p.1
convention), and every finite simple graph on any finite vertex type `V` is covered, with no
degree bound; `n = |V|`, `pw` is the published `GaussianSweep.pathwidth`. The sum
`Σ_{d≥3} a_d n_d` is written over `3 ≤ d ≤ n`: every vertex has degree at most `n − 1`, so
`n_d = 0` for `d > n` and the two sums agree. Entries `a d` with `d < 3` are not used. -/
def IsPathwidthSeq (a : ℕ → ℝ) : Prop :=
  ∃ ρ : ℕ → ℝ, Tendsto (fun n => ρ n / n) atTop (𝓝 0) ∧
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (GaussianSweep.pathwidth G : ℝ) ≤
        (∑ d ∈ Finset.Icc 3 (Fintype.card V), a d * (numDeg G d : ℝ)) + ρ (Fintype.card V)

end GaussianSweep.Supplement


