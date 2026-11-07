-- Prove2me | Definitions.Def_HZTractability_ThresholdDeg2
-- name    : HZTractability_ThresholdDeg2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:10:20.419287+00:00
-- url     : https://prove2.me/theorems/b7785ff4-3b50-4589-898d-7789b69a9890
-- title:
--   The threshold-game search problem with degrees at most two
-- statement:
--   For a fixed tolerance $\kappa$, an **instance** is a nonempty directed graph on $n\ge 1$ vertices in which every vertex has indegree at most two and outdegree at most two, given by its $0/1$ adjacency matrix (diagonal entries are self-loops). An **answer** is a rational $\kappa$-threshold solution of the graph (Definition 2.1).
--
--   [DFHM24, Theorem 4.23], quoted on p.6, states that this problem is PPAD-complete for every fixed $0<\kappa<1/6$; it is the source problem of the reduction proving Theorem 1.1.
--
--   **Formalization Note** The adjacency matrix is written with the public `encRatMatrix`, answers with `encRatVec`. Sinks are allowed; the sink elimination before (2) belongs to the reduction.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), §2.1, p.6 (PDF p.8); nonempty graphs, §5.1, p.20

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_HZTractability_ThrGraph
import Definitions.Def_HZTractability_IsThresholdSol

namespace HZTractability

/-- The graph with vertex set `Fin n` whose edges `u → v` are the entries `A u v = 1` of a `0/1`
matrix `A`. -/
def graphOfMatrix (n : ℕ) (A : Fin n → Fin n → ℚ) : ThrGraph where
  n := n
  adj u v := decide (A u v = 1)

/-- **The threshold-game search problem with degrees at most two** (Panageas–Shein–Taherijam–
Vazirani, arXiv:2610.35848, held version, sha256 74b7bf9f…, §2.1, p.6 (PDF 8): "Finding one is
PPAD-complete for every fixed 0 < κ < 1/6, even when both degrees are at most two
[DFHM24, Theorem 4.23]").

An instance is the code `encRatMatrix n A` of the adjacency matrix `A ∈ {0,1}^{n×n}` of a directed
graph on `n ≥ 1` vertices (`A u v = 1` iff `u → v`; diagonal entries are self-loops) in which every
vertex has indegree at most two and outdegree at most two. An answer is the code `encRatVec n z`
of a rational κ-threshold solution `z` of the graph (Definition 2.1, `IsThresholdSol`).

**Formalization Note** The paper does not fix an encoding of threshold instances; the adjacency
matrix is written with the public `CardinalMatching.encRatMatrix`, and answers are rational vectors
(`encRatVec`). Sinks are allowed (outdegree `0`); the sink elimination before (2) is part of the
reduction, not of the instance. The graph is nonempty (§5.1, p.20: "finite nonempty directed
graph"). -/
def ThresholdDeg2 (κ : ℚ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (n : ℕ) (A : Fin n → Fin n → ℚ), 1 ≤ n ∧ (∀ u v, A u v = 0 ∨ A u v = 1) ∧
    (∀ v, (graphOfMatrix n A).indeg v ≤ 2 ∧ (graphOfMatrix n A).outdeg v ≤ 2) ∧
    s = CardinalMatching.encRatMatrix n A
  answer s t := ∃ (n : ℕ) (A : Fin n → Fin n → ℚ), 1 ≤ n ∧ (∀ u v, A u v = 0 ∨ A u v = 1) ∧
    (∀ v, (graphOfMatrix n A).indeg v ≤ 2 ∧ (graphOfMatrix n A).outdeg v ≤ 2) ∧
    s = CardinalMatching.encRatMatrix n A ∧
    ∃ z : Fin n → ℚ, t = CardinalMatching.encRatVec n z ∧
      IsThresholdSol (κ : ℝ) (graphOfMatrix n A) (fun v => (z v : ℝ))

end HZTractability


