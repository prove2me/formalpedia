-- Prove2me | Definitions.Def_PlantedSubgraphLD_tvDist
-- name    : PlantedSubgraphLD_tvDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:34.780041+00:00
-- url     : https://prove2.me/theorems/fa145555-168e-4958-8837-312312ceea43
-- title:
--   Total variation distance $\|\mu-\nu\|_{\mathrm{TV}}$
-- statement:
--   For two laws $\mu,\nu$ on a finite set $\Omega$, the **total variation distance** is
--
--   $$
--   \|\mu-\nu\|_{\mathrm{TV}}=\sup_{A\subseteq\Omega}|\mu(A)-\nu(A)|,\qquad \mu(A)=\sum_{x\in A}\mu(x).
--   $$
--
--   It is the largest advantage of any test, efficient or not, between the two laws; Theorem 1.1 shows it vanishes between $T_\varepsilon P_n$ and $Q_n$.
--
--   **Formalization Note** On a finite set every subset is a `Finset`; the supremum is over finitely many values.
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.1, p.12 (PDF p.14)

import Mathlib

namespace PlantedSubgraphLD

/-- The total variation distance `‖μ − ν‖_TV := sup_A |μ(A) − ν(A)|` of two laws on a finite set.

Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection* (manuscript of
Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §3.1, p.12: "For probability measures µ and ν,
we write ‖µ − ν‖TV := sup_A |µ(A) − ν(A)|."

**Formalization Note** On a finite set every subset is a `Finset`, and `μ(A) = ∑_{x ∈ A} μ(x)`.
The supremum is over finitely many values, so it is a maximum. -/
noncomputable def tvDist {α : Type*} (μ ν : α → ℝ) : ℝ :=
  ⨆ A : Finset α, |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|

end PlantedSubgraphLD


