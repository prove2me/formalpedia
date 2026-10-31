-- Prove2me | Definitions.Def_SplitPMSGame_sptCost
-- name    : SplitPMSGame_sptCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:35.012928+00:00
-- url     : https://prove2.me/theorems/0c261afd-dd58-48d8-a6ae-96fba2ca2362
-- title:
--   Equation (1): the $Q|split|\sum C_j$ cost of a multiset of jobs
-- statement:
--   For the processing requirements $q$ of $\psi$ jobs and a total machine speed $V$, let $q_{(1)}\le\dots\le q_{(\psi)}$ be the requirements in nondecreasing order. Then
--   $$
--   \mathrm{spt}(q,V)=\frac1V\sum_{k=1}^{\psi}(\psi-k+1)\,q_{(k)}.
--   $$
--   This is equation (1): the minimum total completion time of the jobs when they may be split over machines of total speed $V$ (shortest processing time first).
--
--   **Formalization Note** The requirements form a multiset of reals, sorted nondecreasingly; with 0-based index $k$ the weight is $\psi-k$. For $V=0$ (the empty coalition) the value is $0$.
-- source:
--   Alon, Anily, The Basic Core of a Parallel Machines Scheduling Game, MSOM 25(6) (2023), doi:10.1287/msom.2021.0337, §4.2, eq. (1), p.2239 (PDF p.8)

import Mathlib

namespace SplitPMSGame

/-- **Equation (1) on a multiset of processing requirements** (Alon, Anily, *The Basic Core of a
Parallel Machines Scheduling Game*, MSOM 25(6) (2023), §4.2, eq. (1), p.2239). For the
processing requirements `q` of a coalition's jobs and the coalition's total speed `V`,
`sptCost q V = (1/V) · ∑_{k=1}^{ψ} (ψ − k + 1) · q_(k)`, where `ψ = |q|` and
`q_(1) ≤ q_(2) ≤ ⋯ ≤ q_(ψ)` are the requirements in nondecreasing order: the minimum total
completion time of the jobs when they may be split over machines of total speed `V`.

**Formalization Note** The sorted list is `q.sort` (nondecreasing); with the 0-based list index
`k`, the paper's weight `ψ − k + 1` (1-based `k`) is `ψ − k`. Ties do not matter, since only the
sorted values enter. For `V = 0` Lean's `1/0 = 0` gives the value `0`, which is `P(∅) = 0`
when `q` is empty. -/
noncomputable def sptCost (q : Multiset ℝ) (V : ℝ) : ℝ :=
  (1 / V) * ∑ k ∈ Finset.range q.card, ((q.card - k : ℕ) : ℝ) * (q.sort).getD k 0

end SplitPMSGame


