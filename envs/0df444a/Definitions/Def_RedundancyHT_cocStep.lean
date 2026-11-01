-- Prove2me | Definitions.Def_RedundancyHT_cocStep
-- name    : RedundancyHT_cocStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:51.848116+00:00
-- url     : https://prove2.me/theorems/304d6621-ffbf-4fb0-bfff-bcb5a80dc671
-- title:
--   One event of the redundancy c.o.c. system on job sequences
-- statement:
--   The occupancy of the cancel-on-completion system is the sequence $(c_1,\dots,c_M)$ of the types of all jobs present, oldest first. An arrival of type $S$ appends $S$. The service clock of server $n$ removes the oldest job $c_i$ with $n\in c_i$, because the first replica to finish discards the others; the clock has no effect if no job is compatible with $n$.
--
--   This operational description gives the job at position $i$ the departure rate $\sum_{n\in c_i\setminus\bigcup_{m<i}c_m}\mu_n$, which is the mechanism behind the product form (3).
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §2.1, p.4, and §2.3.1, p.7

import Definitions.Def_BipartiteMatchingHT_Delay_Queue

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **One event of the c.o.c. system** (arXiv:2005.14566v5, §2.1, p.4, and §2.3.1, p.7). The state
is the sequence `(c₁,…,c_M)` of the types of all jobs present, oldest first, in service or not. An
arrival of type `i` joins the end. The clock of server `j` removes the oldest job compatible with
`j`, and does nothing if no job is compatible.

**Formalization Note.** Every server works on its oldest compatible job, and replica sizes are
independent unit exponentials, so server `j` ends a job at rate `µ_j`, and that job leaves with all
its replicas. The job at position `i` therefore leaves at rate
`Σ_{n ∈ c_i \ ∪_{m<i} c_m} µ_n`. -/
def cocStep {n m : ℕ} (D : Model n m) (c : List (Fin n)) : Event n m → List (Fin n)
  | .inl i => c ++ [i]
  | .inr j => c.eraseP (fun i => D.compatible i j)

end RedundancyHT


