-- Prove2me | Definitions.Def_MemQueryFeas_DetMemAlg
-- name    : MemQueryFeas_DetMemAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:45.985337+00:00
-- url     : https://prove2.me/theorems/fcc623a4-7959-47b8-a4af-0bd6be0510f2
-- title:
--   Deterministic $M$-bit memory-constrained algorithm
-- statement:
--   A **deterministic $M$-bit memory-constrained algorithm** is a query map $\psi_{query}:\{0,1\}^M\to B_d(0,1)$ and a memory update map $\psi_{update}:\{0,1\}^M\times\mathbb R^d\times(\mathbb R^d\cup\{\mathrm{Success}\})\to\{0,1\}^M$.
--
--   **Formalization Note** $\{0,1\}^M$ is `Fin M → Bool`; the unit ball is closed.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4); §3.2, p.10

import Mathlib
import Definitions.Def_MemQueryFeas_Vec

namespace MemQueryFeas

/-- **Deterministic `M`-bit memory-constrained algorithm.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4): an
`M`-bit algorithm "is specified by some query map `ψ_query : {0,1}^M → B_d(0,1)` and memory update
function `ψ_update : {0,1}^M × B_d(0,1) × (ℝ^d ∪ {Success}) → {0,1}^M`"; p.10 (PDF p.11): "We will
assume the learner is deterministic for this proof."

**Formalization Note.** `{0,1}^M` is `Fin M → Bool`, Success is `none`, and the unit ball is the
closed ball. The maps are arbitrary functions; measurability of the update in the response is the
separate predicate `DetMemAlg.IsMeasurable`. -/
structure DetMemAlg (d M : ℕ) where
  /-- The query map `ψ_query`. -/
  query : (Fin M → Bool) → Vec d
  /-- Queries lie in the closed unit ball. -/
  query_mem : ∀ m, query m ∈ Metric.closedBall (0 : Vec d) 1
  /-- The memory update map `ψ_update`. -/
  update : (Fin M → Bool) → Vec d → Option (Vec d) → (Fin M → Bool)

end MemQueryFeas


