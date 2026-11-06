-- Prove2me | Definitions.Def_MemQueryFeas_RandMemAlg
-- name    : MemQueryFeas_RandMemAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:34.483193+00:00
-- url     : https://prove2.me/theorems/ef690df3-8d83-4c14-9589-a055989b1097
-- title:
--   Randomized $M$-bit memory-constrained algorithm
-- statement:
--   A **randomized $M$-bit memory-constrained algorithm** consists of
--   1. a probability space $(\Omega,\mu)$ of per-round randomness;
--   2. a query map $\psi_{query}:\{0,1\}^M\times\Omega\to B_d(0,1)$;
--   3. a memory update map $\psi_{update}:\{0,1\}^M\times\mathbb R^d\times(\mathbb R^d\cup\{\mathrm{Success}\})\times\Omega\to\{0,1\}^M$.
--
--   In each round a fresh draw $\omega_t\sim\mu$, independent of earlier rounds, is used by both maps. The memory between rounds is the $M$-bit register; within a round the maps are arbitrary measurable functions.
--
--   **Formalization Note** $\{0,1\}^M$ is `Fin M → Bool`. The maps are measurable in the randomness (the update jointly in the query, the response and the randomness), the standing convention for randomized algorithms. One shared draw per round covers two independent draws, by taking $\Omega$ a product.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_MemQueryFeas_Vec

open MeasureTheory

namespace MemQueryFeas

/-- **Randomized `M`-bit memory-constrained algorithm.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Problem setup, p.3 (PDF p.4): "An
M-bit memory-constrained algorithm maintains an M-bit register `Memory_t ∈ {0, 1}^M` … it is
specified by some query map `ψ_query : {0,1}^M → B_d(0,1)` and memory update function
`ψ_update : {0,1}^M × B_d(0,1) × (ℝ^d ∪ {Success}) → {0,1}^M`. These may be randomized, in which case
the algorithm may use i.i.d. fresh randomness on each round."

A randomized algorithm carries a probability space `(Ω, μ)` of per-round randomness, a query map
`query m ω ∈ B_d(0,1)` and an update map `update m x r ω`, both depending on the memory state
`m ∈ {0,1}^M` and on the round's fresh draw `ω`.

**Formalization Note.** `{0,1}^M` is `Fin M → Bool`; Success is `none`; the unit ball is the closed
ball. One fresh draw `ω ∼ μ` per round feeds both maps of that round (this covers two independent
draws, by taking `Ω` a product). `Ω` lives in `Type`. As is standard for randomized algorithms the
maps are measurable: `query m` in `ω`, and `update m` jointly in the query, the returned normal and
`ω` (separately on Success and on non-Success responses). Within a round the maps are arbitrary
measurable functions; only the memory between rounds is bounded. -/
structure RandMemAlg (d M : ℕ) where
  /-- The space of per-round randomness. -/
  Ω : Type
  /-- Its σ-algebra. -/
  [mΩ : MeasurableSpace Ω]
  /-- The law of one round's fresh randomness. -/
  μ : Measure Ω
  /-- `μ` is a probability measure. -/
  [isProb : IsProbabilityMeasure μ]
  /-- The query map `ψ_query`. -/
  query : (Fin M → Bool) → Ω → Vec d
  /-- Queries lie in the closed unit ball. -/
  query_mem : ∀ m ω, query m ω ∈ Metric.closedBall (0 : Vec d) 1
  /-- The memory update map `ψ_update`. -/
  update : (Fin M → Bool) → Vec d → Option (Vec d) → Ω → (Fin M → Bool)
  /-- The query map is measurable in the randomness. -/
  measurable_query : ∀ m, Measurable (query m)
  /-- The update on a Success response is jointly measurable. -/
  measurable_update_none : ∀ m, Measurable (fun p : Vec d × Ω => update m p.1 none p.2)
  /-- The update on a returned normal is jointly measurable. -/
  measurable_update_some :
    ∀ m, Measurable (fun p : Vec d × Vec d × Ω => update m p.1 (some p.2.1) p.2.2)

attribute [instance] RandMemAlg.mΩ RandMemAlg.isProb

end MemQueryFeas


