-- Prove2me | Definitions.Def_RoslingAssembly_pathMeasure
-- name    : RoslingAssembly_pathMeasure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:38:13.438851+00:00
-- url     : https://prove2.me/theorems/3918feae-b50e-496e-af33-a9a80dab7447
-- title:
--   Law of the i.i.d. demand sequence
-- statement:
--   Let $\mu$ be the law of the one-period demand. The demands $\xi_1,\xi_2,\dots$ of different periods are independent and identically distributed with law $\mu$; their joint law is the infinite product measure $\mu^{\otimes\mathbb N}$ on the space of demand paths $\mathbb R^{\mathbb N}$.
--
--   All expectations in problem P are taken under this measure.
--
--   **Formalization Note** The canonical space is `ℕ → ℝ` with `Measure.infinitePi`; coordinate $j$ is the demand of period $j+1$.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Operations Research 37(4), 1989, §1, p. 566

import Mathlib
open MeasureTheory

namespace RoslingAssembly

/-- **Law of the demand sequence** (§1, p. 566). Rosling, *Optimal Inventory Policies for
Assembly Systems under Random Demands*, Operations Research 37(4), 1989, p. 566 (unnumbered):
"ξ_t = demands in period t for the end item; demands of different periods are identically and
independently distributed, ξ_t ≥ 0;".

Given the one-period demand law `μ` on `ℝ`, `pathMeasure μ` is the law of the i.i.d. demand
sequence (ξ_1, ξ_2, …) on the canonical space `ℕ → ℝ`: the infinite product of copies of `μ`.

**Formalization Note.** Coordinate `j` of `ω : ℕ → ℝ` is the demand of paper period `j + 1`.
`Measure.infinitePi` is the product measure (it is a probability measure when `μ` is). -/
noncomputable def pathMeasure (μ : Measure ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => μ)

end RoslingAssembly


