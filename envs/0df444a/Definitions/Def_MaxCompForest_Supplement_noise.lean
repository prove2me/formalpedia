-- Prove2me | Definitions.Def_MaxCompForest_Supplement_noise
-- name    : MaxCompForest_Supplement_noise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:10:33.359504+00:00
-- url     : https://prove2.me/theorems/9edb2570-cc4b-4bb4-abba-7459869ec3bd
-- title:
--   Gaussian noise law $N(0,\sigma^2D^{-1})$ on a graph
-- statement:
--   For a graph $G$ with weighted degrees $d_v$ and $\sigma>0$, the **noise law** is the law of $\xi\in\mathbb R^V$ with independent centered Gaussian coordinates,
--
--   $$\xi\sim N(0,\sigma^2D^{-1}),\qquad \xi_v\sim N(0,\sigma^2/d_v)\ \text{independently}.$$
--
--   Observations are $Y=f+\xi$ (5.2): the noise variance at a vertex is inversely proportional to its degree.
--
--   **Formalization Note** The product of Mathlib's `gaussianReal 0 (σ²/d_v)`; the variance is passed as a nonnegative real and is positive whenever $\sigma>0$ and $d_v>0$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (5.2), p.28 (PDF p.30)

import Mathlib
import Definitions.Def_EffResSparsify_ResistanceSketch_Graph
import Definitions.Def_MaxCompForest_deg
open EffResSparsify.ResistanceSketch
open MeasureTheory
open ProbabilityTheory
set_option autoImplicit false

namespace MaxCompForest.Supplement

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The noise law** `ξ ∼ N(0, σ² D⁻¹)`: independent centered Gaussian coordinates, the coordinate at `v` with
variance `σ²/d_v`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (5.2), p.28.

**Formalization Note.** The product of the Mathlib laws `gaussianReal 0 (σ²/d_v)`. The variance is passed as a
nonnegative real (`toNNReal`); it is positive whenever `σ > 0` and `d_v > 0`, which holds for a connected graph on
at least two vertices. -/
noncomputable def noise (G : WGraph V E) (σ : ℝ) : Measure (V → ℝ) :=
  Measure.pi fun v => gaussianReal 0 (σ ^ 2 / MaxCompForest.deg G v).toNNReal

end MaxCompForest.Supplement


