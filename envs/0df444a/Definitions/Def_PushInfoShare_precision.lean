-- Prove2me | Definitions.Def_PushInfoShare_precision
-- name    : PushInfoShare_precision
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:45:05.264148+00:00
-- url     : https://prove2.me/theorems/7dcc6ad3-336d-48a0-b79d-87997fd5cf3d
-- title:
--   Precision $t_i$ of a signal
-- statement:
--   The precision of manufacturer $i$'s signal is
--   $$t_i=\frac{1}{E[\mathbb V(Y_i\mid\theta)]}.$$
--   All accuracies of the model are built from it.
--
--   **Formalization Note** Under $E[Y_i\mid\theta]=\theta$ one has $E[\mathbb V(Y_i\mid\theta)]=E[(Y_i-\theta)^2]$, and that integral is the definition here.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), §3, p.8

import Mathlib

open MeasureTheory

namespace PushInfoShare

/-- The precision `tᵢ = 1 / E[𝕍(Yᵢ | θ)]` of manufacturer `i`'s signal, Jain, SSRN:3388957
(PDF of 2021-04-25), §3, p.8.

**Formalization Note.** Under Assumption 1(a) `E[𝕍(Yᵢ | θ)] = E[(Yᵢ − θ)²]`, and that integral is
used here. On an `IsSignalModel` it is positive, so the division is genuine. -/
noncomputable def precision {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θ : Ω → ℝ)
    (Y : Fin 2 → Ω → ℝ) (i : Fin 2) : ℝ :=
  1 / ∫ ω, (Y i ω - θ ω) ^ 2 ∂μ

end PushInfoShare


