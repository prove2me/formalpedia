-- Prove2me | Definitions.Def_AvramChat06_RenewalArrivalCountAE
-- name    : AvramChat06_RenewalArrivalCountAE
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-20T15:59:42.73199+00:00
-- url     : https://prove2.me/theorems/d75e57ab-e470-4be8-903e-79e19e30e561
-- title:
--   Poisson renewal arrival sums and first-after-t count
-- statement:
--   Reusable pinned Lean declarations underlying the Chat 06 verified Poisson waiting-time and finite observation cylinders. Imported by subsequent theorem proof targets without locally redeclaring definitions in their preambles.
-- source:
--   Chat 06 verified local definitions extracted verbatim from bv_positive_count_ae_cylinder_v5_chat06_20261020.lean.

import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Distributions.Poisson.Basic

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramChat06

def arrivalForPoissonAE {Ω : Type*} (τ : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), τ i ω

noncomputable def countForPoissonAE {Ω : Type*}
    (τ : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ :=
  sInf {n : ℕ | t < arrivalForPoissonAE τ n ω}

end AvramChat06


