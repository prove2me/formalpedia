-- Prove2me | Definitions.Def_SourceProof_5a8f87bfb50175f242169433
-- name    : SourceProof_5a8f87bfb50175f242169433
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:28:05.942215+00:00
-- url     : https://prove2.me/theorems/db52bf57-0d9e-4464-9167-7ef89b67e9eb
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.tendsto_condExpL2_nhdsGT
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_CondExpRightContinuous_F000
import Definitions.Def_SourceProof_b59add09b66261635bbb1418

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Right continuity in `L²` of the conditional expectation along a right-continuous filtration

For a filtration `ℱ` indexed by `ℝ` the σ-algebras `ℱ (t + 1/(n+1))` form an antitone sequence
whose infimum is `⨅ r > t, ℱ r`, which is `ℱ t` when `ℱ` is right-continuous. The `L²`
conditional expectations therefore converge to `𝔼[f | ℱ t]` along that sequence
(`LevyStochCalc.Probability.CondExpInf`), and `r ↦ ‖𝔼[f | ℱ r] − 𝔼[f | ℱ t]‖` is monotone on
`[t, ∞)` because the subspaces `lpMeas (ℱ r)` grow, so the convergence upgrades from the sequence
to the filter `𝓝[>] t`.

## Main statements

* `iInf_filtration_add_one_div` — `⨅ n, ℱ (t + 1/(n+1)) = ⨅ r > t, ℱ r`.
* `tendsto_condExpL2_nhdsGT` — `𝔼[f | ℱ r] → 𝔼[f | ℱ t]` in `L²` as `r ↓ t`.
-/

open Filter MeasureTheory Topology
open scoped MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}

section Sequence

variable (ℱ : Filtration ℝ m₀) (t : ℝ)

end Sequence


theorem _root_.Prove2MeSourceProof.h_5a8f87bfb50175f242169433 (ℱ : Filtration ℝ m₀) [ℱ.IsRightContinuous] (t : ℝ)
    (f : Lp ℝ 2 μ) :
    Tendsto (fun r => ((condExpL2 ℝ ℝ (ℱ.le r) f : Lp ℝ 2 μ))) (𝓝[>] t)
      (𝓝 ((condExpL2 ℝ ℝ (ℱ.le t) f : Lp ℝ 2 μ))) := by
  haveI hFact : ∀ r : ℝ, Fact (ℱ r ≤ m₀) := fun r => ⟨ℱ.le r⟩
  set s : ℕ → ℝ := fun n => t + 1 / (n + 1 : ℝ) with hs
  have hinf : ⨅ n, ℱ (s n) = ℱ t := LevyStochCalc.Probability.iInf_filtration_add_one_div_of_isRightContinuous ℱ t
  have hle_inf : (⨅ n, ℱ (s n)) ≤ m₀ := hinf ▸ ℱ.le t
  haveI : Fact ((⨅ n, ℱ (s n)) ≤ m₀) := ⟨hle_inf⟩
  have key := _root_.Prove2MeSourceProof.h_b59add09b66261635bbb1418 (LevyStochCalc.Probability.antitone_filtration_add_one_div ℱ t)
    (fun n => ℱ.le (s n)) hle_inf f
  have hlimit : ((condExpL2 ℝ ℝ hle_inf f : Lp ℝ 2 μ))
      = ((condExpL2 ℝ ℝ (ℱ.le t) f : Lp ℝ 2 μ)) := by
    change (lpMeas ℝ ℝ (⨅ n, ℱ (s n)) 2 μ).starProjection f
      = (lpMeas ℝ ℝ (ℱ t) 2 μ).starProjection f
    exact LevyStochCalc.Probability.starProjection_congr (congrArg (fun mm => lpMeas ℝ ℝ mm 2 μ) hinf) f
  rw [hlimit] at key
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 key ε hε
  filter_upwards [Ioo_mem_nhdsGT (LevyStochCalc.Probability.lt_add_one_div t N)] with r hr
  refine lt_of_le_of_lt ?_ (hN N le_rfl)
  simp only [dist_eq_norm]
  exact LevyStochCalc.Probability.norm_starProjection_sub_le_of_le (LevyStochCalc.Probability.lpMeas_mono (m₀ := m₀) (ℱ.mono hr.1.le))
    (LevyStochCalc.Probability.lpMeas_mono (m₀ := m₀) (ℱ.mono hr.2.le)) f
end LevyStochCalc.Probability


