-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpTelescope_F000
-- name    : LevyStochCalc_Ito_JumpTelescope_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:54:26.740331+00:00
-- url     : https://prove2.me/theorems/5a55bb90-4a1c-4607-9e63-0039ce40b423
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpTelescope
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpTelescope. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoFinsetSum_F000
import Definitions.Def_LevyStochCalc_Probability_StoppedProgressive_F002
import Definitions.Def_SourceProof_4014cddbf3dd1c22757fef9e
import Definitions.Def_SourceProof_4158bbe01732caa4bdb467b2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Telescoping along a finite chain of stopping times

Along a family `σ : ℕ → Ω → WithTop ℝ` the successive differences of the integrand stopped at
`σ i` sum to the integrand stopped at `σ m` minus the one stopped at `σ 0`. If the chain starts
at or below `0` and has reached past `T` by its `m`-th member, the two boundary terms are the
integrand itself and `0` on the window `(0, T]`, so the telescoped sum recovers the integrand
there. The Itô integral turns such a finite sum of integrands into the sum of the integrals.

## Main statements

* `LevyStochCalc.Brownian.Ito.sum_range_stopped_sub` — the pointwise telescoping identity.
* `LevyStochCalc.Brownian.Ito.sum_range_stopped_eq_of_chain` — a chain covering `(0, T]`
  telescopes to the integrand on that window.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_finsetSum` — the Itô integral of a
  finite sum of integrands, with the admissibility data of the sum supplied explicitly.
* `LevyStochCalc.Brownian.Ito.sum_range_sub_comp` — telescoping of a process sampled along a
  chain of times.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Telescope

variable {Ω : Type*}

/-- The successive differences of an integrand stopped along a family of stopping times sum to
the difference of the two extreme stopped integrands. -/
theorem sum_range_stopped_sub (σ : ℕ → Ω → WithTop ℝ) (K : Ω → ℝ → ℝ) (m : ℕ) (ω : Ω) (s : ℝ) :
    ∑ i ∈ Finset.range m,
        (Probability.stopped (σ (i + 1)) K ω s - Probability.stopped (σ i) K ω s)
      = Probability.stopped (σ m) K ω s - Probability.stopped (σ 0) K ω s :=
  Finset.sum_range_sub (fun i => Probability.stopped (σ i) K ω s) m
/-- On the window `(0, T]` an integrand stopped at a time beyond `T` is the integrand itself. -/
theorem stopped_eq_self_of_mem_Ioc {τ : Ω → WithTop ℝ} (K : Ω → ℝ → ℝ) {ω : Ω} {T : ℝ}
    (hτ : ((T : ℝ) : WithTop ℝ) ≤ τ ω) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) T) :
    Probability.stopped τ K ω s = K ω s := by
  have hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω := le_trans (by exact_mod_cast hs.2) hτ
  simp [Probability.stopped, hle]
/-- At a positive time an integrand stopped at a time at or below `0` vanishes. -/
theorem stopped_eq_zero_of_le_zero {τ : Ω → WithTop ℝ} (K : Ω → ℝ → ℝ) {ω : Ω}
    (hτ : τ ω ≤ ((0 : ℝ) : WithTop ℝ)) {s : ℝ} (hs : 0 < s) :
    Probability.stopped τ K ω s = 0 := by
  have hnle : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := by
    intro hle
    have h0 : ((s : ℝ) : WithTop ℝ) ≤ ((0 : ℝ) : WithTop ℝ) := hle.trans hτ
    have hs0 : s ≤ (0 : ℝ) := by exact_mod_cast h0
    linarith
  simp [Probability.stopped, hnle]
/-- A chain of stopping times starting at or below `0` and reaching past `T` telescopes to the
integrand itself on the window `(0, T]`. -/
theorem sum_range_stopped_eq_of_chain (σ : ℕ → Ω → WithTop ℝ) (K : Ω → ℝ → ℝ) {m : ℕ} {T : ℝ}
    {ω : Ω} (h0 : σ 0 ω ≤ ((0 : ℝ) : WithTop ℝ)) (hm : ((T : ℝ) : WithTop ℝ) ≤ σ m ω)
    {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) T) :
    ∑ i ∈ Finset.range m,
        (Probability.stopped (σ (i + 1)) K ω s - Probability.stopped (σ i) K ω s) = K ω s := by
  rw [sum_range_stopped_sub, stopped_eq_self_of_mem_Ioc K hm hs,
    stopped_eq_zero_of_le_zero K h0 hs.1, sub_zero]
/-- The successive differences of a process sampled along a family of times sum to the difference
of its values at the two extreme times. -/
theorem sum_range_sub_comp (Φ : ℝ → Ω → ℝ) (θ : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.range m, (Φ (θ (i + 1) ω) ω - Φ (θ i ω) ω)
      = Φ (θ m ω) ω - Φ (θ 0 ω) ω :=
  Finset.sum_range_sub (fun i => Φ (θ i ω) ω) m
end Telescope

section Integral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- The Itô integral of a finite sum of integrands is the sum of their integrals, with the
admissibility data of the summed integrand supplied by the caller. -/
theorem stochasticIntegralBrownian_finsetSum {ι : Type*}
    (H : ι → Ω → ℝ → ℝ) (hm : ∀ i, Measurable (Function.uncurry (H i)))
    (hp : ∀ i, Probability.ProgressivelyMeasurable ℱ (H i))
    (hq : ∀ (i : ι) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (J : Finset ι)
    (hms : Measurable (Function.uncurry fun ω u => ∑ i ∈ J, H i ω u))
    (hps : Probability.ProgressivelyMeasurable ℱ fun ω u => ∑ i ∈ J, H i ω u)
    (hqs : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T',
      (‖∑ i ∈ J, H i ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω u => ∑ i ∈ J, H i ω u) hms hps hqs T
      =ᵐ[P] fun ω => ∑ i ∈ J,
        stochasticIntegralBrownian W ℱ hℱ (H i) (hm i) (hp i) (hq i) T ω := by
  classical
  obtain ⟨hms', hps', hqs', hae⟩ :=
    _root_.Prove2MeSourceProof.h_4158bbe01732caa4bdb467b2 W ℱ hℱ H hm hp hq J hT
  rwa [stochasticIntegralBrownian_congr_fun W ℱ hℱ rfl hms hps hqs hms' hps' hqs' T]
end Integral

end LevyStochCalc.Brownian.Ito


