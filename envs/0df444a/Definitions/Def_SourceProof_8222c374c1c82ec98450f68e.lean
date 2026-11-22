-- Prove2me | Definitions.Def_SourceProof_8222c374c1c82ec98450f68e
-- name    : SourceProof_8222c374c1c82ec98450f68e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:18:05.765716+00:00
-- url     : https://prove2.me/theorems/3cbea8c8-2f8e-44ec-a357-21df47d2dd7b
-- title:
--   LevyStochCalc source module: SourceProof_8222c374c1c82ec98450f68e
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.exists_progressive_energy_limit_of_window` comes from the `LevyStochCalc.BSDEJ.PicardLimit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardLimit_F000
import Definitions.Def_SourceProof_27f689978bb8ca67ff7e2231

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The limit of the Picard iterates and existence of a solution

The Picard iterates of a backward equation with jumps are Cauchy for the energy of the value
process, for the energies of the diffusion coordinates and for the marked energy of the jump
integrand, so completeness of the admissible integrands produces an admissible limit triple
which the iterates approach in the exponentially weighted norm at the Young weight
`max 2 (24 L²)`. A further Picard step along the limit triple contracts that distance by `1/4`
against every iterate, so its output is at zero weighted distance from the limit triple; a
Lipschitz generator takes the same value along two triples agreeing almost everywhere on
`Ω × [0, T]`, so the output is its own Picard output and solves the equation.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.PicardOutput.congr_inputs` — a Picard output along one input
  triple is a Picard output along any input triple agreeing with it almost everywhere on the
  horizon.
* `LevyStochCalc.BSDEJ.Solves.exists_admissible_wNorm_limit` — an energy-Cauchy sequence of
  admissible triples converges in the weighted norm to an admissible triple.
* `LevyStochCalc.BSDEJ.Solves.exists_solvesBSDEJ` — a backward equation with jumps whose
  generator is Lipschitz and square integrable at the origin and whose terminal datum is square
  integrable has a solution.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Barles–Buckdahn–Pardoux, *BSDEs and integral-partial differential equations*, Stochastics 60
  (1997), §2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Truncation to the horizon -/

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_8222c374c1c82ec98450f68e (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} {H : ℕ → Ω → ℝ → ℝ} (hm : ∀ n, Measurable (Function.uncurry (H n)))
    (hp : ∀ n, Probability.ProgressivelyMeasurable ℱ (H n))
    (hfin : ∀ n, Brownian.Ito.energy P T (H n) ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Brownian.Ito.energy P T (fun ω s => H m ω s - H n ω s) < ε) :
    ∃ K : Ω → ℝ → ℝ, Measurable (Function.uncurry K)
      ∧ Probability.ProgressivelyMeasurable ℱ K
      ∧ Brownian.Ito.energy P T K ≠ ⊤
      ∧ Tendsto (fun n => Brownian.Ito.energy P T (fun ω s => H n ω s - K ω s))
          atTop (𝓝 0) := by
  classical
  set H' : ℕ → Ω → ℝ → ℝ :=
    fun n ω s => (Set.Icc (0 : ℝ) T).indicator (fun _ => H n ω s) s with hH'
  have hval : ∀ (n : ℕ) (ω : Ω), ∀ s ∈ Set.Icc (0 : ℝ) T, H' n ω s = H n ω s :=
    fun n ω s hs => Set.indicator_of_mem hs _
  have hm' : ∀ n, Measurable (Function.uncurry (H' n)) := by
    intro n
    have heq : Function.uncurry (H' n)
        = (Prod.snd ⁻¹' Set.Icc (0 : ℝ) T).indicator (Function.uncurry (H n)) := by
      funext p
      by_cases hp : p.2 ∈ Set.Icc (0 : ℝ) T
      · simp [hH', Function.uncurry, hp]
      · simp [hH', Function.uncurry, hp, Set.indicator_of_notMem]
    rw [heq]
    exact (hm n).indicator (measurable_snd measurableSet_Icc)
  have hz' : ∀ (n : ℕ) (ω : Ω), ∀ s ∉ Set.Icc (0 : ℝ) T, H' n ω s = 0 :=
    fun n ω s hs => Set.indicator_of_notMem hs _
  have hfin' : ∀ n, LevyStochCalc.Brownian.Ito.energy P T (H' n) ≠ ⊤ := by
    intro n
    have he : LevyStochCalc.Brownian.Ito.energy P T (H' n) = LevyStochCalc.Brownian.Ito.energy P T (H n) :=
      LevyStochCalc.BSDEJ.Solves.energy_congr_on_Icc (hval n)
    rw [he]
    exact hfin n
  have hcau' : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      LevyStochCalc.Brownian.Ito.energy P T (fun ω s => H' m ω s - H' n ω s) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcau ε hε
    refine ⟨N, fun m hmN n hnN => ?_⟩
    have he : LevyStochCalc.Brownian.Ito.energy P T (fun ω s => H' m ω s - H' n ω s)
        = LevyStochCalc.Brownian.Ito.energy P T (fun ω s => H m ω s - H n ω s) :=
      LevyStochCalc.BSDEJ.Solves.energy_congr_on_Icc fun ω s hs => by rw [hval m ω s hs, hval n ω s hs]
    rw [he]
    exact hN m hmN n hnN
  obtain ⟨K, hKm, hKp, -, hKq, hKt⟩ := _root_.Prove2MeSourceProof.h_27f689978bb8ca67ff7e2231 ℱ hm'
    (fun n => LevyStochCalc.BSDEJ.Solves.progressivelyMeasurable_indicator_time (hp n) measurableSet_Icc) hz' hfin' hcau'
  refine ⟨K, hKm, hKp, hKq, ?_⟩
  have heq : (fun n => LevyStochCalc.Brownian.Ito.energy P T (fun ω s => H n ω s - K ω s))
      = fun n => LevyStochCalc.Brownian.Ito.energy P T (fun ω s => H' n ω s - K ω s) := by
    funext n
    exact LevyStochCalc.BSDEJ.Solves.energy_congr_on_Icc fun ω s hs => by rw [hval n ω s hs]
  rw [heq]
  exact hKt
/-! ### Changing the input triple of a Picard step on a null set -/

/-! ### Triples at zero weighted distance -/

/-! ### The weighted norm against the energies -/

/-! ### The limit of an energy-Cauchy sequence of admissible triples -/

section Limit

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {T : ℝ}

end Limit

/-! ### The fixed point of the Picard step -/

section FixedPoint

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ}

end FixedPoint

/-! ### Existence of a solution -/

end LevyStochCalc.BSDEJ.Solves


