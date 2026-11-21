-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_PicardItoLevy_F000
-- name    : LevyStochCalc_BSDEJ_PicardItoLevy_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:09:40.272727+00:00
-- url     : https://prove2.me/theorems/6e2f1c81-fbff-40a4-9944-c0d774e7a981
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.PicardItoLevy
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.PicardItoLevy. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_IntegralLocality_F000
import Definitions.Def_LevyStochCalc_BSDEJ_PicardStep_F000
import Definitions.Def_LevyStochCalc_BSDEJ_PicardStep_F001
import Definitions.Def_SourceProof_8a730e00388641e5c85f4c10

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Itô–Lévy decomposition of a Picard output

The output `Y` of a Picard step satisfies the backward equation on the horizon `[0, T]` only.
Frozen at the horizon, `t ↦ Y (min t T)`, it carries an Itô–Lévy decomposition at every
nonnegative time, with drift `-b` for a drift `b` that is almost everywhere the generator along
the input triple, diffusion vector `Z` and jump integrand `U`: subtracting the backward equation
at `t` from the backward equation at `0` turns the remaining window `[t, T]` of the drift
integral into the initial window `[0, t]`, and past the horizon neither the drift integral nor
either stochastic leg moves.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.clampT` — a process frozen at the horizon.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.clampT_decomposition_of_eqn` — the decomposition of a frozen path
  satisfying the backward equation, for abstract stochastic legs.
* `LevyStochCalc.BSDEJ.Solves.PicardOutput.isItoLevyProcess_clampT` — the frozen Picard output
  is an Itô–Lévy process.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Freezing a process at the horizon -/

/-- The process `Y` frozen at the horizon `T`, that is `t ↦ Y (min t T)`. -/
def clampT (T : ℝ) (Y : ℝ → Ω → ℝ) : ℝ → Ω → ℝ := fun t ω => Y (min t T) ω
omit [MeasurableSpace Ω] in
/-- The value of a frozen process is the value of the process at the clamped time. -/
theorem clampT_apply (T : ℝ) (Y : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    clampT T Y t ω = Y (min t T) ω := rfl
omit [MeasurableSpace Ω] in
/-- Before the horizon the frozen process is the process. -/
theorem clampT_apply_of_le {T t : ℝ} (ht : t ≤ T) (Y : ℝ → Ω → ℝ) : clampT T Y t = Y t := by
  funext ω
  rw [clampT_apply, min_eq_left ht]
omit [MeasurableSpace Ω] in
/-- After the horizon the frozen process is the process at the horizon. -/
theorem clampT_apply_of_ge {T t : ℝ} (ht : T ≤ t) (Y : ℝ → Ω → ℝ) : clampT T Y t = Y T := by
  funext ω
  rw [clampT_apply, min_eq_right ht]
/-- The frozen process is jointly measurable. -/
theorem measurable_uncurry_clampT {T : ℝ} {Y : ℝ → Ω → ℝ}
    (hY : Measurable (Function.uncurry Y)) : Measurable (Function.uncurry (clampT T Y)) := by
  have hcomp : Function.uncurry (clampT T Y)
      = Function.uncurry Y ∘ fun p : ℝ × Ω => (min p.1 T, p.2) := rfl
  rw [hcomp]
  exact hY.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
/-! ### The drift integral past the horizon -/

/-- The integral over `[0, t]` of a function vanishing off `[0, T]` is its integral over
`[0, T]`, at every time past the horizon. -/
theorem setIntegral_Icc_eq_of_vanishing {g : ℝ → ℝ} {T t : ℝ} (hTt : T ≤ t)
    (hg : ∀ s, s ∉ Set.Icc (0 : ℝ) T → g s = 0) :
    ∫ s in Set.Icc (0 : ℝ) t, g s = ∫ s in Set.Icc (0 : ℝ) T, g s := by
  have hind : (Set.Icc (0 : ℝ) t).indicator g = (Set.Icc (0 : ℝ) T).indicator g := by
    funext s
    by_cases hsT : s ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem (Set.Icc_subset_Icc le_rfl hTt hsT) g,
        Set.indicator_of_mem hsT g]
    · rw [Set.indicator_of_notMem hsT g]
      by_cases hst : s ∈ Set.Icc (0 : ℝ) t
      · rw [Set.indicator_of_mem hst g]
        exact hg s hsT
      · rw [Set.indicator_of_notMem hst g]
  rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc, hind]
/-! ### The decomposition of a frozen backward path -/

omit [IsProbabilityMeasure P] in
/-- A path satisfying the backward equation on `[0, T]` with drift `b` and stochastic legs
`M^W`, `M^N` vanishing at `0` and constant past `T` has, frozen at the horizon, the
decomposition `Y_{t ∧ T} = Y_0 - ∫_0^t b_s ds + M^W_t + M^N_t` at every nonnegative time. -/
theorem clampT_decomposition_of_eqn {T : ℝ} (hT : 0 < T) {Y : ℝ → Ω → ℝ} {ξ : Ω → ℝ}
    {b : Ω → ℝ → ℝ} {MW MN : ℝ → Ω → ℝ} (hbm : Measurable (Function.uncurry b))
    (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (heqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, Y t ω = ξ ω + (∫ s in Set.Icc t T, b ω s)
      - (MW T ω - MW t ω) - (MN T ω - MN t ω))
    (hW0 : MW 0 =ᵐ[P] 0) (hN0 : MN 0 =ᵐ[P] 0)
    (hWT : ∀ t : ℝ, T ≤ t → MW t =ᵐ[P] MW T)
    (hNT : ∀ t : ℝ, T ≤ t → MN t =ᵐ[P] MN T) :
    ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, clampT T Y t ω
      = Y 0 ω + (∫ s in Set.Icc (0 : ℝ) t, -b ω s) + MW t ω + MN t ω := by
  have hkey : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      Y t ω = Y 0 ω + (∫ s in Set.Icc (0 : ℝ) t, -b ω s) + MW t ω + MN t ω := by
    intro t ht
    filter_upwards [heqn t ht, heqn 0 ⟨le_rfl, hT.le⟩, hW0, hN0, driftLeg_ae_eq hbm hbq T,
      driftLeg_ae_eq hbm hbq t, _root_.Prove2MeSourceProof.h_8a730e00388641e5c85f4c10 hbm hbq ht.1 ht.2] with ω h1 h2 h3 h4 h5 h6 h7
    rw [integral_neg]
    simp only [Pi.zero_apply] at h3 h4
    linarith
  intro t ht
  rcases le_or_gt t T with htT | htT
  · filter_upwards [hkey t ⟨ht, htT⟩] with ω k
    rw [clampT_apply_of_le htT Y]
    exact k
  · have hTt : T ≤ t := htT.le
    have hcut : ∀ ω : Ω, ∫ s in Set.Icc (0 : ℝ) t, -b ω s
        = ∫ s in Set.Icc (0 : ℝ) T, -b ω s := fun ω =>
      setIntegral_Icc_eq_of_vanishing hTt fun s hs => by rw [hbz ω s hs, neg_zero]
    filter_upwards [hkey T ⟨hT.le, le_rfl⟩, hWT t hTt, hNT t hTt] with ω k1 k2 k3
    rw [clampT_apply_of_ge hTt Y, hcut ω, k2, k3]
    exact k1
/-! ### The frozen Picard output -/

end LevyStochCalc.BSDEJ.Solves


