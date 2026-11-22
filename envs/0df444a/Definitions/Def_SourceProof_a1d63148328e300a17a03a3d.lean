-- Prove2me | Definitions.Def_SourceProof_a1d63148328e300a17a03a3d
-- name    : SourceProof_a1d63148328e300a17a03a3d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:52:49.592112+00:00
-- url     : https://prove2.me/theorems/99779844-14b6-472f-ab28-585cf4c49872
-- title:
--   LevyStochCalc source module: SourceProof_a1d63148328e300a17a03a3d
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.exists_globalSolution` comes from the `LevyStochCalc.Ito.PicardGlobal` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardGlobal_F001
import Definitions.Def_LevyStochCalc_Ito_PicardGlobal_F002
import Definitions.Def_SourceProof_000cd4ee6b13d23947f0c539
import Definitions.Def_SourceProof_2885abf558bfdbae518a75a6
import Definitions.Def_SourceProof_bb3bc292bcc4870943aee2a2

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From window solutions to a solution on `[0, ∞)`

The Bielecki contraction produces a solution on each finite window. Uniqueness on the shorter of
two windows makes the family consistent, and right-continuity upgrades that to an almost-sure
agreement of whole paths, so the windows can be glued along `⌈t⌉₊` into a single path map that
restricts to a window solution on every `[0, T]`.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### Right-continuity upgrades per-time equality to path equality -/

/-! ### The glued path map -/

/-! ### Consistency of a family of window solutions -/

section Glue

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)


theorem _root_.Prove2MeSourceProof.h_a1d63148328e300a17a03a3d [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) :
    ∃ X : ℝ → Ω → (Fin n → ℝ),
      Measurable (Function.uncurry X)
        ∧ (∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => X s ω i)
        ∧ (∀ᵐ ω ∂P, X 0 ω = x₀)
        ∧ (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
            Filter.Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (nhds (X t ω))
              ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
                  Filter.Tendsto (fun s => X s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ))
        ∧ (∀ T' : ℝ, 0 < T' →
            ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
        ∧ (∀ T : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) := by
  have hex : ∀ k : ℕ, ∃ Y : ℝ → Ω → (Fin n → ℝ),
      Measurable (Function.uncurry Y)
        ∧ (∀ i : Fin n, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
        ∧ (∀ᵐ ω ∂P, ∀ t : ℝ,
            Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
              ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
                  Filter.Tendsto (fun s => Y s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ))
        ∧ (∀ T' : ℝ, 0 < T' →
            ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
        ∧ LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y ((k : ℝ) + 1) := fun k =>
    _root_.Prove2MeSourceProof.h_2885abf558bfdbae518a75a6 W N ℱ hℱW hℱN coeffs hℱ0 hnull hReg hLip x₀ (by positivity)
  choose Y hYm hYa hYcad hYS hYsol using hex
  have hright : ∀ k, ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => Y k s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y k t ω)) := by
    intro k
    filter_upwards [hYcad k] with ω hω
    exact fun t => (hω t).1
  have hagree := LevyStochCalc.Ito.Picard.ae_globalPatch_eq (Y := Y)
    (LevyStochCalc.Ito.Picard.ae_all_windows_agree W N ℱ hℱW hℱN coeffs hReg hLip x₀ hYm hright hYS hYsol)
  have hsol := _root_.Prove2MeSourceProof.h_000cd4ee6b13d23947f0c539 W N ℱ hℱW hℱN coeffs hReg hLip x₀ hYm hYa hagree hYS hYsol
  exact ⟨LevyStochCalc.Ito.Picard.globalPatch Y, LevyStochCalc.Ito.Picard.measurable_globalPatch hYm,
    fun i => _root_.Prove2MeSourceProof.h_bb3bc292bcc4870943aee2a2 hYa i,
    LevyStochCalc.Ito.Picard.ae_eq_initial_of_solvesOn W N ℱ hℱW hℱN coeffs x₀ zero_le_one (hsol 1),
    LevyStochCalc.Ito.Picard.cadlag_globalPatch hagree hYcad,
    LevyStochCalc.Ito.Picard.lintegral_sq_iSup_globalPatch_lt_top hagree hYS, hsol⟩
end Glue

end LevyStochCalc.Ito.Picard


