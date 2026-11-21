-- Prove2me | Definitions.Def_SourceProof_8ff28f8ca301aab034421e84
-- name    : SourceProof_8ff28f8ca301aab034421e84
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:20:52.510654+00:00
-- url     : https://prove2.me/theorems/e19d64ba-3bc3-44a3-bc6b-2287549a9f71
-- title:
--   LevyStochCalc source module: SourceProof_8ff28f8ca301aab034421e84
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.pairing_value_characterMultidim_eq_zero` comes from the `LevyStochCalc.Brownian.PRPMultidim` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPMultidim_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# One window of the multidimensional Brownian predictable representation

A weight orthogonal to every coordinate's Itô integrals is orthogonal to the integrals against
any unit linear combination of the coordinates, so the one-window statement transfers, and a
multidimensional cell character is a scalar character of the combination.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}


theorem _root_.Prove2MeSourceProof.h_8ff28f8ca301aab034421e84 (W : Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {Z : Ω → ℂ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) Z)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (c : ℕ → Fin d → ℝ) (n : ℕ)
    (hlt : ∀ k, k < n → τ k < τ (k + 1)) :
    ∫ ω, Z ω * Complex.exp (((∑ i, ∑ k ∈ Finset.Ico 1 (n + 1),
      c k i * (W.W i).W (τ k) ω : ℝ) : ℂ) * Complex.I) ∂P = 0 := by
  have hkey := LevyStochCalc.Brownian.Ito.pairing_gridCharacterMultidim_eq_zero W ℱ hℱi hℱB hℱ0 hnull hτ0 hZm hZ2 hperp hZ0
    (fun k i => ∑ j ∈ Finset.Ico (k + 1) (n + 1), c j i) n hlt
  refine Eq.trans (integral_congr_ae ?_) hkey
  have hinit : ∀ᵐ ω ∂P, ∀ i : Fin d, (W.W i).W 0 ω = 0 :=
    ae_all_iff.mpr fun i => (W.W i).initial_zero
  filter_upwards [hinit] with ω hω
  have heq : (∑ k ∈ Finset.range n, ∑ i, (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j i)
        * ((W.W i).W (τ (k + 1)) ω - (W.W i).W (τ k) ω))
      = ∑ i, ∑ k ∈ Finset.Ico 1 (n + 1), c k i * (W.W i).W (τ k) ω := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ =>
      _root_.Prove2MeSourceProof.h_3bb40c5e7df4a1af88374480 (fun k => c k i) (Wv := fun k => (W.W i).W (τ k) ω)
        (by rw [hτ0]; exact hω i) n
  rw [LevyStochCalc.Brownian.Ito.gridCharacterMultidim_eq_exp, heq]
end LevyStochCalc.Brownian.Ito


