-- Prove2me | Definitions.Def_SourceProof_7c1e051c1c1f9aebd6c80fa9
-- name    : SourceProof_7c1e051c1c1f9aebd6c80fa9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:49:09.064256+00:00
-- url     : https://prove2.me/theorems/f1c62f7c-2c2f-4bcc-b439-7591dcd17d1d
-- title:
--   LevyStochCalc source module: SourceProof_7c1e051c1c1f9aebd6c80fa9
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_of_tendsto_lintegral` comes from the `LevyStochCalc.Ito.ItoFormulaUnboundedClamp` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F002
import Definitions.Def_SourceProof_a4dbeae1c9a6b22bf7020922

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Coefficients of a vector Itô process clamped at a finite level

Clamping the coefficients of a vector Itô process at level `j` leaves bounded coefficients of
finite energy whose distance in energy to the original coefficients tends to `0`, and the process
they drive stays within that distance of the original one in `L²`, uniformly on a bounded window;
along a suitable subsequence of levels the clamped processes converge to the original one almost
surely.

## Main statements

* `LevyStochCalc.Brownian.Ito.clampCoeff`, `clampDrift` — the clamped coefficients.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_window_clamp` — the mesh of the approximation.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Clamped

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section ClampProcess

variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_7c1e051c1c1f9aebd6c80fa9 {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ι : Type*} [Finite ι] {u : ℕ → ι → α → ℝ} {v : ι → α → ℝ}
    (hu : ∀ (i : ℕ) (c : ι), Measurable (u i c)) (hv : ∀ c : ι, Measurable (v c))
    (h : ∀ c : ι, Filter.Tendsto (fun i : ℕ => ∫⁻ a, (‖u i c a - v c a‖₊ : ℝ≥0∞) ^ 2 ∂μ)
      Filter.atTop (𝓝 0)) :
    ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧
      ∀ᵐ a ∂μ, ∀ c : ι, Filter.Tendsto (fun i : ℕ => u (ms i) c a) Filter.atTop (𝓝 (v c a)) := by
  classical
  haveI := Fintype.ofFinite ι
  have hsumTendsto : Filter.Tendsto
      (fun i : ℕ => ∑ c : ι, ∫⁻ a, (‖u i c a - v c a‖₊ : ℝ≥0∞) ^ 2 ∂μ)
      Filter.atTop (𝓝 0) := by
    have hfin := tendsto_finsetSum (Finset.univ : Finset ι) fun c _ => h c
    simpa using hfin
  obtain ⟨ms, hmsge, hmslt⟩ := LevyStochCalc.Brownian.Ito.exists_seq_lt_of_tendsto_zero hsumTendsto
  refine ⟨ms, hmsge, ?_⟩
  rw [MeasureTheory.ae_all_iff]
  intro c
  have hmeasi : ∀ i : ℕ, Measurable fun a : α => (‖u (ms i) c a - v c a‖₊ : ℝ≥0∞) ^ 2 :=
    fun i => ((((hu (ms i) c).sub (hv c)).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hsum : ∑' i : ℕ, ∫⁻ a, (‖u (ms i) c a - v c a‖₊ : ℝ≥0∞) ^ 2 ∂μ ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun i => ?_)
      (lt_top_iff_ne_top.mpr (LevyStochCalc.Brownian.Ito.tsum_geometric_inv_two_mul_ne_top (1 : ℝ≥0∞) (by simp))))
    rw [one_mul]
    refine le_trans ?_ (hmslt i).le
    exact Finset.single_le_sum
      (f := fun c' : ι => ∫⁻ a, (‖u (ms i) c' a - v c' a‖₊ : ℝ≥0∞) ^ 2 ∂μ)
      (fun _ _ => zero_le) (Finset.mem_univ c)
  filter_upwards [LevyStochCalc.Brownian.Ito.ae_tendsto_zero_of_lintegral_summable hmeasi hsum] with a ha
  exact _root_.Prove2MeSourceProof.h_a4dbeae1c9a6b22bf7020922 ha
end ClampProcess

end Clamped

end LevyStochCalc.Brownian.Ito


