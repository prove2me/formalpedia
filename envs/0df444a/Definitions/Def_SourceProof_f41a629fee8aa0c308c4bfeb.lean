-- Prove2me | Definitions.Def_SourceProof_f41a629fee8aa0c308c4bfeb
-- name    : SourceProof_f41a629fee8aa0c308c4bfeb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:52:50.851175+00:00
-- url     : https://prove2.me/theorems/423bafa5-b800-4c2f-9190-059532babd3d
-- title:
--   LevyStochCalc source module: SourceProof_f41a629fee8aa0c308c4bfeb
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.ae_tendsto_version_clamp_at` comes from the `LevyStochCalc.Ito.ItoFormulaUnboundedClamp` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_f41a629fee8aa0c308c4bfeb
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Xj : ℕ → ℝ → Ω → Fin n → ℝ}
    (hX : IsVectorItoVersion W ℱ' hcoord H hm hpg hq X₀ b X)
    (hXj : ∀ j : ℕ, IsVectorItoVersion W ℱ' hcoord (clampCoeff H j)
      (fun p k => measurable_clampCoeff hm j p k)
      (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
      (fun p k T' hT' => energy_clampCoeff_lt_top j p k T' hT')
      X₀ (clampDrift b j) (Xj j))
    {T : ℝ} {ns : ℕ → ℕ}
    (hns : ∀ i : ℕ, clampMesh P H b T (ns i) < ((2 : ℝ≥0∞)⁻¹) ^ i)
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) :
    ∀ᵐ ω ∂P, Filter.Tendsto (fun i => Xj (ns i) s ω) Filter.atTop (𝓝 (X s ω)) := by
  have hmeasi : ∀ i : ℕ, Measurable fun ω : Ω =>
      (‖Xj (ns i) s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 := by
    intro i
    have h1 : Measurable fun ω : Ω => Xj (ns i) s ω := (hXj (ns i)).measurable s
    have h2 : Measurable fun ω : Ω => X s ω := hX.measurable s
    exact (((h1.sub h2).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hsum : ∑' i : ℕ, ∫⁻ ω, (‖Xj (ns i) s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≠ ⊤ := by
    have hgeom := LevyStochCalc.Brownian.Ito.tsum_geometric_inv_two_mul_ne_top (1 : ℝ≥0∞) (by simp)
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun i => ?_)
      (lt_top_iff_ne_top.mpr hgeom))
    refine (LevyStochCalc.Brownian.Ito.lintegral_sq_norm_version_clamp_sub_le W ℱ' hcoord hX₀ hbm hbq hX
      (hXj (ns i)) hs hsT).trans ?_
    rw [one_mul]
    exact (hns i).le
  filter_upwards [LevyStochCalc.Brownian.Ito.ae_tendsto_zero_of_lintegral_summable (μ := P) hmeasi hsum] with ω hω
  exact _root_.Prove2MeSourceProof.h_a4dbeae1c9a6b22bf7020922 hω
end ClampProcess

end Clamped

end LevyStochCalc.Brownian.Ito


