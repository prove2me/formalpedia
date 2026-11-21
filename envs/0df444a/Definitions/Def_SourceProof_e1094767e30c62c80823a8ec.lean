-- Prove2me | Definitions.Def_SourceProof_e1094767e30c62c80823a8ec
-- name    : SourceProof_e1094767e30c62c80823a8ec
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:48:01.106741+00:00
-- url     : https://prove2.me/theorems/fcd62389-2c0e-410c-b6aa-c68f8d97039a
-- title:
--   LevyStochCalc source module: SourceProof_e1094767e30c62c80823a8ec
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.ae_ae_tendsto_version_clamp` comes from the `LevyStochCalc.Ito.ItoFormulaUnboundedClamp` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_e1094767e30c62c80823a8ec
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
    (hns : ∀ i : ℕ, clampMesh P H b T (ns i) < ((2 : ℝ≥0∞)⁻¹) ^ i) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Xj (ns i) s ω) Filter.atTop (𝓝 (X s ω)) := by
  have hmeasi : ∀ i : ℕ, Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Xj (ns i) s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro i
    have hjoint : Measurable fun q : Ω × ℝ => (‖Xj (ns i) q.2 q.1 - X q.2 q.1‖₊ : ℝ≥0∞) ^ 2 :=
      ((((hXj (ns i)).measurable_uncurry.sub
        hX.measurable_uncurry).nnnorm).coe_nnreal_ennreal).pow_const 2
    exact hjoint.lintegral_prod_right'
  have hsum : ∑' i : ℕ, ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Xj (ns i) s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun i => ?_)
      (lt_top_iff_ne_top.mpr (LevyStochCalc.Brownian.Ito.tsum_geometric_inv_two_mul_ne_top (ENNReal.ofReal T)
        ENNReal.ofReal_ne_top)))
    refine (LevyStochCalc.Brownian.Ito.lintegral_window_sq_norm_version_clamp_sub_le W ℱ' hcoord hX₀ hbm hbq hX
      (hXj (ns i))).trans ?_
    exact mul_le_mul' le_rfl (hns i).le
  filter_upwards [LevyStochCalc.Brownian.Ito.ae_tsum_ne_top_of_lintegral_summable (μ := P) hmeasi hsum] with ω hω
  have hmeasω : ∀ i : ℕ, Measurable fun s : ℝ => (‖Xj (ns i) s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 := by
    intro i
    have h1 : Measurable fun s : ℝ => Xj (ns i) s ω :=
      ((hXj (ns i)).measurable_uncurry.comp (measurable_const.prodMk measurable_id))
    have h2 : Measurable fun s : ℝ => X s ω :=
      (hX.measurable_uncurry.comp (measurable_const.prodMk measurable_id))
    exact (((h1.sub h2).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hinner := LevyStochCalc.Brownian.Ito.ae_tendsto_zero_of_lintegral_summable
    (μ := volume.restrict (Set.Icc (0 : ℝ) T)) hmeasω hω
  filter_upwards [hinner] with s hs
  exact _root_.Prove2MeSourceProof.h_a4dbeae1c9a6b22bf7020922 hs
end ClampProcess

end Clamped

end LevyStochCalc.Brownian.Ito


