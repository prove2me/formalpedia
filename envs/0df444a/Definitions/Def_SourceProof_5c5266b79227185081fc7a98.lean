-- Prove2me | Definitions.Def_SourceProof_5c5266b79227185081fc7a98
-- name    : SourceProof_5c5266b79227185081fc7a98
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:11:16.878474+00:00
-- url     : https://prove2.me/theorems/9e878478-c00d-4cae-bbcb-15f068b72b8f
-- title:
--   LevyStochCalc source module: SourceProof_5c5266b79227185081fc7a98
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_crossSum` comes from the `LevyStochCalc.Brownian.CrossOrthogonalityDirectCross` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross_F000
import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The direct cross identity for distinct Brownian coordinates

For a `d`-dimensional Brownian motion `W` whose coordinates are all Brownian motions for one
filtration `ℱ`, and distinct coordinates `i ≠ j`, the identity
`E[Z (Wⁱ_b - Wⁱ_a)(Wʲ_b - Wʲ_a)] = 0` holds for a bounded `ℱ_a`-measurable weight `Z`: along a
uniform grid of `[a, b]`, the product of the two increments telescopes into cell-wise terms, the
terms with a past factor are killed by conditioning, and the sum of the cell-wise cross products
has second moment `(b - a)² / m` by the independence of the two coordinates.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

namespace Multidim.MultidimBrownianMotion

section DirectCross


theorem _root_.Prove2MeSourceProof.h_5c5266b79227185081fc7a98 (W : MultidimBrownianMotion P d)
    (i j : Fin d) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (m : ℕ) {Z : Ω → ℝ} (hZ : StronglyMeasurable[ℱ a] Z)
    (hZm : Measurable Z) {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C) :
    ∫ ω, Z ω * (((W.W i).W (affineGrid a h m) ω - (W.W i).W a ω)
      * ((W.W j).W (affineGrid a h m) ω - (W.W j).W a ω)) ∂P
      = ∫ ω, Z ω * ∑ k ∈ Finset.range m,
        ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω) ∂P := by
  have hg0 : ∀ k : ℕ, 0 ≤ LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_nonneg ha hh.le
  have hglt : ∀ k : ℕ, LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k < LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1) := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_lt_succ hh
  have hag : ∀ k : ℕ, a ≤ LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.le_affineGrid hh.le
  have hCabs : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ |C| := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact (hZb ω).trans (le_abs_self C)
  have hAm : ∀ (V : LevyStochCalc.Brownian.BrownianMotion P) (k : ℕ),
      Measurable fun ω => V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - V.W a ω :=
    fun V k => (V.measurable_eval _).sub (V.measurable_eval _)
  -- a bounded coefficient times a past increment is killed by a fresh increment
  have hzero : ∀ (V V' : LevyStochCalc.Brownian.BrownianMotion P), LevyStochCalc.Brownian.IsBrownianFiltration V ℱ →
      LevyStochCalc.Brownian.IsBrownianFiltration V' ℱ → ∀ k : ℕ,
      ∫ ω, Z ω * ((V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - V.W a ω)
        * (V'.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V'.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)) ∂P = 0 := by
    intro V V' hV hV' k
    have hY : StronglyMeasurable[ℱ (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k)] fun ω =>
        Z ω * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - V.W a ω) :=
      (hZ.mono (ℱ.mono (hag k))).mul
        ((hV.measurable _).sub ((hV.measurable a).mono (ℱ.mono (hag k)) le_rfl)).stronglyMeasurable
    have h := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_eq_zero V' hV' (hg0 k) (hglt k) hY (hZm.mul (hAm V k))
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (mul_assoc _ _ _).symm)
  have hintA : ∀ (V V' : LevyStochCalc.Brownian.BrownianMotion P) (k : ℕ), Integrable (fun ω =>
      Z ω * ((V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - V.W a ω)
        * (V'.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V'.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))) P := fun V V' k =>
    Integrable.bdd_mul (MemLp.integrable_mul (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le V ha (hag k))
      (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le V' (hg0 k) (hglt k).le)) hZm.aestronglyMeasurable hCabs
  have hintΔ : ∀ k : ℕ, Integrable (fun ω =>
      Z ω * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
        * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))) P := fun k =>
    Integrable.bdd_mul (MemLp.integrable_mul (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le (W.W i) (hg0 k) (hglt k).le)
      (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le (W.W j) (hg0 k) (hglt k).le)) hZm.aestronglyMeasurable hCabs
  have htel : ∀ ω, Z ω * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h m) ω - (W.W i).W a ω)
        * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h m) ω - (W.W j).W a ω))
      = ∑ k ∈ Finset.range m,
        (Z ω * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - (W.W i).W a ω)
            * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
          + Z ω * (((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - (W.W j).W a ω)
            * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
          + Z ω * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
            * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))) := by
    intro ω
    have h0 := Finset.sum_range_sub (fun k => ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - (W.W i).W a ω)
      * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - (W.W j).W a ω)) m
    simp only [LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_zero, sub_self, mul_zero, sub_zero] at h0
    rw [← h0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hint3 : ∀ k : ℕ, Integrable (fun ω =>
      Z ω * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - (W.W i).W a ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        + Z ω * (((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - (W.W j).W a ω)
          * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        + Z ω * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))) P :=
    fun k => ((hintA (W.W i) (W.W j) k).add (hintA (W.W j) (W.W i) k)).add (hintΔ k)
  have hint12 : ∀ k : ℕ, Integrable (fun ω =>
      Z ω * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - (W.W i).W a ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        + Z ω * (((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω - (W.W j).W a ω)
          * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))) P :=
    fun k => (hintA (W.W i) (W.W j) k).add (hintA (W.W j) (W.W i) k)
  rw [integral_congr_ae (Filter.Eventually.of_forall htel), integral_finsetSum _ fun k _ => hint3 k]
  simp_rw [integral_add (hint12 _) (hintΔ _),
    integral_add (hintA (W.W i) (W.W j) _) (hintA (W.W j) (W.W i) _),
    hzero (W.W i) (W.W j) (hcoord i) (hcoord j), hzero (W.W j) (W.W i) (hcoord j) (hcoord i),
    add_zero, zero_add]
  rw [← integral_finsetSum _ fun k _ => hintΔ k]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (Finset.mul_sum _ _ _).symm)
end DirectCross

end Multidim.MultidimBrownianMotion

end LevyStochCalc.Brownian


