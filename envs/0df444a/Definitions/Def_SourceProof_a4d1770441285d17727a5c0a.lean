-- Prove2me | Definitions.Def_SourceProof_a4d1770441285d17727a5c0a
-- name    : SourceProof_a4d1770441285d17727a5c0a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:13:14.366106+00:00
-- url     : https://prove2.me/theorems/ca5f650e-64c6-4f56-ad36-133fee71ebfd
-- title:
--   LevyStochCalc source module: SourceProof_a4d1770441285d17727a5c0a
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_increment_mul_increment_eq_zero` comes from the `LevyStochCalc.Brownian.CrossOrthogonalityDirectCross` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_5c5266b79227185081fc7a98
import Definitions.Def_SourceProof_b754c00c0b12d061458c07f9

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


theorem _root_.Prove2MeSourceProof.h_a4d1770441285d17727a5c0a (W : MultidimBrownianMotion P d) {i j : Fin d}
    (hij : i ≠ j) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[ℱ a] Z) (hZm : Measurable Z) {C : ℝ}
    (hZb : ∀ ω, |Z ω| ≤ C) :
    ∫ ω, Z ω * (((W.W i).W b ω - (W.W i).W a ω) * ((W.W j).W b ω - (W.W j).W a ω)) ∂P = 0 := by
  set I := ∫ ω, Z ω * (((W.W i).W b ω - (W.W i).W a ω) * ((W.W j).W b ω - (W.W j).W a ω)) ∂P
    with hI
  have hC : ∀ ω, |Z ω| ≤ |C| := fun ω => (hZb ω).trans (le_abs_self C)
  have hCabs : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ |C| :=
    Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω
  have hbound : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ,
      |I| ≤ |C| * ε / 2 + |C| * (b - a) ^ 2 / (2 * ε) * (1 / ((m : ℝ) + 1)) := by
    intro ε hε m
    have hnpos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have hh : 0 < (b - a) / (m + 1 : ℕ) := div_pos (by linarith) hnpos
    have hgm : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (m + 1) = b := by
      simp only [LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid]
      field_simp
      ring
    obtain ⟨hQ2int, hQ2⟩ := _root_.Prove2MeSourceProof.h_b754c00c0b12d061458c07f9 W hij hcoord ha hh (m + 1)
    have hI' := _root_.Prove2MeSourceProof.h_5c5266b79227185081fc7a98 W i j hcoord ha hh (m + 1) hZ
      hZm hZb
    rw [hgm] at hI'
    rw [hI, hI']
    have hg0 : ∀ k : ℕ, 0 ≤ LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_nonneg ha hh.le
    have hglt : ∀ k : ℕ, LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k
        < LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1) := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_lt_succ hh
    have hQint : Integrable (fun ω => ∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)) P :=
      integrable_finsetSum _ fun k _ => MemLp.integrable_mul
        (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le (W.W i) (hg0 k) (hglt k).le)
        (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le (W.W j) (hg0 k) (hglt k).le)
    have hZQ := Integrable.bdd_mul hQint hZm.aestronglyMeasurable hCabs
    -- the arithmetic-geometric bound
    have hpt : ∀ ω, |Z ω * ∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)|
        ≤ |C| * ε / 2 + |C| / (2 * ε) * (∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)) ^ 2 := by
      intro ω
      generalize (∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)) = Q
      have hQ : |Q| ≤ ε / 2 + Q ^ 2 / (2 * ε) := by
        rw [div_add_div _ _ two_ne_zero (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (ε - |Q|), sq_abs Q]
      calc |Z ω * Q| = |Z ω| * |Q| := abs_mul _ _
        _ ≤ |C| * (ε / 2 + Q ^ 2 / (2 * ε)) :=
          mul_le_mul (hC ω) hQ (abs_nonneg _) (abs_nonneg _)
        _ = |C| * ε / 2 + |C| / (2 * ε) * Q ^ 2 := by ring
    calc |∫ ω, Z ω * ∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω) ∂P|
        ≤ ∫ ω, |Z ω * ∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)| ∂P :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ ω, (|C| * ε / 2 + |C| / (2 * ε) * (∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)) ^ 2) ∂P :=
          integral_mono hZQ.abs ((integrable_const _).add (hQ2int.const_mul _)) hpt
      _ = |C| * ε / 2 + |C| / (2 * ε) * ((m + 1 : ℕ) * ((b - a) / (m + 1 : ℕ)) ^ 2) := by
          rw [integral_add (integrable_const _) (hQ2int.const_mul _), integral_const,
            integral_const_mul, hQ2]
          simp
      _ = |C| * ε / 2 + |C| * (b - a) ^ 2 / (2 * ε) * (1 / ((m : ℝ) + 1)) := by
          have hn : ((m : ℝ) + 1) ≠ 0 := by positivity
          push_cast
          rw [div_pow, mul_div_assoc', sq ((m : ℝ) + 1), mul_div_mul_left _ _ hn]
          ring
  have hlim : ∀ ε : ℝ, 0 < ε → |I| ≤ |C| * ε / 2 := by
    intro ε hε
    have ht : Filter.Tendsto (fun m : ℕ =>
        |C| * ε / 2 + |C| * (b - a) ^ 2 / (2 * ε) * (1 / ((m : ℝ) + 1))) Filter.atTop
        (nhds (|C| * ε / 2 + |C| * (b - a) ^ 2 / (2 * ε) * 0)) :=
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _)
    rw [mul_zero, add_zero] at ht
    exact ge_of_tendsto' ht (hbound ε hε)
  have hI0 : |I| ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have h1 := hlim (|I| / (|C| + 1)) (by positivity)
    have h2 : |C| * (|I| / (|C| + 1)) ≤ |I| := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg C, abs_nonneg I]
    linarith
  exact abs_nonpos_iff.mp hI0
end DirectCross

end Multidim.MultidimBrownianMotion

end LevyStochCalc.Brownian


