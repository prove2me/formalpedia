-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross_F000
-- name    : LevyStochCalc_Brownian_CrossOrthogonalityDirectCross_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:08:23.077167+00:00
-- url     : https://prove2.me/theorems/a7ff17f2-4357-4ce3-8f8b-713f113c95fe
-- title:
--   Source declarations: LevyStochCalc.Brownian.CrossOrthogonalityDirectCross
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.CrossOrthogonalityDirectCross. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_AugmentedFiltration_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentLintegral_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoFourthMomentLintegral_F001
import Definitions.Def_LevyStochCalc_Brownian_MultidimFiltered_F000
import Definitions.Def_SourceProof_947c94e08f8784ad6039b2d1

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

/-- Every coordinate is a Brownian motion for the augmented joint natural filtration. -/
theorem isBrownianFiltration_augNatural (W : MultidimBrownianMotion P d) (j : Fin d) :
    IsBrownianFiltration (W.W j) (augFiltration W.naturalFiltration P) :=
  isBrownianFiltration_augFiltration ((_root_.Prove2MeSourceProof.h_947c94e08f8784ad6039b2d1 W) j)
section DirectCross

/-- Borel functionals of the paths of two distinct coordinates are independent. -/
lemma indepFun_comp_coord (W : MultidimBrownianMotion P d) {i j : Fin d} (hij : i ≠ j)
    {φ ψ : (ℝ → ℝ) → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) :
    IndepFun (fun ω => φ fun t => (W.W i).W t ω) (fun ω => ψ fun t => (W.W j).W t ω) P :=
  (W.components_independent.indepFun hij).comp hφ hψ
/-- An increment of a Brownian motion over a possibly degenerate interval is square-integrable. -/
lemma memLp_two_increment_of_le (V : BrownianMotion P) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    MemLp (fun ω => V.W q ω - V.W p ω) 2 P := by
  rcases eq_or_lt_of_le hpq with h | h
  · subst h
    simp only [sub_self]
    exact memLp_const 0
  · exact Ito.memLp_increment V hp h 2 (by simp)
/-- Increments of a Brownian motion over two intervals, the second starting after the first
ends, are uncorrelated. -/
lemma integral_increment_mul_increment_eq_zero (V : BrownianMotion P)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hV : IsBrownianFiltration V ℱ) {p q r v : ℝ}
    (hpr : p ≤ r) (hqr : q ≤ r) (hr : 0 ≤ r) (hrv : r < v) :
    ∫ ω, (V.W q ω - V.W p ω) * (V.W v ω - V.W r ω) ∂P = 0 := by
  have hY : StronglyMeasurable[ℱ r] fun ω => V.W q ω - V.W p ω :=
    (((hV.measurable q).mono (ℱ.mono hqr) le_rfl).sub
      ((hV.measurable p).mono (ℱ.mono hpr) le_rfl)).stronglyMeasurable
  have hYm : Measurable fun ω => V.W q ω - V.W p ω :=
    (V.measurable_eval q).sub (V.measurable_eval p)
  have h := _root_.Prove2MeSourceProof.h_2f34208c7b9f4e759c37de78 V ℱ hV hr hrv hY hYm 1
  rw [Ito.integral_increment_pow_odd V hr hrv odd_one, mul_zero] at h
  simpa only [pow_one] using h
/-- The uniform grid `a, a + h, a + 2h, …`. -/
noncomputable def affineGrid (a h : ℝ) (k : ℕ) : ℝ := a + k * h
lemma affineGrid_zero (a h : ℝ) : affineGrid a h 0 = a := by simp [affineGrid]
lemma affineGrid_succ_sub (a h : ℝ) (k : ℕ) : affineGrid a h (k + 1) - affineGrid a h k = h := by
  simp only [affineGrid, Nat.cast_succ]; ring
lemma affineGrid_mono {a h : ℝ} (hh : 0 ≤ h) {k l : ℕ} (hkl : k ≤ l) :
    affineGrid a h k ≤ affineGrid a h l := by
  simp only [affineGrid]
  have hkl' : (k : ℝ) ≤ l := Nat.cast_le.2 hkl
  nlinarith
lemma affineGrid_lt_succ {a h : ℝ} (hh : 0 < h) (k : ℕ) :
    affineGrid a h k < affineGrid a h (k + 1) := by
  have := affineGrid_succ_sub a h k
  linarith
lemma le_affineGrid {a h : ℝ} (hh : 0 ≤ h) (k : ℕ) : a ≤ affineGrid a h k := by
  simpa [affineGrid_zero] using affineGrid_mono (a := a) hh (Nat.zero_le k)
lemma affineGrid_nonneg {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (k : ℕ) : 0 ≤ affineGrid a h k :=
  ha.trans (le_affineGrid hh k)
end DirectCross

end Multidim.MultidimBrownianMotion

end LevyStochCalc.Brownian


