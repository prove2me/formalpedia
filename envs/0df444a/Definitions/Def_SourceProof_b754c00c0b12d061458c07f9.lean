-- Prove2me | Definitions.Def_SourceProof_b754c00c0b12d061458c07f9
-- name    : SourceProof_b754c00c0b12d061458c07f9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:09:55.442867+00:00
-- url     : https://prove2.me/theorems/3cc8d303-3719-4eba-a40d-d25058b07935
-- title:
--   LevyStochCalc source module: SourceProof_b754c00c0b12d061458c07f9
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_crossSum_sq` comes from the `LevyStochCalc.Brownian.CrossOrthogonalityDirectCross` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityDirectCross_F000

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


theorem _root_.Prove2MeSourceProof.h_b754c00c0b12d061458c07f9 (W : MultidimBrownianMotion P d) {i j : Fin d} (hij : i ≠ j)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (m : ℕ) :
    Integrable (fun ω => (∑ k ∈ Finset.range m,
        ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)) ^ 2) P
    ∧ ∫ ω, (∑ k ∈ Finset.range m,
        ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)) ^ 2 ∂P
      = m * h ^ 2 := by
  have hg0 : ∀ k : ℕ, 0 ≤ LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_nonneg ha hh.le
  have hglt : ∀ k : ℕ, LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k < LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1) := LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_lt_succ hh
  -- the functional on path space picking out the product of two increments
  have hφ : ∀ k l : ℕ, Measurable fun path : ℝ → ℝ =>
      (path (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) - path (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k))
        * (path (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) - path (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l)) := fun k l => by
    fun_prop
  have hind : ∀ k l : ℕ, IndepFun
      (fun ω => ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
        * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))
      (fun ω => ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
        * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) P :=
    fun k l => LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.indepFun_comp_coord W hij (hφ k l) (hφ k l)
  have hint2 : ∀ (V : LevyStochCalc.Brownian.BrownianMotion P) (k l : ℕ), Integrable
      (fun ω => (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
        * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) P := fun V k l =>
    MemLp.integrable_mul (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le V (hg0 k) (hglt k).le)
      (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_two_increment_of_le V (hg0 l) (hglt l).le)
  have hcov : ∀ (V : LevyStochCalc.Brownian.BrownianMotion P), LevyStochCalc.Brownian.IsBrownianFiltration V ℱ → ∀ k l : ℕ,
      ∫ ω, (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
        * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω) ∂P
        = if k = l then h else 0 := by
    intro V hV k l
    rcases lt_trichotomy k l with hkl | rfl | hlk
    · rw [if_neg hkl.ne]
      exact LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_increment_mul_increment_eq_zero V hV
        (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_mono hh.le hkl.le) (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_mono hh.le hkl) (hg0 l) (hglt l)
    · have hsq := LevyStochCalc.Brownian.Ito.integral_increment_sq V (hg0 k) (hglt k)
      rw [LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_succ_sub] at hsq
      have hsq' : ∫ ω, (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω) ∂P
          = ∫ ω, (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω) ^ 2 ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => (sq _).symm)
      rw [if_pos rfl, hsq', hsq]
    · rw [if_neg hlk.ne']
      rw [show (fun ω => (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))
          = fun ω => (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
            * (V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - V.W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω) from
        funext fun ω => mul_comm _ _]
      exact LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_increment_mul_increment_eq_zero V hV
        (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_mono hh.le hlk.le) (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid_mono hh.le hlk) (hg0 k) (hglt k)
  have hterm : ∀ k l : ℕ,
      ∫ ω, (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) ∂P
        = if k = l then h ^ 2 else 0 := by
    intro k l
    have hrw : (fun ω => (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)))
        = fun ω => (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))
        * (((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) := by
      funext ω; ring
    rw [hrw]
    have hmul := (hind k l).integral_mul_eq_mul_integral
      (hint2 (W.W i) k l).1 (hint2 (W.W j) k l).1
    rw [show ∫ ω, (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))
        * (((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) ∂P
        = (∫ ω, ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω) ∂P)
        * ∫ ω, ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω) ∂P from hmul,
      hcov (W.W i) (hcoord i) k l, hcov (W.W j) (hcoord j) k l]
    by_cases hkl : k = l
    · simp [hkl, sq]
    · simp [hkl]
  have hint : ∀ k l : ℕ, Integrable
      (fun ω => (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))) P := by
    intro k l
    have hrw : (fun ω => (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)))
        = fun ω => (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω))
        * (((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) := by
      funext ω; ring
    rw [hrw]
    exact (hind k l).integrable_mul (hint2 (W.W i) k l) (hint2 (W.W j) k l)
  have hexp : (fun ω => (∑ k ∈ Finset.range m,
        ((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)) ^ 2)
      = fun ω => ∑ k ∈ Finset.range m, ∑ l ∈ Finset.range m,
        (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (k + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h k) ω))
        * (((W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W i).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)
          * ((W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h (l + 1)) ω - (W.W j).W (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.affineGrid a h l) ω)) := by
    funext ω
    rw [sq, Finset.sum_mul_sum]
  rw [hexp]
  refine ⟨integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l, ?_⟩
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  simp_rw [integral_finsetSum _ fun l _ => hint _ l, hterm, Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl fun x hx => if_pos hx, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
end DirectCross

end Multidim.MultidimBrownianMotion

end LevyStochCalc.Brownian


