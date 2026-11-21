-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_PRPMultidim_F000
-- name    : LevyStochCalc_Brownian_PRPMultidim_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:17:07.004216+00:00
-- url     : https://prove2.me/theorems/64adc67d-02c4-4540-b943-904aa9740872
-- title:
--   Source declarations: LevyStochCalc.Brownian.PRPMultidim
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.PRPMultidim. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoDriverLinear_F000
import Definitions.Def_LevyStochCalc_Brownian_PRPGrid_F001
import Definitions.Def_SourceProof_b23612bd7f724e39ce57d7eb

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

/-- **One window, multidimensional.** A square-integrable weight orthogonal to every
coordinate's Itô integrals, times a bounded weight measurable before the window and of mean
zero, is orthogonal to the character of the vector of Brownian increments across the window. -/
theorem pairing_cell_multidim_eq_zero (W : Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℂ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) Z)
    {V : Ω → ℂ} (hVm : Measurable V) {Mv : ℝ} (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, ‖V ω‖ ≤ Mv)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℂ _ (ℱ a) V)
    (hZV : ∫ ω, Z ω * V ω ∂P = 0) (lam : Fin d → ℝ) :
    ∫ ω, Z ω * V ω * Complex.exp
      (((∑ i, lam i * ((W.W i).W b ω - (W.W i).W a ω) : ℝ) : ℂ) * Complex.I) ∂P = 0 := by
  classical
  by_cases hzero : ∀ i, lam i = 0
  · have h1 : ∀ ω : Ω, Complex.exp
        (((∑ i, lam i * ((W.W i).W b ω - (W.W i).W a ω) : ℝ) : ℂ) * Complex.I) = 1 := by
      intro ω
      have hs : (∑ i, lam i * ((W.W i).W b ω - (W.W i).W a ω)) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hzero i, zero_mul]
      rw [hs]
      simp
    simpa only [h1, mul_one] using hZV
  · obtain ⟨j, hj⟩ := not_forall.mp hzero
    have hsum_pos : 0 < ∑ i, lam i ^ 2 := by
      refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ j, ?_⟩
      rcases lt_trichotomy (lam j) 0 with h | h | h
      · nlinarith
      · exact absurd h hj
      · nlinarith
    have hn_pos : 0 < Real.sqrt (∑ i, lam i ^ 2) := Real.sqrt_pos.mpr hsum_pos
    have hc : ∑ i, (lam i / Real.sqrt (∑ k, lam k ^ 2)) ^ 2 = 1 := by
      simp only [div_pow]
      rw [← Finset.sum_div, Real.sq_sqrt hsum_pos.le]
      exact div_self hsum_pos.ne'
    have hexp : ∀ ω : Ω, (∑ i, lam i * ((W.W i).W b ω - (W.W i).W a ω))
        = Real.sqrt (∑ k, lam k ^ 2)
          * (Multidim.MultidimBrownianMotion.combine W
              (fun i => lam i / Real.sqrt (∑ k, lam k ^ 2)) b ω
            - Multidim.MultidimBrownianMotion.combine W
              (fun i => lam i / Real.sqrt (∑ k, lam k ^ 2)) a ω) := by
      intro ω
      rw [Multidim.MultidimBrownianMotion.combine_sub, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    have hcell := _root_.Prove2MeSourceProof.h_1c13a49ea3c40dba0c47df8d (W := Multidim.MultidimBrownianMotion.combineBM W hc)
      (ℱ := ℱ) (hℱ := hℱB hc) hℱ0 hnull ha hab hZm hZ2
      (_root_.Prove2MeSourceProof.h_b23612bd7f724e39ce57d7eb W hc ℱ (hℱB hc) hℱi hZ2 hperp)
      hVm hMv0 hVb hVa hZV (Real.sqrt (∑ k, lam k ^ 2))
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)) hcell
    simp only [hexp ω]
    rfl
/-- The character of the vector of increments of `W` along the first `n` cells of a grid. -/
noncomputable def gridCharacterMultidim (W : Multidim.MultidimBrownianMotion P d) (τ : ℕ → ℝ)
    (lam : ℕ → Fin d → ℝ) (n : ℕ) (ω : Ω) : ℂ :=
  ∏ k ∈ Finset.range n, Complex.exp
    (((∑ i, lam k i * ((W.W i).W (τ (k + 1)) ω - (W.W i).W (τ k) ω) : ℝ) : ℂ) * Complex.I)
theorem norm_gridCharacterMultidim (W : Multidim.MultidimBrownianMotion P d) (τ : ℕ → ℝ)
    (lam : ℕ → Fin d → ℝ) (n : ℕ) (ω : Ω) : ‖gridCharacterMultidim W τ lam n ω‖ = 1 := by
  rw [gridCharacterMultidim, norm_prod]
  exact Finset.prod_eq_one fun k _ => Complex.norm_exp_ofReal_mul_I _
/-- The character of the first `n` cells is measurable for the filtration at the `n`-th grid
point. -/
theorem measurable_gridCharacterMultidim (W : Multidim.MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    {τ : ℕ → ℝ} {n : ℕ} (hτ : ∀ k, k < n → τ k ≤ τ (k + 1)) (lam : ℕ → Fin d → ℝ) :
    Measurable[ℱ (τ n)] (gridCharacterMultidim W τ lam n) := by
  refine Finset.measurable_prod _ fun k hk => ?_
  have hkn : k < n := Finset.mem_range.mp hk
  have hk1 : τ (k + 1) ≤ τ n := grid_le hτ hkn (le_refl n)
  have hk0 : τ k ≤ τ n := grid_le hτ hkn.le (le_refl n)
  refine Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp ?_).mul measurable_const)
  refine Finset.measurable_sum _ fun i _ => Measurable.const_mul ?_ _
  exact (((hℱi i).measurable _).mono (ℱ.mono hk1) le_rfl).sub
    (((hℱi i).measurable _).mono (ℱ.mono hk0) le_rfl)
/-- **The multidimensional grid induction.** -/
theorem pairing_gridCharacterMultidim_eq_zero (W : Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {Z : Ω → ℂ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) Z)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (lam : ℕ → Fin d → ℝ) :
    ∀ n : ℕ, (∀ k, k < n → τ k < τ (k + 1)) →
      ∫ ω, Z ω * gridCharacterMultidim W τ lam n ω ∂P = 0 := by
  intro n
  induction n with
  | zero =>
      intro _
      have h1 : ∀ ω : Ω, Z ω * gridCharacterMultidim W τ lam 0 ω = Z ω := by
        intro ω; rw [gridCharacterMultidim]; simp
      simpa only [h1] using hZ0
  | succ n ih =>
      intro hlt
      have hlt' : ∀ k, k < n → τ k < τ (k + 1) := fun k hk => hlt k (Nat.lt_succ_of_lt hk)
      have hle' : ∀ k, k < n → τ k ≤ τ (k + 1) := fun k hk => (hlt' k hk).le
      have hτn0 : 0 ≤ τ n := by
        rw [← hτ0]; exact grid_le hle' (Nat.zero_le n) le_rfl
      have hstep := pairing_cell_multidim_eq_zero W ℱ hℱi hℱB hℱ0 hnull hτn0
        (hlt n (Nat.lt_succ_self n)) hZm hZ2 hperp
        (V := gridCharacterMultidim W τ lam n)
        ((measurable_gridCharacterMultidim W hℱi hle' lam).mono (ℱ.le _) le_rfl)
        (Mv := 1) zero_le_one
        (fun ω => le_of_eq (norm_gridCharacterMultidim W τ lam n ω))
        (measurable_gridCharacterMultidim W hℱi hle' lam).stronglyMeasurable (ih hlt') (lam n)
      have hrw : ∀ ω : Ω, Z ω * gridCharacterMultidim W τ lam (n + 1) ω
          = Z ω * gridCharacterMultidim W τ lam n ω
            * Complex.exp (((∑ i, lam n i
                * ((W.W i).W (τ (n + 1)) ω - (W.W i).W (τ n) ω) : ℝ) : ℂ) * Complex.I) := by
        intro ω
        rw [gridCharacterMultidim, gridCharacterMultidim, Finset.prod_range_succ]
        ring
      simpa only [hrw] using hstep
/-- The character of the increments is the character of a single sum. -/
theorem gridCharacterMultidim_eq_exp (W : Multidim.MultidimBrownianMotion P d) (τ : ℕ → ℝ)
    (lam : ℕ → Fin d → ℝ) (n : ℕ) (ω : Ω) :
    gridCharacterMultidim W τ lam n ω
      = Complex.exp (((∑ k ∈ Finset.range n, ∑ i, lam k i
          * ((W.W i).W (τ (k + 1)) ω - (W.W i).W (τ k) ω) : ℝ) : ℂ) * Complex.I) := by
  rw [gridCharacterMultidim, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]
end LevyStochCalc.Brownian.Ito


