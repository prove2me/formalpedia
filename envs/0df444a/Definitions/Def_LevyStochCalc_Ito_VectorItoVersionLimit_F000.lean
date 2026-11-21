-- Prove2me | Definitions.Def_LevyStochCalc_Ito_VectorItoVersionLimit_F000
-- name    : LevyStochCalc_Ito_VectorItoVersionLimit_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T22:48:23.976503+00:00
-- url     : https://prove2.me/theorems/93527bcb-ba0a-4339-948d-404c2e14c490
-- title:
--   Source declarations: LevyStochCalc.Ito.VectorItoVersionLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.VectorItoVersionLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaUnboundedClamp_F000
import Definitions.Def_SourceProof_015aa1314bb60351ad6e692a
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Continuous versions of vector Itô processes with unbounded coefficients

Clamping the coefficients at a level whose mesh decays geometrically on every bounded window
produces versions whose window suprema of consecutive differences are summable almost surely,
hence converge uniformly on compact time sets; the limit is a continuous adapted version of the
vector Itô process driven by the unclamped coefficients.

## Main statements

* `LevyStochCalc.Brownian.Ito.clampMesh_mono_window` — the clamping mesh grows with the window.
* `LevyStochCalc.Brownian.Ito.exists_seq_clampMesh_window_lt` — clamping levels along which the
  mesh of every window decays geometrically.
* `LevyStochCalc.Brownian.Ito.exists_isVectorItoVersion_of_unbounded` — a continuous adapted
  version of a vector Itô process whose coefficients have finite energy on every window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal Topology

universe u

section Elementary

/-- Powers of `2⁻¹` decrease with the exponent. -/
theorem pow_inv_two_antitone {i j : ℕ} (h : i ≤ j) :
    ((2 : ℝ≥0∞)⁻¹) ^ j ≤ ((2 : ℝ≥0∞)⁻¹) ^ i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  have hk : ((2 : ℝ≥0∞)⁻¹) ^ k ≤ (1 : ℝ≥0∞) ^ k :=
    pow_le_pow_left' (ENNReal.inv_lt_one.mpr (by norm_num)).le k
  rw [one_pow] at hk
  calc ((2 : ℝ≥0∞)⁻¹) ^ i * ((2 : ℝ≥0∞)⁻¹) ^ k
      ≤ ((2 : ℝ≥0∞)⁻¹) ^ i * 1 := mul_le_mul' le_rfl hk
    _ = ((2 : ℝ≥0∞)⁻¹) ^ i := mul_one _
/-- A scaled arithmetic-geometric bound for extended non-negative reals. -/
theorem le_add_inv_mul_sq {ε : ℝ≥0∞} (h0 : ε ≠ 0) (htop : ε ≠ ⊤) (a : ℝ≥0∞) :
    a ≤ ε + ε⁻¹ * a ^ 2 := by
  rcases le_or_gt a ε with h | h
  · calc a ≤ ε := h
      _ = ε + 0 := (add_zero ε).symm
      _ ≤ ε + ε⁻¹ * a ^ 2 := by gcongr; exact zero_le
  · have hmain : a ≤ ε⁻¹ * a ^ 2 := by
      calc a = ε⁻¹ * (ε * a) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel h0 htop, one_mul]
        _ ≤ ε⁻¹ * (a * a) := mul_le_mul' le_rfl (mul_le_mul' h.le le_rfl)
        _ = ε⁻¹ * a ^ 2 := by rw [sq]
    calc a ≤ ε⁻¹ * a ^ 2 := hmain
      _ = 0 + ε⁻¹ * a ^ 2 := (zero_add _).symm
      _ ≤ ε + ε⁻¹ * a ^ 2 := by gcongr; exact zero_le
/-- A tail of a uniformly convergent family converges uniformly. -/
theorem tendstoUniformlyOn_of_shift {β E : Type*} [UniformSpace E] (A : ℕ → β → E)
    {a : β → E} {s : Set β} (m : ℕ)
    (h : TendstoUniformlyOn (fun N => A (N + m)) a Filter.atTop s) :
    TendstoUniformlyOn A a Filter.atTop s := by
  intro u hu
  rw [← Filter.map_add_atTop_eq_nat m, Filter.eventually_map]
  exact h u hu
/-- Adding a fixed function to a uniformly convergent family preserves uniform convergence. -/
theorem tendstoUniformlyOn_of_sub_const {β E : Type*} [NormedAddCommGroup E] (A : ℕ → β → E)
    (c : β → E) {a : β → E} {s : Set β}
    (h : TendstoUniformlyOn (fun N x => A N x - c x) a Filter.atTop s) :
    TendstoUniformlyOn A (fun x => c x + a x) Filter.atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with N hN x hx
  have heq : c x + a x - A N x = a x - (A N x - c x) := by abel
  rw [dist_eq_norm, heq, ← dist_eq_norm]
  exact hN x hx
end Elementary

section Mesh

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-- The clamping mesh grows with the window. -/
theorem clampMesh_mono_window (P : Measure Ω) (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (b : Fin n → Ω → ℝ → ℝ) {T T' : ℝ} (hTT' : T ≤ T') (j : ℕ) :
    clampMesh P H b T j ≤ clampMesh P H b T' j := by
  unfold clampMesh
  refine Finset.sum_le_sum fun p _ => ?_
  have hmonoD : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖clampDrift b j p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖clampDrift b j p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    MeasureTheory.lintegral_mono fun ω =>
      MeasureTheory.lintegral_mono_set (Set.Icc_subset_Icc_right hTT')
  have hmonoH : ∀ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    fun k => MeasureTheory.lintegral_mono fun ω =>
      MeasureTheory.lintegral_mono_set (Set.Icc_subset_Icc_right hTT')
  have hT : ENNReal.ofReal T ≤ ENNReal.ofReal T' := ENNReal.ofReal_le_ofReal hTT'
  gcongr
/-- On a probability space an integral is controlled by `ε` plus a scaled bound on the integral
of the square. -/
theorem lintegral_le_add_inv_mul_of_sq_le (f : Ω → ℝ≥0∞) {ε C : ℝ≥0∞}
    (h0 : ε ≠ 0) (htop : ε ≠ ⊤) (hsq : ∫⁻ ω, f ω ^ 2 ∂P ≤ C) :
    ∫⁻ ω, f ω ∂P ≤ ε + ε⁻¹ * C := by
  calc ∫⁻ ω, f ω ∂P ≤ ∫⁻ ω, (ε + ε⁻¹ * f ω ^ 2) ∂P :=
        MeasureTheory.lintegral_mono fun ω => le_add_inv_mul_sq h0 htop (f ω)
    _ = ε + ε⁻¹ * ∫⁻ ω, f ω ^ 2 ∂P := by
        rw [MeasureTheory.lintegral_add_left measurable_const,
          MeasureTheory.lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr h0),
          MeasureTheory.lintegral_const, measure_univ, mul_one]
    _ ≤ ε + ε⁻¹ * C := by gcongr
/-- **Clamping levels along which the mesh of every bounded window decays geometrically.** -/
theorem exists_seq_clampMesh_window_lt {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hq : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hbq : ∀ (p : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧
      ∀ i : ℕ, clampMesh P H b ((i : ℝ) + 1) (ms i) < ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) := by
  classical
  have hchoice : ∀ i : ℕ, ∃ j : ℕ,
      i ≤ j ∧ clampMesh P H b ((i : ℝ) + 1) j < ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) := by
    intro i
    have hTpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have htend := _root_.Prove2MeSourceProof.h_015aa1314bb60351ad6e692a (P := P) hm hbm
      (fun p k => (hq p k _ hTpos).ne) (fun p => (hbq p _ hTpos).ne)
    have hpos : (0 : ℝ≥0∞) < ((2 : ℝ≥0∞)⁻¹) ^ (2 * i) := by
      refine pos_iff_ne_zero.mpr (pow_ne_zero _ ?_)
      simp
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds hpos))
    exact ⟨max N i, le_max_right N i, hN (max N i) (le_max_left N i)⟩
  choose ms hge hms using hchoice
  exact ⟨ms, hge, hms⟩
end Mesh

section Limit

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-- A vector Itô process starts at its initial value. -/
theorem vectorItoProcess_ae_eq_zero (W : Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
    (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (X₀ : Ω → Fin n → ℝ) (b : Fin n → Ω → ℝ → ℝ) :
    vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ b 0 =ᵐ[P] X₀ := by
  have hall : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
      stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
        (hHs p k) 0 ω = 0 := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 (W.W k) ℱ (hcoord k) (H p k)
      (hHm p k) (hHp p k) (hHs p k) le_rfl
  filter_upwards [hall] with ω hz
  funext p
  have hdrift : ∫ s in Set.Icc (0 : ℝ) 0, b p ω s ∂volume = 0 := by
    rw [show Set.Icc (0 : ℝ) 0 = {(0 : ℝ)} from Set.Icc_self 0,
      MeasureTheory.setIntegral_measure_zero _ Real.volume_singleton]
  simp only [vectorItoProcess, vectorItoMartingale, coordItoIntegral, hdrift]
  have hsum : ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k)
      (hHm p k) (hHp p k) (hHs p k) 0 ω = 0 := Finset.sum_eq_zero fun k _ => hz p k
  rw [hsum]
  ring
end Limit

end LevyStochCalc.Brownian.Ito


