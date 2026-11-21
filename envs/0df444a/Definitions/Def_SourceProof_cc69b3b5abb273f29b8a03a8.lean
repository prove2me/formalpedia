-- Prove2me | Definitions.Def_SourceProof_cc69b3b5abb273f29b8a03a8
-- name    : SourceProof_cc69b3b5abb273f29b8a03a8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:42:28.7067+00:00
-- url     : https://prove2.me/theorems/002b7b03-f826-458c-bb1b-962b29c5ce6f
-- title:
--   LevyStochCalc source module: SourceProof_cc69b3b5abb273f29b8a03a8
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_frozenRiemann_sub_le` comes from the `LevyStochCalc.Brownian.VectorItoTimeRiemann` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoTimeRiemann_F000
import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000
import Definitions.Def_SourceProof_d7cba35146767f24248848dd

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Frozen-weight Riemann sums for a vector Itô process

Freezing a Lipschitz function of a continuous vector Itô process at the left endpoints of a
uniform grid and pairing it with the cell integrals of a bounded time density gives a Riemann sum
for `∫_0^T φ(X_s)·w_s ds`, with an `L¹` error of order `√(T/m)`. Both the process's own drift
coordinates and the entries of the diffusion matrix are admissible densities.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_frozenRiemann_sub_le` — the `L¹`
  error of a frozen-weight Riemann sum along a vector Itô process.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section VectorRiemann

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_cc69b3b5abb273f29b8a03a8
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)
    (wgt : Ω → ℝ → ℝ) (hwm : Measurable (Function.uncurry wgt))
    {A : ℝ} (hA0 : 0 ≤ A) (hA : ∀ (ω : Ω) (s : ℝ), |wgt ω s| ≤ A)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hφbd : ∀ x, |φ x| ≤ Kφ)
    {Mφ L : ℝ} (hMφ0 : 0 ≤ Mφ) (hL0 : 0 ≤ L)
    (hφaff : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ Mφ + L * ‖x - y‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω =>
        (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume) P
      ∧ ∫ ω, |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume| ∂P
        ≤ Mφ * A * T + L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
          + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))) := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hKφ0 : 0 ≤ Kφ := le_trans (abs_nonneg _) (hφbd 0)
  have hLA0 : (0 : ℝ) ≤ L * A := mul_nonneg hL0 hA0
  have hcellT : ∀ i : ℕ, volume (Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) ≠ ⊤ :=
    fun i => (measure_Ioc_lt_top).ne
  have hXmeas : ∀ ω : Ω, Measurable fun s => X s ω := fun ω => (h.continuous_path ω).measurable
  have hwmeas : ∀ ω : Ω, Measurable (wgt ω) := fun ω => Measurable.of_uncurry_left hwm
  have hgmeas : ∀ ω : Ω, Measurable fun s => φ (X s ω) * wgt ω s := fun ω =>
    (hφc.measurable.comp (hXmeas ω)).mul (hwmeas ω)
  have hgbd : ∀ (ω : Ω) (s : ℝ), |φ (X s ω) * wgt ω s| ≤ Kφ * A := by
    intro ω s
    rw [abs_mul]
    exact mul_le_mul (hφbd _) (hA ω s) (abs_nonneg _) hKφ0
  have hcellb : ∀ (ω : Ω) (i : ℕ), IntegrableOn (wgt ω)
      (Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) volume := fun ω i =>
    LevyStochCalc.integrableOn_of_bounded_of_measurable (hwmeas ω) (hA ω) (hcellT i)
  have hcellg : ∀ (ω : Ω) (i : ℕ),
      IntegrableOn (fun s => φ (X s ω) * wgt ω s)
        (Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) volume := fun ω i =>
    LevyStochCalc.integrableOn_of_bounded_of_measurable (hgmeas ω) (hgbd ω) (hcellT i)
  have hcelld : ∀ (ω : Ω) (i : ℕ),
      IntegrableOn (fun s => (φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) - φ (X s ω)) * wgt ω s)
        (Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) volume := by
    intro ω i
    refine LevyStochCalc.integrableOn_of_bounded_of_measurable (B := (Kφ + Kφ) * A)
      (f := fun s => (φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) - φ (X s ω)) * wgt ω s)
      (((measurable_const).sub (hφc.measurable.comp (hXmeas ω))).mul (hwmeas ω))
      (fun s => ?_) (hcellT i)
    rw [abs_mul]
    exact mul_le_mul ((LevyStochCalc.Brownian.Ito.abs_sub_le_abs_add_abs _ _).trans (add_le_add (hφbd _) (hφbd _)))
      (hA ω s) (abs_nonneg _) (by linarith)
  have hcellL : ∀ (ω : Ω) (i : ℕ),
      IntegrableOn (fun s => L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖)
        (Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) volume := by
    intro ω i
    refine MeasureTheory.IntegrableOn.mono_set ?_ Set.Ioc_subset_Icc_self
    exact Continuous.integrableOn_Icc
      (continuous_const.mul ((continuous_const.sub (h.continuous_path ω)).norm))
  have hcellC : ∀ i : ℕ, IntegrableOn (fun _ : ℝ => Mφ * A)
      (Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) volume := by
    intro i
    refine MeasureTheory.IntegrableOn.mono_set ?_ Set.Ioc_subset_Icc_self
    exact Continuous.integrableOn_Icc continuous_const
  have hcellLM : ∀ (ω : Ω) (i : ℕ),
      IntegrableOn (fun s => Mφ * A + L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖)
        (Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1))) volume := fun ω i =>
    (hcellC i).add (hcellL ω i)
  have hpart : ∀ ω : Ω,
      ∑ i ∈ Finset.range m, ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
          φ (X s ω) * wgt ω s ∂volume
        = ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume := fun ω =>
    LevyStochCalc.Brownian.Ito.sum_setIntegral_unifGrid hT hm0 (hgmeas ω) (hgbd ω)
  have hcell : ∀ (ω : Ω) (i : ℕ),
      φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
        - ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), φ (X s ω) * wgt ω s ∂volume
      = ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
          (φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) - φ (X s ω)) * wgt ω s ∂volume := by
    intro ω i
    rw [← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_sub ((hcellb ω i).const_mul _) (hcellg ω i)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    ring
  have hcellvol : ∀ i : ℕ,
      (volume : Measure ℝ).real (Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)))
        = T / (m : ℝ) := by
    intro i
    rw [Real.volume_real_Ioc_of_le (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i).le, LevyStochCalc.Brownian.Ito.unifGrid_succ_sub hm0 i]
  have hcellle : ∀ (ω : Ω) (i : ℕ),
      |∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
          (φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) - φ (X s ω)) * wgt ω s ∂volume|
      ≤ Mφ * A * (T / (m : ℝ))
        + ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
            L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume := by
    intro ω i
    refine (MeasureTheory.abs_integral_le_integral_abs).trans ?_
    have hstep : ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
        |(φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) - φ (X s ω)) * wgt ω s| ∂volume
        ≤ ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
            (Mφ * A + L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖) ∂volume := by
      refine MeasureTheory.integral_mono (hcelld ω i).abs (hcellLM ω i) fun s => ?_
      rw [abs_mul]
      calc |φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) - φ (X s ω)| * |wgt ω s|
          ≤ (Mφ + L * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖) * A :=
            mul_le_mul (hφaff _ _) (hA ω s) (abs_nonneg _)
              (by positivity)
        _ = Mφ * A + L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ := by ring
    refine hstep.trans (le_of_eq ?_)
    rw [MeasureTheory.integral_add (hcellC i) (hcellL ω i),
      MeasureTheory.setIntegral_const, hcellvol i, smul_eq_mul]
    ring
  have hZ : ∀ ω : Ω,
      |(∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume|
      ≤ Mφ * A * T
        + ∑ i ∈ Finset.range m, ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
            L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume := by
    intro ω
    rw [← hpart ω, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hsum : ∑ i ∈ Finset.range m,
        |φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
            - ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                φ (X s ω) * wgt ω s ∂volume|
        ≤ ∑ i ∈ Finset.range m, (Mφ * A * (T / (m : ℝ))
            + ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hcell ω i]
      exact hcellle ω i
    refine hsum.trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hTm : (m : ℝ) * (T / (m : ℝ)) = T := by field_simp
    have : (m : ℝ) * (Mφ * A * (T / (m : ℝ))) = Mφ * A * ((m : ℝ) * (T / (m : ℝ))) := by ring
    rw [this, hTm]
  have hjointg : Measurable (Function.uncurry fun ω s => φ (X s ω) * wgt ω s) :=
    (h.measurable_uncurry_comp hφc.measurable).mul hwm
  have hZmeas : Measurable fun ω : Ω =>
      (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume := by
    refine Measurable.sub ?_ (LevyStochCalc.measurable_setIntegral hjointg _)
    exact Finset.measurable_sum _ fun i _ =>
      (hφc.measurable.comp (h.measurable (LevyStochCalc.Brownian.Ito.unifGrid T m i))).mul
        (LevyStochCalc.measurable_setIntegral_Ioc hwm _ _)
  have hZbd : ∀ ω : Ω,
      |(∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume|
      ≤ 2 * (Kφ * A * T) := by
    intro ω
    have h1 : |∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume|
        ≤ Kφ * A * T := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hterm : ∀ i ∈ Finset.range m, |φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume|
          ≤ Kφ * (A * (T / (m : ℝ))) := by
        intro i _
        rw [abs_mul]
        refine mul_le_mul (hφbd _) ?_ (abs_nonneg _) hKφ0
        have := _root_.Prove2MeSourceProof.h_0c7e85b4037c170c4bb0381a (Measurable.of_uncurry_left hwm) (hA ω)
          (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i).le
        rwa [LevyStochCalc.Brownian.Ito.unifGrid_succ_sub hm0 i] at this
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hTm : (m : ℝ) * (T / (m : ℝ)) = T := by field_simp
      calc (m : ℝ) * (Kφ * (A * (T / (m : ℝ))))
          = Kφ * A * ((m : ℝ) * (T / (m : ℝ))) := by ring
        _ = Kφ * A * T := by rw [hTm]
        _ ≤ Kφ * A * T := le_rfl
    have h2 : |∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume| ≤ Kφ * A * T := by
      have := _root_.Prove2MeSourceProof.h_0c7e85b4037c170c4bb0381a (hgmeas ω) (hgbd ω) hT.le
      simpa using this
    calc |(∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume|
        ≤ |∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume|
          + |∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume| :=
          LevyStochCalc.Brownian.Ito.abs_sub_le_abs_add_abs _ _
      _ ≤ 2 * (Kφ * A * T) := by linarith
  have hZint : Integrable (fun ω : Ω =>
      (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume) P := by
    refine (MeasureTheory.integrable_const (2 * (Kφ * A * T))).mono
      hZmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (le_trans (abs_nonneg _) (hZbd ω))]
    exact hZbd ω
  have hRHS0 : (0 : ℝ) ≤ Mφ * A * T + L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
      + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))) := by
    have hT0 : (0 : ℝ) ≤ T := hT.le
    positivity
  refine ⟨hZint, LevyStochCalc.Brownian.Ito.integral_le_of_lintegral_ofReal_le hZint.abs (fun ω => abs_nonneg _)
    hRHS0 ?_⟩
  have hwin : ∀ i : ℕ, ∫⁻ ω, ∫⁻ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
        ENNReal.ofReal ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume ∂P
      ≤ ENNReal.ofReal ((T / (m : ℝ)) * ((n : ℝ) * (B * (T / (m : ℝ))
          + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))) := by
    intro i
    have hsym : ∀ (ω : Ω) (s : ℝ), ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖
        = ‖X s ω - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω‖ := fun ω s => norm_sub_rev _ _
    simp_rw [hsym]
    have := (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_d7cba35146767f24248848dd p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB0 hB
      (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i) (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i).le
    rwa [LevyStochCalc.Brownian.Ito.unifGrid_succ_sub hm0 i] at this
  have hmeasCell : ∀ i : ℕ, Measurable fun ω : Ω =>
      ENNReal.ofReal (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
        L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume) := by
    intro i
    refine ENNReal.measurable_ofReal.comp (LevyStochCalc.measurable_setIntegral ?_ _)
    exact measurable_const.mul
      ((((h.measurable (LevyStochCalc.Brownian.Ito.unifGrid T m i)).comp measurable_fst).sub h.measurable_uncurry).norm)
  have hYle : ∫⁻ ω, ∑ i ∈ Finset.range m, ENNReal.ofReal
        (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
          L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume) ∂P
      ≤ ENNReal.ofReal (L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
        + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))) := by
    calc ∫⁻ ω, ∑ i ∈ Finset.range m, ENNReal.ofReal
            (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
            L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume) ∂P
        = ∑ i ∈ Finset.range m, ∫⁻ ω, ENNReal.ofReal
            (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
              L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume) ∂P :=
        MeasureTheory.lintegral_finsetSum _ fun i _ => hmeasCell i
    _ = ∑ i ∈ Finset.range m, ENNReal.ofReal (L * A)
          * ∫⁻ ω, ∫⁻ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
              ENNReal.ofReal ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume ∂P := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (L * A) ≠ ⊤)]
        refine lintegral_congr fun ω => ?_
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hcellL ω i)
          (Filter.Eventually.of_forall fun s => by positivity),
          ← MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (L * A) ≠ ⊤)]
        refine lintegral_congr fun s => ?_
        rw [← ENNReal.ofReal_mul hLA0]
    _ ≤ ∑ i ∈ Finset.range m, ENNReal.ofReal (L * A)
          * ENNReal.ofReal ((T / (m : ℝ)) * ((n : ℝ) * (B * (T / (m : ℝ))
            + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))) :=
        Finset.sum_le_sum fun i _ => by gcongr; exact hwin i
    _ = ENNReal.ofReal (L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
          + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))) := by
        have hwnn : (0 : ℝ) ≤ (T / (m : ℝ)) * ((n : ℝ) * (B * (T / (m : ℝ))
            + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))) := by positivity
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← ENNReal.ofReal_mul hLA0]
        rw [show ((m : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((m : ℝ)) from
          (ENNReal.ofReal_natCast m).symm, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
        congr 1
        field_simp
  have hMAT0 : (0 : ℝ) ≤ Mφ * A * T := by positivity
  have hLAT0 : (0 : ℝ) ≤ L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
      + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))) := by
    have hT0 : (0 : ℝ) ≤ T := hT.le
    positivity
  calc ∫⁻ ω, ENNReal.ofReal
        |(∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), wgt ω s ∂volume)
            - ∫ s in Set.Ioc (0 : ℝ) T, φ (X s ω) * wgt ω s ∂volume| ∂P
      ≤ ∫⁻ _ω : Ω, ENNReal.ofReal (Mφ * A * T) ∂P
        + ∫⁻ ω, ∑ i ∈ Finset.range m, ENNReal.ofReal
            (∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
              L * A * ‖X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω - X s ω‖ ∂volume) ∂P := by
        rw [← MeasureTheory.lintegral_add_left measurable_const]
        refine lintegral_mono fun ω => ?_
        refine (ENNReal.ofReal_le_ofReal (hZ ω)).trans ?_
        rw [ENNReal.ofReal_add hMAT0 (Finset.sum_nonneg fun i _ =>
          MeasureTheory.integral_nonneg fun s => by positivity)]
        gcongr
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _
        exact MeasureTheory.integral_nonneg fun s => by positivity
    _ ≤ ENNReal.ofReal (Mφ * A * T)
        + ENNReal.ofReal (L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
          + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))) := by
        rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
        exact add_le_add le_rfl hYle
    _ = ENNReal.ofReal (Mφ * A * T + L * A * (T * ((n : ℝ) * (B * (T / (m : ℝ))
          + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))) := (ENNReal.ofReal_add hMAT0 hLAT0).symm
end VectorRiemann

end LevyStochCalc.Brownian.Ito


