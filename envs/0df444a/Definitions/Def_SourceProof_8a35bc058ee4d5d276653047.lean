-- Prove2me | Definitions.Def_SourceProof_8a35bc058ee4d5d276653047
-- name    : SourceProof_8a35bc058ee4d5d276653047
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:51:14.800015+00:00
-- url     : https://prove2.me/theorems/fbbe896b-1915-4625-969b-4b250af509a6
-- title:
--   StochLean source theorem: MeasureTheory.condExp_increment_bounds_of_finite_jump_removal

import Definitions.Def_SourceProof_ec9bc2113b2e672c1b3d4335
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Conditional estimates after finitely many jumps are removed

The actual pathwise clipped-residual inequality is proved before conditional
expectation is taken. An integrable envelope for that clipped residual and
conditional probabilities for finitely many stopping windows then control
the conditional increment. There is no interchange of `min` and conditional
expectation, and no moment assumption on a random total number of jumps.

The envelope and conditional-probability representatives are inputs to this
building block. No small-window convergence or Doob--Meyer decomposition is
asserted here.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ}


theorem _root_.Prove2MeSourceProof.h_8a35bc058ee4d5d276653047
    (X : ℝ≥0 → Ω → ℝ) (s : Finset ι) (τ : ι → Ω → WithTop ℝ≥0)
    (Z : ι → Ω → ℝ) (D M : Ω → ℝ) (R : ι → Ω → ℝ)
    {t u δ : ℝ≥0} (htu : t ≤ u) (huδ : u ≤ t + δ) {N : ℝ} (hN : 0 ≤ N)
    (hτ : ∀ i ∈ s, IsStoppingTime F (τ i))
    (hit : Integrable (X t) P) (hiu : Integrable (X u) P) (hiD : Integrable D P)
    (hb : ∀ᵐ ω ∂P, ‖X t ω‖ ≤ N ∧ ‖X u ω‖ ≤ N ∧
      ∀ i ∈ s, ‖Z i ω‖ ≤ 2 * N)
    (hD : ∀ᵐ ω ∂P,
      min (2 * N) ‖(X u ω - ∑ i ∈ s,
          {v | τ i v ≤ (u : WithTop ℝ≥0)}.indicator (Z i) ω) -
        (X t ω - ∑ i ∈ s, {v | τ i v ≤ (t : WithTop ℝ≥0)}.indicator (Z i) ω)‖ ≤ D ω)
    (hM : M =ᵐ[P] P[D | F t])
    (hR : ∀ i ∈ s, R i =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < τ i ω ∧
          τ i ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ)) | F t]) :
    ∀ᵐ ω ∂P,
      P[(fun v ↦ ‖X t v - X u v‖) | F t] ω ≤ M ω + 2 * N * ∑ i ∈ s, R i ω ∧
        ‖P[X t - X u | F t] ω‖ ≤ M ω + 2 * N * ∑ i ∈ s, R i ω ∧
          P[X t - X u | F t] ω ≤ M ω + 2 * N * ∑ i ∈ s, R i ω := by
  classical
  let W : ι → Ω → ℝ := fun i ↦
    {ω | (t : WithTop ℝ≥0) < τ i ω ∧
      τ i ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator (fun _ ↦ (1 : ℝ))
  let S : Ω → ℝ := ∑ i ∈ s, W i
  let B : Ω → ℝ := D + (2 * N) • S
  have hiW : ∀ i ∈ s, Integrable (W i) P := by
    intro i hi
    apply (integrable_const (1 : ℝ)).indicator
    exact (F.le t _ ((hτ i hi).measurableSet_gt t)).inter
      (F.le (t + δ) _ (hτ i hi (t + δ)))
  have hiS : Integrable S P := integrable_finsetSum' s hiW
  have hiB : Integrable B P := hiD.add (hiS.smul (2 * N))
  have hpath : (fun ω ↦ ‖X t ω - X u ω‖) ≤ᵐ[P] B := by
    filter_upwards [hb, hD] with ω hω hDω
    have hwindow : (∑ i ∈ s,
        {v | (t : WithTop ℝ≥0) < τ i v ∧ τ i v ≤ (u : WithTop ℝ≥0)}.indicator
          (fun _ ↦ (1 : ℝ)) ω) ≤ ∑ i ∈ s, W i ω := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hw : (t : WithTop ℝ≥0) < τ i ω ∧ τ i ω ≤ (u : WithTop ℝ≥0)
      · have hwδ : (t : WithTop ℝ≥0) < τ i ω ∧
            τ i ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0) :=
          ⟨hw.1, hw.2.trans (WithTop.coe_le_coe.mpr huδ)⟩
        simp only [W, indicator_apply, mem_ofPred_eq, hw, hwδ, le_refl]
      · rw [indicator_of_notMem (s := {v | (t : WithTop ℝ≥0) < τ i v ∧
          τ i v ≤ (u : WithTop ℝ≥0)}) hw]
        exact indicator_nonneg (fun _ _ ↦ zero_le_one) ω
    have h := _root_.Prove2MeSourceProof.h_ec9bc2113b2e672c1b3d4335 X s τ Z htu ω
      hω.1 hω.2.1 hω.2.2
    have h' := h.trans (add_le_add hDω
      (mul_le_mul_of_nonneg_left hwindow (mul_nonneg (by norm_num) hN)))
    simpa only [B, S, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      norm_sub_rev] using h'
  have hce := condExp_mono (m := F t) (hit.sub hiu).norm hiB hpath
  have hadd := condExp_add hiD (hiS.smul (2 * N)) (F t)
  have hsmul := condExp_smul (2 * N) S (F t) (μ := P)
  have hsum := condExp_finsetSum hiW (F t)
  have hRall : ∀ᵐ ω ∂P, ∀ i ∈ s, R i ω = P[W i | F t] ω :=
    s.eventually_all.mpr hR
  have hnorm := norm_condExp_le (μ := P) (m := F t) (X t - X u)
  filter_upwards [hce, hadd, hsmul, hsum, hM, hRall, hnorm]
    with ω hceω haddω hsmulω hsumω hMω hRω hnormω
  have hsumR : P[S | F t] ω = ∑ i ∈ s, R i ω := by
    change P[S | F t] ω = (∑ i ∈ s, P[W i | F t]) ω at hsumω
    rw [hsumω, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun i hi ↦ (hRω i hi).symm)
  have hB : P[B | F t] ω = M ω + 2 * N * ∑ i ∈ s, R i ω := by
    change P[B | F t] ω = P[D | F t] ω + P[(2 * N) • S | F t] ω at haddω
    change P[(2 * N) • S | F t] ω = 2 * N * P[S | F t] ω at hsmulω
    rw [haddω, hsmulω, hsumR, ← hMω]
  have habs := hceω.trans_eq hB
  have hnormBound : ‖P[X t - X u | F t] ω‖ ≤ M ω + 2 * N * ∑ i ∈ s, R i ω :=
    hnormω.trans habs
  have hle : P[X t - X u | F t] ω ≤ ‖P[X t - X u | F t] ω‖ := by
    simpa only [Real.norm_eq_abs] using le_abs_self (P[X t - X u | F t] ω)
  exact ⟨habs, hnormBound, hle.trans hnormBound⟩
end MeasureTheory


