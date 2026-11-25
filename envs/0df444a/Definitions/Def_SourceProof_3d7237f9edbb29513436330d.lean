-- Prove2me | Definitions.Def_SourceProof_3d7237f9edbb29513436330d
-- name    : SourceProof_3d7237f9edbb29513436330d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:24:19.3078+00:00
-- url     : https://prove2.me/theorems/a18b1ccf-6d67-4e58-9ea9-8765ba7ce18b
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.condExp_increment_bounds_of_largeJumpResidual

import Definitions.Def_StochLean_Probability_Process_Stopping_LargeJumpResidual_F000
import Definitions.Def_SourceProof_335e23439381136e5a7ba192
import Definitions.Def_SourceProof_6d758566b1ff249a1db9f23e
import Definitions.Def_SourceProof_8a35bc058ee4d5d276653047
import Definitions.Def_SourceProof_99888e5ea4c2153e420fc686
import Definitions.Def_SourceProof_e719b25f8ab4a533f714b2af
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Conditional control by the actual finite large-jump residual

The residual is the existing finite prefix of the actual large-jump
enumeration, with explicitly zero coefficients at infinity. Its actual
fixed-cap dense-window envelope is measurable and square integrable. The
double-width path bridge proves clipped-residual domination, and the
original common path bound proves all coefficient bounds.

Thus the conditional estimate has no supplied residual-domination or jump
coefficient-bound premise. Small-window convergence is not assumed here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

end ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [F.IsRightContinuous]
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

namespace Adapted

theorem _root_.Prove2MeSourceProof.h_3d7237f9edbb29513436330d (hX : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (X · ω)) (hb : 0 < b) (T : ℝ≥0) (K : ℕ)
    {N : ℝ} (hN : 0 ≤ N) (hbound : ∀ᵐ ω ∂P, ∀ t, ‖X t ω‖ ≤ N)
    {t u δ : ℝ≥0} (hδ : 0 < δ) (htu : t ≤ u) (huT : u ≤ T) (huδ : u ≤ t + δ)
    (M : Ω → ℝ) (R : ℕ → Ω → ℝ)
    (hM : M =ᵐ[P]
      P[cappedDenseWindowOscillation (largeJumpResidual X b K) T (2 * δ) (2 * N) | F t])
    (hR : ∀ i ∈ Finset.range K, R i =ᵐ[P]
      P[{ω | (t : WithTop ℝ≥0) < largeJumpSequence X b i ω ∧
          largeJumpSequence X b i ω ≤ ((t + δ : ℝ≥0) : WithTop ℝ≥0)}.indicator
        (fun _ ↦ (1 : ℝ)) | F t]) :
    ∀ᵐ ω ∂P,
      P[(fun v ↦ ‖X t v - X u v‖) | F t] ω ≤
          M ω + 2 * N * ∑ i ∈ Finset.range K, R i ω ∧
        ‖P[X t - X u | F t] ω‖ ≤ M ω + 2 * N * ∑ i ∈ Finset.range K, R i ω ∧
          P[X t - X u | F t] ω ≤ M ω + 2 * N * ∑ i ∈ Finset.range K, R i ω := by
  have hiX (r : ℝ≥0) : Integrable (X r) P := by
    have hp : MemLp (X r) 1 P := MemLp.of_bound
      ((hX r).mono (F.le r) le_rfl).aestronglyMeasurable N (hbound.mono fun _ hω ↦ hω r)
    exact hp.integrable le_rfl
  have hC : 0 ≤ 2 * N := mul_nonneg (by norm_num) hN
  have hiD := ((_root_.Prove2MeSourceProof.h_99888e5ea4c2153e420fc686 (P := P) hX) hc hb T (2 * δ) K hC).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcad : ProbabilityTheory.HasCadlagPaths X P := Eventually.of_forall hc
  have hcoeff := (_root_.Prove2MeSourceProof.h_6d758566b1ff249a1db9f23e hcad) hbound (ProbabilityTheory.largeJumpSequence X b)
  apply _root_.Prove2MeSourceProof.h_8a35bc058ee4d5d276653047 X (Finset.range K)
    (ProbabilityTheory.largeJumpSequence X b)
    (fun i ↦ MeasureTheory.stoppedValueWithTerminal (ProbabilityTheory.jumpProcess X) (fun _ ↦ (0 : ℝ))
      (ProbabilityTheory.largeJumpSequence X b i))
    (ProbabilityTheory.cappedDenseWindowOscillation (ProbabilityTheory.largeJumpResidual X b K) T (2 * δ) (2 * N)) M R
    htu huδ hN (fun i _ ↦ (_root_.Prove2MeSourceProof.h_335e23439381136e5a7ba192 hX) hc hb i)
    (hiX t) (hiX u) hiD _ _ hM hR
  · filter_upwards [hbound, hcoeff] with ω hω hz
    exact ⟨hω t, hω u, fun i _ ↦ hz i⟩
  · apply Eventually.of_forall
    intro ω
    change min (2 * N) ‖ProbabilityTheory.largeJumpResidual X b K u ω - ProbabilityTheory.largeJumpResidual X b K t ω‖ ≤ _
    exact (_root_.Prove2MeSourceProof.h_e719b25f8ab4a533f714b2af (hc ω)) b K (2 * N)
      hδ htu huT huδ
end Adapted

end MeasureTheory


