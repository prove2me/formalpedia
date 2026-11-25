-- Prove2me | Definitions.Def_SourceProof_02ddc32af3a69faa78af1f8f
-- name    : SourceProof_02ddc32af3a69faa78af1f8f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:21:50.655719+00:00
-- url     : https://prove2.me/theorems/d170238c-3c67-5eb3-b31f-fb8139fa514e
-- title:
--   StochLean source theorem: StochLean.tendsto_quadraticPairSum_stopped_cadlag_jump_series

import Definitions.Def_SourceProof_442732a15c788dd8b43d508a
import Definitions.Def_SourceProof_8e1107f87943e546fb1d9f6d
import Definitions.Def_SourceProof_adea31b71d0c282b78b657e6
import Definitions.Def_SourceProof_ba24b60c318b33c18cd33a68

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Jump-series convergence for partial quadratic-pair sums

Partition horizons may vary and only need eventually cover the fixed
evaluation time. Clipping retains repeated endpoints and the last partial
cell; no additional mesh rate or refinement assumption is introduced.
-/

@[expose] public section

open Set Finset Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_02ddc32af3a69faa78af1f8f {S : ℕ → ℝ≥0}
    (π : ∀ n, TimePartition (S n)) {T : ℝ≥0} {x : ℝ≥0 → ℝ} (hx : IsCadlagPath x)
    {Φ : ℝ → ℝ → ℝ} (hΦ : Continuous (fun p : ℝ × ℝ ↦ Φ p.1 p.2))
    (hdiag : ∀ a, Φ a a = 0)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    (hT : ∀ᶠ n in atTop, T ≤ S n) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᶠ n in atTop, quadraticVariationSum (π n) (fun u ↦ x (min u T)) ≤ B)
    (hsum : Summable (fun s : Ioc 0 T ↦
      Φ (Function.leftLim x s) (x s) * (x s - Function.leftLim x s) ^ 2)) :
    Tendsto (fun n ↦ quadraticPairSum (π n) Φ x T) atTop
      (𝓝 (∑' s : Ioc 0 T,
        Φ (Function.leftLim x s) (x s) * (x s - Function.leftLim x s) ^ 2)) := by
  classical
  let ρ : ℕ → StochLean.TimePartition T := fun n ↦
    if h : T ≤ S n then (π n).stop T h else StochLean.TimePartition.single T
  have hm : Tendsto (fun n ↦ ((ρ n).mesh : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n ↦ NNReal.coe_nonneg (ρ n).mesh)) _ hmesh
    filter_upwards [hT] with n hn
    simp only [ρ, dif_pos hn]
    exact_mod_cast (_root_.Prove2MeSourceProof.h_8e1107f87943e546fb1d9f6d (π n)) hn
  have hb' : ∀ᶠ n in atTop, StochLean.quadraticVariationSum (ρ n) x ≤ B := by
    filter_upwards [hT, hb] with n hn hbn
    simpa only [ρ, dif_pos hn, _root_.Prove2MeSourceProof.h_ba24b60c318b33c18cd33a68] using hbn
  apply (_root_.Prove2MeSourceProof.h_adea31b71d0c282b78b657e6 hx hΦ hdiag hm hB hb' hsum).congr'
  filter_upwards [hT] with n hn
  simp only [ρ, dif_pos hn, _root_.Prove2MeSourceProof.h_442732a15c788dd8b43d508a]
end StochLean


