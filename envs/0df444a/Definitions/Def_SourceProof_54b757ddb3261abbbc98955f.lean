-- Prove2me | Definitions.Def_SourceProof_54b757ddb3261abbbc98955f
-- name    : SourceProof_54b757ddb3261abbbc98955f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:23:36.61836+00:00
-- url     : https://prove2.me/theorems/92a3da24-cf53-4096-a303-51e0b7a91140
-- title:
--   StochLean source theorem: StochLean.tendsto_normSquarePairSum_stopped_cadlag_jump_series

import Definitions.Def_SourceProof_4a1642646798190188bdf9ea
import Definitions.Def_SourceProof_868765551567206b826f381b
import Definitions.Def_SourceProof_8e1107f87943e546fb1d9f6d
import Definitions.Def_SourceProof_ea2a7fd3e5f3c080bfd2c0f2

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

variable {E : Type*} [NormedAddCommGroup E]

theorem _root_.Prove2MeSourceProof.h_54b757ddb3261abbbc98955f [ProperSpace E] {S : ℕ → ℝ≥0}
    (π : ∀ n, TimePartition (S n)) {T : ℝ≥0} {x : ℝ≥0 → E} (hx : IsCadlagPath x)
    {Φ : E → E → ℝ} (hΦ : Continuous (fun p : E × E ↦ Φ p.1 p.2))
    (hdiag : ∀ a, Φ a a = 0)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    (hT : ∀ᶠ n in atTop, T ≤ S n) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᶠ n in atTop, normSquareVariationSum (π n) (fun u ↦ x (min u T)) ≤ B)
    (hsum : Summable (fun s : Ioc 0 T ↦
      Φ (Function.leftLim x s) (x s) * ‖x s - Function.leftLim x s‖ ^ 2)) :
    Tendsto (fun n ↦ normSquarePairSum (π n) Φ x T) atTop
      (𝓝 (∑' s : Ioc 0 T,
        Φ (Function.leftLim x s) (x s) * ‖x s - Function.leftLim x s‖ ^ 2)) := by
  classical
  let ρ : ℕ → StochLean.TimePartition T := fun n ↦
    if h : T ≤ S n then (π n).stop T h else StochLean.TimePartition.single T
  have hm : Tendsto (fun n ↦ ((ρ n).mesh : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n ↦ NNReal.coe_nonneg (ρ n).mesh)) _ hmesh
    filter_upwards [hT] with n hn
    simp only [ρ, dif_pos hn]
    exact_mod_cast (_root_.Prove2MeSourceProof.h_8e1107f87943e546fb1d9f6d (π n)) hn
  have hb' : ∀ᶠ n in atTop, StochLean.normSquareVariationSum (ρ n) x ≤ B := by
    filter_upwards [hT, hb] with n hn hbn
    simpa only [ρ, dif_pos hn, _root_.Prove2MeSourceProof.h_868765551567206b826f381b] using hbn
  apply (_root_.Prove2MeSourceProof.h_ea2a7fd3e5f3c080bfd2c0f2 hx hΦ hdiag hm hB hb' hsum).congr'
  filter_upwards [hT] with n hn
  simp only [ρ, dif_pos hn, _root_.Prove2MeSourceProof.h_4a1642646798190188bdf9ea]
end StochLean


