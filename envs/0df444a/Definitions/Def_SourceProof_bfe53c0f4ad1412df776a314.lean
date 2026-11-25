-- Prove2me | Definitions.Def_SourceProof_bfe53c0f4ad1412df776a314
-- name    : SourceProof_bfe53c0f4ad1412df776a314
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:32:41.63953+00:00
-- url     : https://prove2.me/theorems/c4543b35-df52-5671-a92e-20c635d3f35f
-- title:
--   StochLean source theorem: StochLean.tendsto_quadraticTaylorErrorSum_cadlag

import Definitions.Def_StochLean_Analysis_PathVariation_TaylorSums_F000
import Definitions.Def_SourceProof_02ddc32af3a69faa78af1f8f
import Definitions.Def_SourceProof_03d80293d3aa59b22d10d9aa
import Definitions.Def_SourceProof_1cf1f1d77236c2b817d0e363
import Definitions.Def_SourceProof_62c74d4c6782b2a3e76047aa
import Definitions.Def_SourceProof_ca07ea6fa0932d45a475bf39

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual cadlag Taylor errors converge to the second-order jump correction -/

@[expose] public section

open Set Filter Function ProbabilityTheory
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_bfe53c0f4ad1412df776a314 {S : ℕ → ℝ≥0}
    (π : ∀ n, TimePartition (S n)) {T : ℝ≥0} {x : ℝ≥0 → ℝ} (hx : IsCadlagPath x)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0))
    (hT : ∀ᶠ n in atTop, T ≤ S n) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᶠ n in atTop, quadraticVariationSum (π n) (fun u ↦ x (min u T)) ≤ B)
    (hsq : Summable (fun s : Ioc 0 T ↦ (x s - leftLim x s) ^ 2)) :
    Tendsto (fun n ↦ quadraticTaylorErrorSum (π n) f x T) atTop
      (𝓝 (∑' s : Ioc 0 T,
        (f (x s) - f (leftLim x s) - deriv f (leftLim x s) * (x s - leftLim x s) -
          deriv (deriv f) (leftLim x s) / 2 * (x s - leftLim x s) ^ 2))) := by
  have hd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  let Φ : ℝ → ℝ → ℝ := fun a b ↦ StochLean.quadraticTaylorSlope f a b - deriv (deriv f) a / 2
  have hΦ : Continuous (fun p : ℝ × ℝ ↦ Φ p.1 p.2) :=
    (_root_.Prove2MeSourceProof.h_03d80293d3aa59b22d10d9aa hf).sub
      ((hd.continuous_deriv_one.comp continuous_fst).div_const 2)
  have hs := (_root_.Prove2MeSourceProof.h_ca07ea6fa0932d45a475bf39 hx hsq hΦ).of_abs
  have h := _root_.Prove2MeSourceProof.h_02ddc32af3a69faa78af1f8f π hx hΦ
    (fun a ↦ by simp only [Φ, _root_.Prove2MeSourceProof.h_1cf1f1d77236c2b817d0e363, sub_self]) hmesh hT hB hb hs
  simpa only [StochLean.quadraticTaylorErrorSum, Φ, sub_mul, _root_.Prove2MeSourceProof.h_62c74d4c6782b2a3e76047aa] using h
end StochLean


