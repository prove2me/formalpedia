-- Prove2me | Definitions.Def_SourceProof_592358001a7c02aa8319b535
-- name    : SourceProof_592358001a7c02aa8319b535
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:05:39.938533+00:00
-- url     : https://prove2.me/theorems/5f06ab97-9a4d-4c68-9386-d3e972aa0b56
-- title:
--   StochLean source theorem: StochLean.tendstoUniformlyOn_pathStieltjesIntegral

import Definitions.Def_SourceProof_7fcabca3f7233ab3a9a0e9d6
import Definitions.Def_SourceProof_edcd15c8d7818a605e0602ee

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Uniform continuity of finite-horizon Stieltjes integration

The pathwise operator bound includes the initial value. Local uniform convergence
therefore passes through the integral uniformly in its terminal time.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal Topology

namespace StochLean

variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t} {f g : ℝ≥0 → ℝ} {T t : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_592358001a7c02aa8319b535 {ι : Type*} {l : Filter ι}
    {f : ι → ℝ≥0 → ℝ} {g : ℝ≥0 → ℝ}
    (hf : ∀ i, IntegrableOn (f i) (Ioc 0 T) (totalVariationStieltjes x hx hr).measure)
    (hg : IntegrableOn g (Ioc 0 T) (totalVariationStieltjes x hx hr).measure)
    (hfg : TendstoUniformlyOn f g l (Icc 0 T)) :
    TendstoUniformlyOn (fun i ↦ pathStieltjesIntegral x hx hr (f i))
      (pathStieltjesIntegral x hx hr g) l (Icc 0 T) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let C : ℝ := |x 0| + StochLean.pathTotalVariation x T
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (_root_.Prove2MeSourceProof.h_7fcabca3f7233ab3a9a0e9d6 x T)
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hfg (ε / (C + 1)) hδ] with i hi
  intro t ht
  rw [dist_eq_norm_sub]
  have hb := _root_.Prove2MeSourceProof.h_edcd15c8d7818a605e0602ee hg (hf i) hδ.le
    (fun u hu ↦ (show ‖g u - f i u‖ < ε / (C + 1) from hi u hu).le) ht.2
  apply hb.trans_lt
  change ε / (C + 1) * C < ε
  calc
    _ < ε / (C + 1) * (C + 1) := mul_lt_mul_of_pos_left (by linarith) hδ
    _ = ε := div_mul_cancel₀ _ (by linarith)
end StochLean


