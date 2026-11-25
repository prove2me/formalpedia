-- Prove2me | Definitions.Def_SourceProof_2910b8af6805663c425d1b72
-- name    : SourceProof_2910b8af6805663c425d1b72
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:44:57.262305+00:00
-- url     : https://prove2.me/theorems/be949f21-ed0d-417e-9a00-ce1f849c66d4
-- title:
--   StochLean source theorem: StochLean.tendsto_pathStieltjesIncrementIntegral_of_dominated_convergence

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
import Definitions.Def_SourceProof_0e9a3c1ecba0183e8cff41a4
import Definitions.Def_SourceProof_17e97db7cf70e0ac4580327f
import Definitions.Def_SourceProof_1ef5b6976ba2a56deb7b7a9a
import Definitions.Def_SourceProof_4c96a642af2c2b9a1811dd30

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite-horizon integration against a locally BV path

The increment integral on `(s,t]` is the difference of integrals against the
canonical positive and negative Stieltjes components. Integrability is measured
against their sum, the total-variation measure. The source integral from time
zero additionally contains `f 0 * x 0`; this is not a measure atom.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

namespace StochLean

variable (x : ℝ≥0 → ℝ) (hx : LocallyBoundedVariationOn x univ)
  (hr : ∀ t, ContinuousWithinAt x (Ici t) t)

variable {x hx hr} {f g : ℝ≥0 → ℝ} {s t : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_2910b8af6805663c425d1b72
    {f : ℕ → ℝ≥0 → ℝ} {g : ℝ≥0 → ℝ} {bound : ℝ≥0 → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n)
      ((totalVariationStieltjes x hx hr).measure.restrict (Ioc s t)))
    (hb : IntegrableOn bound (Ioc s t) (totalVariationStieltjes x hx hr).measure)
    (hf : ∀ n, ∀ᵐ u ∂(totalVariationStieltjes x hx hr).measure.restrict (Ioc s t),
      ‖f n u‖ ≤ bound u)
    (hlim : ∀ᵐ u ∂(totalVariationStieltjes x hx hr).measure.restrict (Ioc s t),
      Tendsto (fun n ↦ f n u) atTop (𝓝 (g u))) :
    Tendsto (fun n ↦ pathStieltjesIncrementIntegral x hx hr (f n) s t) atTop
      (𝓝 (pathStieltjesIncrementIntegral x hx hr g s t)) := by
  have hp := Measure.restrict_mono_measure (_root_.Prove2MeSourceProof.h_4c96a642af2c2b9a1811dd30 x hx hr) (Ioc s t)
  have hn := Measure.restrict_mono_measure (_root_.Prove2MeSourceProof.h_1ef5b6976ba2a56deb7b7a9a x hx hr) (Ioc s t)
  exact (tendsto_integral_of_dominated_convergence bound (fun n ↦ (hfm n).mono_measure hp)
    (_root_.Prove2MeSourceProof.h_17e97db7cf70e0ac4580327f hb) (fun n ↦ (hf n).filter_mono (ae_mono hp))
    (hlim.filter_mono (ae_mono hp))).sub
      (tendsto_integral_of_dominated_convergence bound (fun n ↦ (hfm n).mono_measure hn)
        (_root_.Prove2MeSourceProof.h_0e9a3c1ecba0183e8cff41a4 hb) (fun n ↦ (hf n).filter_mono (ae_mono hn))
        (hlim.filter_mono (ae_mono hn)))
end StochLean


