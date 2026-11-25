-- Prove2me | Definitions.Def_SourceProof_47027b6b170bba7ee3a3145f
-- name    : SourceProof_47027b6b170bba7ee3a3145f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:27.494951+00:00
-- url     : https://prove2.me/theorems/f6a89e6d-0e20-4b5f-8b9c-77605a967b16
-- title:
--   StochLean source theorem: StochLean.pathStieltjesIncrementIntegral_congr_ae

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
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

theorem _root_.Prove2MeSourceProof.h_47027b6b170bba7ee3a3145f
    (hfg : f =ᵐ[(totalVariationStieltjes x hx hr).measure.restrict (Ioc s t)] g) :
    pathStieltjesIncrementIntegral x hx hr f s t =
      pathStieltjesIncrementIntegral x hx hr g s t := by
  have hp := hfg.filter_mono (ae_mono
    (Measure.restrict_mono_measure (_root_.Prove2MeSourceProof.h_4c96a642af2c2b9a1811dd30 x hx hr) _))
  have hn := hfg.filter_mono (ae_mono
    (Measure.restrict_mono_measure (_root_.Prove2MeSourceProof.h_1ef5b6976ba2a56deb7b7a9a x hx hr) _))
  rw [StochLean.pathStieltjesIncrementIntegral, StochLean.pathStieltjesIncrementIntegral,
    integral_congr_ae hp, integral_congr_ae hn]
end StochLean


