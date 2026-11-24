-- Prove2me | Definitions.Def_SourceProof_0b9fe09b8f4623735111204a
-- name    : SourceProof_0b9fe09b8f4623735111204a
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:01:46.272798+00:00
-- url     : https://prove2.me/theorems/a1ddaf17-37a2-4eb8-a710-1c1a4689c957
-- title:
--   StochLean source theorem: StochLean.integrableOn_variationStieltjes_finite_step

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite-sum formulas for the canonical Stieltjes integral

Intervals are open on the left and closed on the right. Stopping at a finite
horizon caps both endpoints; intervals starting after the horizon contribute zero.
-/

@[expose] public section

open Set MeasureTheory
open scoped NNReal BigOperators

namespace StochLean

variable {x : ℝ≥0 → ℝ} {hx : LocallyBoundedVariationOn x univ}
  {hr : ∀ t, ContinuousWithinAt x (Ici t) t}

theorem _root_.Prove2MeSourceProof.h_0b9fe09b8f4623735111204a {ι : Type*} [Fintype ι]
    (a b : ι → ℝ≥0) (c : ι → ℝ) (c0 : ℝ) (T : ℝ≥0) :
    IntegrableOn
      (fun t ↦ if t = 0 then c0 else ∑ i, (Ioc (a i) (b i)).indicator (fun _ ↦ c i) t)
      (Ioc 0 T) (totalVariationStieltjes x hx hr).measure := by
  classical
  have hi (i : ι) : IntegrableOn ((Ioc (a i) (b i)).indicator (fun _ ↦ c i)) (Ioc 0 T)
      (StochLean.totalVariationStieltjes x hx hr).measure := by
    have hconst : IntegrableOn (fun _ : ℝ≥0 ↦ c i) (Ioc 0 T)
        (StochLean.totalVariationStieltjes x hx hr).measure := integrableOn_const measure_Ioc_lt_top.ne
    exact hconst.indicator measurableSet_Ioc
  apply (integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [if_neg (ne_of_gt ht.1)]
end StochLean


