-- Prove2me | Definitions.Def_SourceProof_5bee744d40cb242ad8e05050
-- name    : SourceProof_5bee744d40cb242ad8e05050
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:44:47.33641+00:00
-- url     : https://prove2.me/theorems/cc69d15b-0ccd-580d-ad03-02710607ac58
-- title:
--   StochLean source theorem: StochLean.pathStieltjesIncrementIntegral_finsetSum

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegral_F000
import Definitions.Def_SourceProof_0e9a3c1ecba0183e8cff41a4
import Definitions.Def_SourceProof_17e97db7cf70e0ac4580327f

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

theorem _root_.Prove2MeSourceProof.h_5bee744d40cb242ad8e05050 {ι : Type*} (s : Finset ι)
    {f : ι → ℝ≥0 → ℝ} {a b : ℝ≥0}
    (hf : ∀ i ∈ s, IntegrableOn (f i) (Ioc a b) (totalVariationStieltjes x hx hr).measure) :
    pathStieltjesIncrementIntegral x hx hr (fun u ↦ ∑ i ∈ s, f i u) a b =
      ∑ i ∈ s, pathStieltjesIncrementIntegral x hx hr (f i) a b := by
  simp only [StochLean.pathStieltjesIncrementIntegral,
    integral_finsetSum s (fun i hi ↦ _root_.Prove2MeSourceProof.h_17e97db7cf70e0ac4580327f (hf i hi)),
    integral_finsetSum s (fun i hi ↦ _root_.Prove2MeSourceProof.h_0e9a3c1ecba0183e8cff41a4 (hf i hi)),
    Finset.sum_sub_distrib]
end StochLean


