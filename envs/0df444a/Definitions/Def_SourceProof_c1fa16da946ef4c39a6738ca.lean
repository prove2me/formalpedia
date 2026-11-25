-- Prove2me | Definitions.Def_SourceProof_c1fa16da946ef4c39a6738ca
-- name    : SourceProof_c1fa16da946ef4c39a6738ca
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:06.935794+00:00
-- url     : https://prove2.me/theorems/2c1038fa-6d65-4a97-8725-b227c233e89d
-- title:
--   StochLean source theorem: StochLean.pathStieltjesIntegral_finite_step

import Definitions.Def_SourceProof_47027b6b170bba7ee3a3145f
import Definitions.Def_SourceProof_5bee744d40cb242ad8e05050
import Definitions.Def_SourceProof_de50296af2881fca8cc599af

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

theorem _root_.Prove2MeSourceProof.h_c1fa16da946ef4c39a6738ca {ι : Type*} [Fintype ι]
    (a b : ι → ℝ≥0) (c : ι → ℝ) (hab : ∀ i, a i ≤ b i) (c0 : ℝ) (T : ℝ≥0) :
    pathStieltjesIntegral x hx hr
      (fun t ↦ if t = 0 then c0 else ∑ i, (Ioc (a i) (b i)).indicator (fun _ ↦ c i) t) T =
      c0 * x 0 + ∑ i, c i * (x (min (b i) T) - x (min (a i) T)) := by
  classical
  have hi (i : ι) : IntegrableOn ((Ioc (a i) (b i)).indicator (fun _ ↦ c i)) (Ioc 0 T)
      (StochLean.totalVariationStieltjes x hx hr).measure := by
    have hconst : IntegrableOn (fun _ : ℝ≥0 ↦ c i) (Ioc 0 T)
        (StochLean.totalVariationStieltjes x hx hr).measure := integrableOn_const measure_Ioc_lt_top.ne
    exact hconst.indicator measurableSet_Ioc
  have hcongr : StochLean.pathStieltjesIncrementIntegral x hx hr
      (fun t ↦ if t = 0 then c0 else ∑ i, (Ioc (a i) (b i)).indicator (fun _ ↦ c i) t) 0 T =
      StochLean.pathStieltjesIncrementIntegral x hx hr
        (fun t ↦ ∑ i, (Ioc (a i) (b i)).indicator (fun _ ↦ c i) t) 0 T := by
    apply _root_.Prove2MeSourceProof.h_47027b6b170bba7ee3a3145f
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [if_neg (ne_of_gt ht.1)]
  simp only [StochLean.pathStieltjesIntegral, ↓reduceIte, hcongr,
    _root_.Prove2MeSourceProof.h_5bee744d40cb242ad8e05050 Finset.univ (fun i _ ↦ hi i),
    _root_.Prove2MeSourceProof.h_de50296af2881fca8cc599af (hab _)]
end StochLean


