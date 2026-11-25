-- Prove2me | Definitions.Def_SourceProof_9dc5f658b159b2384b1b34af
-- name    : SourceProof_9dc5f658b159b2384b1b34af
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:16:38.407766+00:00
-- url     : https://prove2.me/theorems/d3528355-eb07-53d2-a7d6-1e6dce340c89
-- title:
--   StochLean source theorem: StochLean.measurable_tprod_exponentialJumpFactor_of_kernel_atoms

import Definitions.Def_SourceProof_3f982b6cb5bd7b54e3186947
import Definitions.Def_SourceProof_61bad4bf4babd22e06805bca
import Definitions.Def_SourceProof_6a697584c8707d1dd1f231ef
import Definitions.Def_SourceProof_6a699b84e118f7439b9a72bc
import Definitions.Def_SourceProof_911b993558830136570eb23c
import Definitions.Def_SourceProof_c4ca568f1e2168c1b07e73bd
import Definitions.Def_SourceProof_f34c8af209232225589c0804

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurability of the actual jump product on random atom sets

The nonzero jump locations are supported by a measurable finite-fiber
kernel. Square summability supplies both the zero count and the complex
logarithm series. The guarded formula preserves zero and negative factors;
it proves measurability of the original product, not of a substitute.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_9dc5f658b159b2384b1b34af
    {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℝ≥0)
    (hκ : ∀ ω, IsFiniteMeasure (κ ω)) {u : Ω → ℝ≥0 → ℝ}
    (hu : Measurable (uncurry u)) (hs : ∀ ω, Summable (fun t ↦ u ω t ^ 2))
    (hzero : ∀ ω t, κ ω {t} = 0 → u ω t = 0) :
    Measurable fun ω ↦ ∏' t, exponentialJumpFactor (u ω t) := by
  classical
  have hc : Measurable fun ω ↦ ∑' t, if u ω t = -1 then (1 : ℝ) else 0 :=
    _root_.Prove2MeSourceProof.h_f34c8af209232225589c0804 κ hκ
      (g := fun ω t ↦ if u ω t = -1 then (1 : ℝ) else 0)
      (Measurable.ite (measurableSet_eq_fun hu measurable_const)
        measurable_const measurable_const)
      (fun ω ↦ (_root_.Prove2MeSourceProof.h_6a697584c8707d1dd1f231ef (hs ω)).abs)
      (fun ω t ht ↦ by simp [hzero ω t ht])
  have hlog : Measurable (uncurry fun ω t ↦
      Complex.log (StochLean.exponentialJumpFactor (u ω t) : ℂ)) :=
    Complex.measurable_log.comp (Complex.measurable_ofReal.comp
      ((_root_.Prove2MeSourceProof.h_6a699b84e118f7439b9a72bc (n := 2)).continuous.measurable.comp hu))
  have hl := _root_.Prove2MeSourceProof.h_c4ca568f1e2168c1b07e73bd κ hκ hlog
    (fun ω ↦ _root_.Prove2MeSourceProof.h_61bad4bf4babd22e06805bca (hs ω))
    (fun ω t ht ↦ by simp only [hzero ω t ht, _root_.Prove2MeSourceProof.h_911b993558830136570eb23c,
      Complex.ofReal_one, Complex.log_one])
  have he (ω : Ω) := _root_.Prove2MeSourceProof.h_3f982b6cb5bd7b54e3186947 (hs ω)
  simp_rw [he]
  exact Measurable.ite (measurableSet_eq_fun hc measurable_const)
    (Complex.measurable_re.comp (Complex.measurable_exp.comp hl)) measurable_const
end StochLean


