-- Prove2me | Definitions.Def_SourceProof_23918421d4ee43274d29eb96
-- name    : SourceProof_23918421d4ee43274d29eb96
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:45:12.30139+00:00
-- url     : https://prove2.me/theorems/41ab2e9a-6a57-509f-83a8-87b25041403e
-- title:
--   StochLean source theorem: StochLean.integral_pointAtomicPart_div_singleton_eq_tsum

import Definitions.Def_SourceProof_d12b203582a773ced0e16a77
import Definitions.Def_SourceProof_da9aca4c0192738c4fa4fc29

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Integrability from actual summable point-atomic weights

The finite measure may live on an uncountable space. Only its intrinsic
countable atom set is used. The inverse singleton mass converts supported
unweighted series into integrals, with zero-mass points handled explicitly.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace StochLean

variable {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass T]
  {μ : Measure T} [IsFiniteMeasure μ] {f g : T → ℝ}

theorem _root_.Prove2MeSourceProof.h_23918421d4ee43274d29eb96
    (hg : Measurable g) (hm : Measurable (fun t ↦ μ.real {t}))
    (hs : Summable (fun t ↦ |g t|)) (hzero : ∀ t, μ {t} = 0 → g t = 0) :
    (∫ t, g t / μ.real {t} ∂pointAtomicPart μ) = ∑' t, g t := by
  rw [_root_.Prove2MeSourceProof.h_da9aca4c0192738c4fa4fc29 (_root_.Prove2MeSourceProof.h_d12b203582a773ced0e16a77 hg hm hs)]
  apply tsum_congr
  intro t
  by_cases hz : μ {t} = 0
  · simp [measureReal_def, hz, hzero t hz]
  · have hn : μ.real {t} ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hz, measure_ne_top μ {t}⟩
    field_simp
end StochLean


