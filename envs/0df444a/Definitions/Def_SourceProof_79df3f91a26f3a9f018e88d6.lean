-- Prove2me | Definitions.Def_SourceProof_79df3f91a26f3a9f018e88d6
-- name    : SourceProof_79df3f91a26f3a9f018e88d6
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:27:14.310704+00:00
-- url     : https://prove2.me/theorems/0394c865-6dea-41de-8d26-96e512647174
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.measurable_eVariationOn_univ_of_usual

import Definitions.Def_SourceProof_bc2a5e0bb7b5d60aab1ce150

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurability of actual whole-half-line variation

The existing adapted extended-variation process and its integer horizons
make the original path's canonical `eVariationOn` measurable in the terminal
sigma-field and in the ambient sigma-field. Usual completeness already
handles the common exceptional path event in the compact-variation owner.

These are exact measurability statements for the original function, not
merely measurable versions. No finite-variation assumption, real-valued
conversion, terminal selector, or new stochastic-process predicate is used.
-/

@[expose] public section

open ProbabilityTheory StochLean Set
open scoped NNReal ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace Adapted

theorem _root_.Prove2MeSourceProof.h_79df3f91a26f3a9f018e88d6
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    Measurable (fun ω ↦ eVariationOn (X · ω) univ) :=
  ((_root_.Prove2MeSourceProof.h_bc2a5e0bb7b5d60aab1ce150 ha) hF hc).mono (iSup_le F.le) le_rfl
end Adapted

end MeasureTheory


