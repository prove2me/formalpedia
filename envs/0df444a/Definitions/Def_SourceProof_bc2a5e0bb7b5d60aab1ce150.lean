-- Prove2me | Definitions.Def_SourceProof_bc2a5e0bb7b5d60aab1ce150
-- name    : SourceProof_bc2a5e0bb7b5d60aab1ce150
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:22:23.645933+00:00
-- url     : https://prove2.me/theorems/a5afcb31-c7ca-505f-a72e-b51851838fcd
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.measurable_eVariationOn_univ_iSup_of_usual

import Definitions.Def_SourceProof_0e901fd5681db7f241412ea5
import Definitions.Def_SourceProof_76feef3dc1aabdf57bee683f

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

theorem _root_.Prove2MeSourceProof.h_bc2a5e0bb7b5d60aab1ce150
    (ha : Adapted F X) (hF : F.IsUsual P) (hc : HasCadlagPaths X P) :
    Measurable[⨆ t, F t] (fun ω ↦ eVariationOn (X · ω) univ) := by
  have he : (fun ω ↦ eVariationOn (X · ω) univ) =
      fun ω ↦ ⨆ n : ℕ, ProbabilityTheory.eTotalVariationProcess X (n : ℝ≥0) ω :=
    funext fun ω ↦ _root_.Prove2MeSourceProof.h_76feef3dc1aabdf57bee683f (X · ω)
  rw [he]
  let : MeasurableSpace Ω := ⨆ t, F t
  exact Measurable.iSup fun n ↦
    ((_root_.Prove2MeSourceProof.h_0e901fd5681db7f241412ea5 ha) hF hc (n : ℝ≥0)).mono
      (le_iSup F (n : ℝ≥0)) le_rfl
end Adapted

end MeasureTheory


