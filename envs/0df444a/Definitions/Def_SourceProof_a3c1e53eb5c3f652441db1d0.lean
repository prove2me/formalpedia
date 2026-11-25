-- Prove2me | Definitions.Def_SourceProof_a3c1e53eb5c3f652441db1d0
-- name    : SourceProof_a3c1e53eb5c3f652441db1d0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:27:06.019031+00:00
-- url     : https://prove2.me/theorems/0638d0e6-5d92-4de2-bf25-72d9bc8c7cd5
-- title:
--   StochLean source theorem: ProbabilityTheory.IsPreLocalizingSequence.adapted_of_masked

import Definitions.Def_SourceProof_46e00cd1de49de31920230f6
import Definitions.Def_SourceProof_49a22f8c8626f92746c475a0
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Definitions.Def_SourceProof_e79cc5d7fc8aa48d10e205ad
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Iterated localization

The stable property used internally is the conjunction of the canonical UI
martingale and common-event cadlag predicates. Mathlib's diagonal extraction
and local-property idempotence are reused. An explicit tail infimum converts
its AE-monotone witness to the everywhere-monotone fundamental sequence used
by this project. No local-martingale theorem is assumed as a structure field.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

namespace IsPreLocalizingSequence
omit [IsFiniteMeasure P] in

theorem _root_.Prove2MeSourceProof.h_a3c1e53eb5c3f652441db1d0 {τ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : IsPreLocalizingSequence F τ P) (hF : F.IsUsual P)
    (ha : ∀ n, Adapted F
      (stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n))) : Adapted F X := by
  intro t
  let U n := stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n) t
  have hm : StronglyMeasurable[F t] (fun ω ↦ limUnder atTop (fun n ↦ U n ω)) := by
    let : MeasurableSpace Ω := F t
    exact StronglyMeasurable.limUnder (fun n ↦ (ha n t).stronglyMeasurable)
  have heq : (fun ω ↦ limUnder atTop (fun n ↦ U n ω)) =ᵐ[P] X t := by
    filter_upwards [(_root_.Prove2MeSourceProof.h_49a22f8c8626f92746c475a0 (X := X) hτ) t] with ω hω
    have he : (fun n ↦ U n ω) =ᶠ[atTop] (fun _ ↦ X t ω) := hω
    exact (tendsto_const_nhds.congr' he.symm).limUnder_eq
  have hc : MeasureTheory.IsCompleteSubMeasurableSpace P (F t) := fun A hA ↦
    F.mono bot_le A ((_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) A hA)
  exact (_root_.Prove2MeSourceProof.h_46e00cd1de49de31920230f6 hc) hm.measurable heq
end IsPreLocalizingSequence

end ProbabilityTheory


