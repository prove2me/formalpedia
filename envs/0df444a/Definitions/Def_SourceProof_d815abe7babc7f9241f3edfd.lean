-- Prove2me | Definitions.Def_SourceProof_d815abe7babc7f9241f3edfd
-- name    : SourceProof_d815abe7babc7f9241f3edfd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:54:32.675296+00:00
-- url     : https://prove2.me/theorems/562dfaeb-6c4f-4fd7-831a-aea8a043ef54
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.stronglyAdapted_tsum_Ioc_large_jumps_of_cadlag

import Definitions.Def_StochLean_ForMathlib_Topology_Algebra_InfiniteSum_LifetimeReindex_F000
import Definitions.Def_StochLean_Probability_Process_Stopping_TerminalValue_F000
import Definitions.Def_SourceProof_20377c625b34905cce0ac877
import Definitions.Def_SourceProof_335e23439381136e5a7ba192
import Definitions.Def_SourceProof_62aa9c78f78fd9c67ea0fbce
import Definitions.Def_SourceProof_7270b3ab7a1632573e0ea3ed
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Actual large-jump sums through the existing lifetime enumeration

The canonical large-jump sequence escapes each finite horizon. Consequently
only finitely many of its closed steps are active by that horizon, and their
actual coefficient series is summable. Unique finite lifetimes and complete
large-jump coverage reindex this series as the literal positive-time jump sum.

An arbitrary real transformation is allowed at each jump. In particular, no
zero-preservation condition is imposed: the lifetime indicator remains outside
the transformation, so an infinite lifetime never contributes a finite-time
term, even when the transformation is nonzero at zero. Signed and norm sums
are the identity and norm specializations of the same result.

Adaptedness follows from the existing stopped-jump measurability and native
measurability of a countable sum. No new process, sum, or sampling owner is
introduced, and no integrability or jump-count moment is assumed.
-/

@[expose] public section

open MeasureTheory Filter Set Function
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {b : ℝ}

end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b : ℝ}

namespace Adapted

theorem _root_.Prove2MeSourceProof.h_d815abe7babc7f9241f3edfd [F.IsRightContinuous]
    (ha : Adapted F X) (hc : ∀ ω, IsCadlagPath (X · ω)) (hb : 0 < b)
    {φ : ℝ → ℝ} (hφ : Measurable φ) :
    StronglyAdapted F (fun (t : ℝ≥0) ω ↦
      ∑' s : Ioc 0 t, if b < ‖jumpProcess X s ω‖ then φ (jumpProcess X s ω) else 0) := by
  have hτ (n : ℕ) : IsStoppingTime F (ProbabilityTheory.largeJumpSequence X b n) :=
    (_root_.Prove2MeSourceProof.h_335e23439381136e5a7ba192 ha) hc hb n
  have hm (n : ℕ) : StronglyMeasurable[(hτ n).measurableSpace]
      (fun ω ↦ φ (MeasureTheory.stoppedValueWithTerminal (ProbabilityTheory.jumpProcess X) (fun _ ↦ (0 : ℝ))
        (ProbabilityTheory.largeJumpSequence X b n) ω)) :=
    (hφ.comp ((_root_.Prove2MeSourceProof.h_20377c625b34905cce0ac877 ha) hc (hτ n)).measurable).stronglyMeasurable
  intro T
  let : MeasurableSpace Ω := F T
  have he : (fun ω ↦ ∑' n : ℕ,
      {v | ProbabilityTheory.largeJumpSequence X b n v ≤ (T : WithTop ℝ≥0)}.indicator
        (fun v ↦ φ (MeasureTheory.stoppedValueWithTerminal (ProbabilityTheory.jumpProcess X) (fun _ ↦ (0 : ℝ))
          (ProbabilityTheory.largeJumpSequence X b n) v)) ω) =
      (fun ω ↦ ∑' s : Ioc 0 T,
        if b < ‖ProbabilityTheory.jumpProcess X s ω‖ then φ (ProbabilityTheory.jumpProcess X s ω) else 0) :=
    funext fun ω ↦ (_root_.Prove2MeSourceProof.h_62aa9c78f78fd9c67ea0fbce (hc ω)) hb φ T
  change StronglyMeasurable[F T] (fun ω ↦ ∑' s : Ioc 0 T,
    if b < ‖ProbabilityTheory.jumpProcess X s ω‖ then φ (ProbabilityTheory.jumpProcess X s ω) else 0)
  rw [← he]
  exact StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ)
    (fun n ↦ (fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_7270b3ab7a1632573e0ea3ed p2mMethodArg0 (hm n)) (hτ n) T)
end Adapted

end MeasureTheory


