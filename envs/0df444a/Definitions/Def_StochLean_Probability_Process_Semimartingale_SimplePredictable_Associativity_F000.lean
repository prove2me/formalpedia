-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Associativity_F000
-- name    : StochLean_Probability_Process_Semimartingale_SimplePredictable_Associativity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:01:09.903427+00:00
-- url     : https://prove2.me/theorems/0b2dc6ca-17e1-5e6b-afd1-e0b4774d007b
-- title:
--   StochLean: Probability.Process.Semimartingale.SimplePredictable.Associativity F000

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_SourceProof_0146b8a6534f7d6ff6a61309
import Definitions.Def_SourceProof_335ae0b6c99b920a26294278
import Definitions.Def_SourceProof_45763a1547f08491c4364e73
import Definitions.Def_SourceProof_8f7895612117943074291d58
import Definitions.Def_SourceProof_a9c44e06617a4753cffd0417
import Definitions.Def_SourceProof_ec04cdbdbe92b05b4697a078
import Definitions.Def_SourceProof_f2413a3b51825efc6a057b76
import Definitions.Def_SourceProof_f342d2c1dd9e363eb1f13e2b
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Predictable
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Associativity of source elementary integration

Actual common stopping partitions reduce the proof to the integral increment
on one cell. Both the initial coefficient product and every repeated endpoint
are retained. The integrator is arbitrary; no semimartingale premise is used.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

private theorem integral_integralProcess_of_partition_eq
    (G H : SimplePredictableRep F) (hp : G.partition = H.partition) (X : ℝ≥0 → Ω → ℝ) :
    G.integral (H.integralProcess X) =
      ((_root_.Prove2MeSourceProof.h_f2413a3b51825efc6a057b76 (show IsSimplePredictable G.toProcess F from ⟨G, rfl⟩))
        (show IsSimplePredictable H.toProcess F from ⟨H, rfl⟩)).elementaryIntegral X := by
  rcases G with ⟨π, g0, hg0, g, hg⟩
  rcases H with ⟨ρ, h0, hh0, h, hh⟩
  change π = ρ at hp
  subst ρ
  let G : SimplePredictableRep F := ⟨π, g0, hg0, g, hg⟩
  let H : SimplePredictableRep F := ⟨π, h0, hh0, h, hh⟩
  let R : SimplePredictableRep F :=
    ⟨π, fun ω ↦ g0 ω * h0 ω, hg0.mul hh0,
      fun i ω ↦ g i ω * h i ω, fun i ↦ (hg i).mul (hh i)⟩
  have hR : R.toProcess = G.toProcess * H.toProcess := by
    funext t ω
    change R.toProcess t ω = G.toProcess t ω * H.toProcess t ω
    by_cases ht : t = 0
    · subst t
      simp only [_root_.Prove2MeSourceProof.h_a9c44e06617a4753cffd0417]
      rfl
    · by_cases hterm : t ≤ π.terminal ω
      · obtain ⟨i, hi⟩ := (_root_.Prove2MeSourceProof.h_8f7895612117943074291d58 (π.path ω))
          (show (0 : ℝ≥0) < t ∧ t ≤ π.terminal ω from ⟨pos_iff_ne_zero.mpr ht, hterm⟩)
        rw [(_root_.Prove2MeSourceProof.h_45763a1547f08491c4364e73 (i := i) R) hi,
          (_root_.Prove2MeSourceProof.h_45763a1547f08491c4364e73 (i := i) G) hi,
          (_root_.Prove2MeSourceProof.h_45763a1547f08491c4364e73 (i := i) H) hi]
      · rw [(_root_.Prove2MeSourceProof.h_335ae0b6c99b920a26294278 R) (lt_of_not_ge hterm),
          (_root_.Prove2MeSourceProof.h_335ae0b6c99b920a26294278 G) (lt_of_not_ge hterm),
          (_root_.Prove2MeSourceProof.h_335ae0b6c99b920a26294278 H) (lt_of_not_ge hterm), mul_zero]
  rw [_root_.Prove2MeSourceProof.h_ec04cdbdbe92b05b4697a078 _ R hR]
  funext ω
  change g0 ω * H.integralProcess X 0 ω +
      (∑ i : Fin π.size, g i ω * (H.integralProcess X (π.point i.succ ω) ω -
        H.integralProcess X (π.point i.castSucc ω) ω)) =
    (g0 ω * h0 ω) * X 0 ω +
      ∑ i : Fin π.size, (g i ω * h i ω) * (X (π.point i.succ ω) ω - X (π.point i.castSucc ω) ω)
  rw [(_root_.Prove2MeSourceProof.h_0146b8a6534f7d6ff6a61309 H)]
  have hi (i : Fin π.size) : H.integralProcess X (π.point i.succ ω) ω -
      H.integralProcess X (π.point i.castSucc ω) ω =
        h i ω * (X (π.point i.succ ω) ω - X (π.point i.castSucc ω) ω) :=
    (_root_.Prove2MeSourceProof.h_f342d2c1dd9e363eb1f13e2b H) X i ω
  have hinit : H.initial = h0 := rfl
  simp only [hi, hinit, mul_assoc]
end SimplePredictableRep

namespace IsSimplePredictable

variable {G H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable

end ProbabilityTheory


