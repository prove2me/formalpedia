-- Prove2me | Definitions.Def_MarkovProcess_V3H_Feller_FiniteTimeKernelContinuity_b2a7d2a7
-- name    : MarkovProcess_V3H_Feller_FiniteTimeKernelContinuity_b2a7d2a7
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:35:55.549196+00:00
-- url     : https://prove2.me/theorems/961103e0-0460-4b7e-b1ce-d30475a57b13
-- title:
--   MarkovProcess: MarkovProcess_V3H_Feller_FiniteTimeKernelContinuity_b2a7d2a7
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_Kernel_C0SemigroupJoint_9aea0383
import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuity tools for finite-time Feller kernels

This file records the analytic continuity mechanism needed in a recursive proof of continuity of
finite-time laws.  In particular, strong continuity and contractivity imply joint continuity in
the time and in a varying `C₀` test function.  After evaluation, this gives convergence of kernel
integrals when both the transition time and the test function vary.

The extension from product tests to arbitrary compactly supported tests on a finite product is
not asserted here.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty

namespace MarkovProcess

namespace Semigroup.StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A strongly continuous contraction semigroup acts continuously when both time and the vector
vary.  Strong continuity alone only states this for a fixed vector; contractivity makes the
dependence on the vector uniform in time. -/
theorem p2m_embedded_0957dd8f4e4395ee
    (S : StronglyContinuousContractionSemigroup E) {X : Type*} {l : Filter X}
    {t : X → NNReal} {t₀ : NNReal} {f : X → E} {f₀ : E}
    (ht : Tendsto t l (nhds t₀)) (hf : Tendsto f l (nhds f₀)) :
    Tendsto (fun x ↦ S (t x) (f x)) l (nhds (S t₀ f₀)) := by
  rw [Metric.tendsto_nhds] at hf ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have htime : ∀ᶠ x in l, dist (S (t x) f₀) (S t₀ f₀) < ε / 2 :=
    ((S.continuous f₀).tendsto t₀ |>.comp ht) (Metric.ball_mem_nhds _ hhalf)
  filter_upwards [hf (ε / 2) hhalf, htime] with x hx htx
  calc
    dist (S (t x) (f x)) (S t₀ f₀)
        ≤ dist (S (t x) (f x)) (S (t x) f₀) +
            dist (S (t x) f₀) (S t₀ f₀) := dist_triangle _ _ _
    _ ≤ dist (f x) f₀ + dist (S (t x) f₀) (S t₀ f₀) :=
      by
        simpa only [add_comm] using
          add_le_add_right (S.dist_apply_le (t x) (f x) f₀)
            (dist (S (t x) f₀) (S t₀ f₀))
    _ < ε / 2 + ε / 2 := add_lt_add hx htx
    _ = ε := add_halves ε



end Semigroup.StronglyContinuousContractionSemigroup

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]





end SubMarkovKernelSemigroup

end MarkovProcess


