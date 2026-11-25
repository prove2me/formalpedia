-- Prove2me | Definitions.Def_SourceProof_ca1768529b4cdee6d56d9537
-- name    : SourceProof_ca1768529b4cdee6d56d9537
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T12:46:07.690854+00:00
-- url     : https://prove2.me/theorems/8ad0c82b-892c-56e0-b66e-16a1548c1a85
-- title:
--   StochLean source theorem: StochLean.measurable_pointDiffusePart_of_finite_fibers

import Definitions.Def_SourceProof_7ec3afbd59428de38f0e2bdf
import Definitions.Def_SourceProof_8541783849134de6ca757428

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurable removal of the point atoms of a random finite measure

Joint singleton mass is the kernel integral of the measurable diagonal. The
zero-singleton-mass region is therefore jointly measurable, so its restriction
is again a measurable random measure. Only fiberwise finite mass is required.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace StochLean

variable {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℝ≥0)
  (hκ : ∀ ω, IsFiniteMeasure (κ ω))

include hκ

theorem _root_.Prove2MeSourceProof.h_ca1768529b4cdee6d56d9537 :
    Measurable fun ω ↦ pointDiffusePart (κ ω) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  let S : Set (Ω × ℝ≥0) := {p | p.2 ∈ s ∧ κ p.1 {p.2} = 0}
  have hS : MeasurableSet S :=
    (measurable_snd hs).inter
      (measurableSet_eq_fun (_root_.Prove2MeSourceProof.h_7ec3afbd59428de38f0e2bdf κ hκ) measurable_const)
  have h := _root_.Prove2MeSourceProof.h_8541783849134de6ca757428 hκ
    (show Measurable (S.indicator (fun _ ↦ (1 : ℝ≥0∞))) from measurable_const.indicator hS)
  have heq (ω : Ω) : (∫⁻ t, S.indicator (fun _ ↦ (1 : ℝ≥0∞)) (ω, t) ∂κ ω) =
      StochLean.pointDiffusePart (κ ω) s := by
    rw [lintegral_indicator_const_comp (f := Prod.mk ω) measurable_prodMk_left hS 1, one_mul,
      StochLean.pointDiffusePart, Measure.restrict_apply hs]
    congr 1
    ext t
    simp only [S, StochLean.pointAtomSet, mem_preimage, mem_ofPred_eq, mem_inter_iff, mem_compl_iff,
      not_not]
  simpa only [heq] using h
end StochLean


