-- Prove2me | Definitions.Def_SourceProof_c4ca568f1e2168c1b07e73bd
-- name    : SourceProof_c4ca568f1e2168c1b07e73bd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:06:21.786394+00:00
-- url     : https://prove2.me/theorems/17a07994-87a8-5e71-bc4f-26aa61a48537
-- title:
--   StochLean source theorem: StochLean.measurable_complex_tsum_of_support_in_kernel_atoms

import Definitions.Def_SourceProof_f34c8af209232225589c0804
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Complex series on sample-dependent atom sets

The real and imaginary series use the same finite-fiber kernel and its
intrinsic atoms. Actual complex summability justifies coordinate sums.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_c4ca568f1e2168c1b07e73bd
    {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℝ≥0)
    (hκ : ∀ ω, IsFiniteMeasure (κ ω)) {g : Ω → ℝ≥0 → ℂ}
    (hg : Measurable (uncurry g)) (hs : ∀ ω, Summable (g ω))
    (hzero : ∀ ω t, κ ω {t} = 0 → g ω t = 0) :
    Measurable fun ω ↦ ∑' t, g ω t := by
  have hr := _root_.Prove2MeSourceProof.h_f34c8af209232225589c0804 κ hκ
    (g := fun ω t ↦ (g ω t).re)
    (Complex.measurable_re.comp hg)
    (fun ω ↦ (Complex.hasSum_re (hs ω).hasSum).summable.abs)
    (fun ω t ht ↦ congrArg Complex.re (hzero ω t ht))
  have hi := _root_.Prove2MeSourceProof.h_f34c8af209232225589c0804 κ hκ
    (g := fun ω t ↦ (g ω t).im)
    (Complex.measurable_im.comp hg)
    (fun ω ↦ (Complex.hasSum_im (hs ω).hasSum).summable.abs)
    (fun ω t ht ↦ congrArg Complex.im (hzero ω t ht))
  have h := (Complex.measurable_ofReal.comp hr).add
    ((Complex.measurable_ofReal.comp hi).mul_const Complex.I)
  change Measurable (fun ω ↦ Complex.ofReal (∑' t, (g ω t).re) +
    Complex.ofReal (∑' t, (g ω t).im) * Complex.I) at h
  have hre (ω : Ω) := Complex.re_tsum (hs ω)
  have him (ω : Ω) := Complex.im_tsum (hs ω)
  simpa only [← hre, ← him, Complex.re_add_im] using h
end StochLean


