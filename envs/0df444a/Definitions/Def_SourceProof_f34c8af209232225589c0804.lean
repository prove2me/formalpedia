-- Prove2me | Definitions.Def_SourceProof_f34c8af209232225589c0804
-- name    : SourceProof_f34c8af209232225589c0804
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:56:09.695981+00:00
-- url     : https://prove2.me/theorems/80afd2ba-e396-4dea-943f-411e5f92dffa
-- title:
--   StochLean source theorem: StochLean.measurable_tsum_of_support_in_kernel_atoms

import Definitions.Def_SourceProof_23918421d4ee43274d29eb96
import Definitions.Def_SourceProof_557830813c6833ac5ce8fc92
import Definitions.Def_SourceProof_7ec3afbd59428de38f0e2bdf

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Measurability of unweighted series on sample-dependent atom sets

Dividing by the actual singleton mass represents the series as a kernel
integral. Absolute summability proves integrability, and the support
condition handles points of zero mass. Neither the time space nor a
common deterministic set containing all random atoms needs to be countable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped NNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_f34c8af209232225589c0804
    {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω ℝ≥0)
    (hκ : ∀ ω, IsFiniteMeasure (κ ω)) {g : Ω → ℝ≥0 → ℝ}
    (hg : Measurable (uncurry g)) (hs : ∀ ω, Summable (fun t ↦ |g ω t|))
    (hzero : ∀ ω t, κ ω {t} = 0 → g ω t = 0) :
    Measurable fun ω ↦ ∑' t, g ω t := by
  have hm : Measurable fun p : Ω × ℝ≥0 ↦ (κ p.1).real {p.2} :=
    ENNReal.measurable_toReal.comp (_root_.Prove2MeSourceProof.h_7ec3afbd59428de38f0e2bdf κ hκ)
  have hdiv : Measurable (uncurry (fun ω t ↦ g ω t / (κ ω).real {t})) := hg.div hm
  have he (ω : Ω) : (∫ t, g ω t / (κ ω).real {t} ∂StochLean.pointAtomicPart (κ ω)) =
      ∑' t, g ω t := by
    let : IsFiniteMeasure (κ ω) := hκ ω
    exact _root_.Prove2MeSourceProof.h_23918421d4ee43274d29eb96
      (hg.comp measurable_prodMk_left) (hm.comp measurable_prodMk_left) (hs ω) (hzero ω)
  simpa only [he] using _root_.Prove2MeSourceProof.h_557830813c6833ac5ce8fc92 κ hκ hdiv
end StochLean


