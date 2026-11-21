-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionConvergence_F001
-- name    : LevyStochCalc_Brownian_ItoL2CompletionConvergence_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:01:11.308078+00:00
-- url     : https://prove2.me/theorems/b3ce36f6-c6b3-43f9-a1df-63690367320c
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoL2CompletionConvergence
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoL2CompletionConvergence. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionIncrement_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionIncrement_F001
import Definitions.Def_SourceProof_410f74bc0d5bdc6969bf4ac5

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: `L¹`/`L²` convergence and adapted approximation

Transfer of the martingale property along `L¹`-limits, criteria for `L¹`
convergence of squares from `L²` bounds, the endpoint `L²` bound for differences of
simple integrals, and the existence of an adapted `SimplePredictable` integrand
within a prescribed `L²([0, T] × Ω)` tolerance of a progressively measurable
square-integrable integrand, together with the norm and increment identities they
use.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Monotonicity of the second moment of an L² martingale.** Immediate from the
orthogonal-increment identity: `𝔼[(M t)²] − 𝔼[(M s)²] = 𝔼[(M t − M s)²] ≥ 0`. This
gives the `L²`-Cauchy property at every intermediate time `t ≤ T` from the
endpoint (`T`) `L²`-bound, since `M t − M' t` is itself a martingale. -/
lemma integral_sq_mono_of_martingale
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {M : ℝ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale M ℱ P)
    {s t : ℝ} (hMs : MeasureTheory.MemLp (M s) 2 P) (hMt : MeasureTheory.MemLp (M t) 2 P)
    (hst : s ≤ t) :
    ∫ ω, (M s ω) ^ 2 ∂P ≤ ∫ ω, (M t ω) ^ 2 ∂P := by
  have h := _root_.Prove2MeSourceProof.h_410f74bc0d5bdc6969bf4ac5 hmart hMs hMt hst
  have h_nn : 0 ≤ ∫ ω, (M t ω - M s ω) ^ 2 ∂P :=
    integral_nonneg (fun ω => sq_nonneg _)
  linarith [h, h_nn]
end LevyStochCalc.Brownian.Ito


