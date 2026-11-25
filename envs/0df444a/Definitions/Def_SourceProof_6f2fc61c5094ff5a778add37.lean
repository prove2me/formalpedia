-- Prove2me | Definitions.Def_SourceProof_6f2fc61c5094ff5a778add37
-- name    : SourceProof_6f2fc61c5094ff5a778add37
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:57:00.971202+00:00
-- url     : https://prove2.me/theorems/a259f163-6438-5d01-a05d-7dd615a3908a
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.isSemimartingale_stochasticExponentialJumpProduct

import Definitions.Def_SourceProof_00a8a291a5ec377d57feab0f
import Definitions.Def_SourceProof_6b0aad381fde89d7c19479e6
import Definitions.Def_SourceProof_8fcba75198d6a3dc02488251
import Definitions.Def_SourceProof_daca2e66d302eb408e43e93d
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The product-defined stochastic exponential is a semimartingale

General cadlag adaptedness and finite variation of the product factor
are proved prerequisites. C2 preservation and multiplication then give
semimartingale regularity of the same canonical expression. This result
does not yet assert its stochastic equation or uniqueness.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_6f2fc61c5094ff5a778add37
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    IsSemimartingale (stochasticExponentialJumpProduct X) F P :=
  (_root_.Prove2MeSourceProof.h_00a8a291a5ec377d57feab0f ((_root_.Prove2MeSourceProof.h_daca2e66d302eb408e43e93d hX) hF))
    ((_root_.Prove2MeSourceProof.h_6b0aad381fde89d7c19479e6 hX) hF) hF
    ((_root_.Prove2MeSourceProof.h_8fcba75198d6a3dc02488251 hX) hF)
end IsSemimartingale

end ProbabilityTheory


