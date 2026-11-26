-- Prove2me | Definitions.Def_SourceProof_ff03f74ed817cc1d54b3540e
-- name    : SourceProof_ff03f74ed817cc1d54b3540e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T22:53:51.029733+00:00
-- url     : https://prove2.me/theorems/ba13f748-e186-5fe6-962d-6d40347f2439
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.isLocalMartingale_stochasticIntegral_of_locally_squareIntegrable

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_SourceProof_470edda0db5866af621dc0b9
import Definitions.Def_SourceProof_5e00cfe4b65ea9e92240dd84
import Definitions.Def_SourceProof_eca6d372e09543f30c7c6907
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Lipschitz

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Protter II.20: locally square-integrable martingale preservation

The integrator's L2 localizers and the integrand's norm-exit localizers are combined
by their pointwise minimum. Bounded integration of the first masked process against
the second masked cutoff is exactly this joint localization of the final integral.
No integrability or vanishing assumption on the unmasked initial value is required.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_ff03f74ed817cc1d54b3540e
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hL : Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F X P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    IsLocalMartingale (hX.stochasticIntegral hF ha hr) F P :=
  _root_.Prove2MeSourceProof.h_eca6d372e09543f30c7c6907 hF
    ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hX) hF ha hr)
    ((_root_.Prove2MeSourceProof.h_5e00cfe4b65ea9e92240dd84 hX) hF hL ha hr)
end IsSemimartingale

end ProbabilityTheory


