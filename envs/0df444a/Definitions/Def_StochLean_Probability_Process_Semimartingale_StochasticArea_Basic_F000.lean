-- Prove2me | Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticArea_Basic_F000
-- name    : StochLean_Probability_Process_Semimartingale_StochasticArea_Basic_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:57:57.723555+00:00
-- url     : https://prove2.me/theorems/999ecedf-d954-59f1-b93c-a862319d8cc2
-- title:
--   StochLean: Probability.Process.Semimartingale.StochasticArea.Basic F000

import Definitions.Def_StochLean_Probability_Process_Path_LeftLimit_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticIntegral_F000
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_2d0886ee2025f07cabb3dec2
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_dff15d58aea8e47b608598ba
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
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Lipschitz

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The actual antisymmetric stochastic area integral

The source area is `integral X_- dY - integral Y_- dX`, using the sole
Chapter II stochastic integral. It is twice the signed geometric area in
Protter's convention. It starts at zero even for arbitrary initial values.
Continuous local-martingale coordinates give a continuous local martingale;
neither Brownian laws nor a bracket formula are built into the definition.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

noncomputable def IsSemimartingale.stochasticArea
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ℝ≥0 → Ω → ℝ :=
  hY.stochasticIntegral hF ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
    (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) -
  hX.stochasticIntegral hF ((_root_.Prove2MeSourceProof.h_2d0886ee2025f07cabb3dec2 (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hY)) hF (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY))
    (_root_.Prove2MeSourceProof.h_dff15d58aea8e47b608598ba (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY))
end ProbabilityTheory


