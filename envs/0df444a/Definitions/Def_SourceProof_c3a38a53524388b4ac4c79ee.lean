-- Prove2me | Definitions.Def_SourceProof_c3a38a53524388b4ac4c79ee
-- name    : SourceProof_c3a38a53524388b4ac4c79ee
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:24:06.713977+00:00
-- url     : https://prove2.me/theorems/a9984c6b-f9ec-5981-ac13-74146a00cd25
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.tendstoUCP_quadraticVariationSumProcess

import Definitions.Def_StochLean_Probability_Process_Partition_SquareSums_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticVariation_F000
import Definitions.Def_SourceProof_215f6d5e6b10999a8c8f10ba
import Definitions.Def_SourceProof_24278e78a60501166c68bfc8
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_502517db36e3723689ca0e06
import Definitions.Def_SourceProof_5922ecc268414b6fc6aec126
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_ff07642989734d14cb2ac8eb

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Random-partition square sums converge to the raw quadratic variation

Exact telescoping reduces the square sums to the stopped square minus twice
the left Riemann sum. Endpoint exhaustion and the proved cadlag-integrand
Riemann theorem then give UCP convergence, with the original initial square.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_c3a38a53524388b4ac4c79ee
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    TendstoUCP P (fun n ↦ (π n).quadraticVariationSumProcess X) atTop
      (hX.quadraticVariation hF) := by
  have hsq := (_root_.Prove2MeSourceProof.h_215f6d5e6b10999a8c8f10ba hπ) (fun t ω ↦ (X t ω) ^ 2)
  have hJ := (_root_.Prove2MeSourceProof.h_5922ecc268414b6fc6aec126 hX)
    hF (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX) hπ
  have hu := (_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb hsq) ((_root_.Prove2MeSourceProof.h_24278e78a60501166c68bfc8 hJ) 2)
  have heq (n : ℕ) : (fun t ω ↦ (X (min ((π n).terminal ω) t) ω) ^ 2) -
      (2 : ℝ) • (π n).leftRiemannSumProcess X X = (π n).quadraticVariationSumProcess X := by
    funext t ω
    exact ((_root_.Prove2MeSourceProof.h_502517db36e3723689ca0e06 (π n)) X t ω).symm
  rw [show (fun n ↦ (fun t ω ↦ (X (min ((π n).terminal ω) t) ω) ^ 2) -
    (2 : ℝ) • (π n).leftRiemannSumProcess X X) =
      (fun n ↦ (π n).quadraticVariationSumProcess X) from funext heq] at hu
  exact hu
end IsSemimartingale

end ProbabilityTheory


