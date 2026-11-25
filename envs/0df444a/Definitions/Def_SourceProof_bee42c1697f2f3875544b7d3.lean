-- Prove2me | Definitions.Def_SourceProof_bee42c1697f2f3875544b7d3
-- name    : SourceProof_bee42c1697f2f3875544b7d3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:37:25.612812+00:00
-- url     : https://prove2.me/theorems/56155593-39a2-5740-a9d1-4a31b037e8de
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.exists_elementaryIntegralProcess_limit

import Definitions.Def_SourceProof_1802507598740e0a76388352
import Definitions.Def_SourceProof_260006becf8053b16cb2c165
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_578c5291502c2a4d4272ca3a
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_932e1321dcffebeba90e2ea9
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_bae5ae9701ba5ce704cf231a
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.WithTop

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Construction of the Chapter II integral by simple UCP approximation

Density supplies an actual sequence, source continuity makes its elementary
integrals Cauchy, and UCP completeness constructs their adapted cadlag limit.
Linearity and source continuity then prove convergence for every simple
approximation of the same integrand. No integral operator is assumed as data.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_bee42c1697f2f3875544b7d3
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {S : ℕ → ℝ≥0 → Ω → ℝ} (hS : ∀ n, IsSimplePredictable (S n) F)
    (hu : TendstoUCP P S atTop H) :
    ∃ J : ℝ≥0 → Ω → ℝ, Adapted F J ∧ (∀ ω, IsCadlagPath (J · ω)) ∧
      TendstoUCP P (fun n ↦ (hS n).elementaryIntegralProcess X) atTop J := by
  have hc : ProbabilityTheory.CauchyUCP P (fun n ↦ (hS n).elementaryIntegralProcess X) :=
    (_root_.Prove2MeSourceProof.h_1802507598740e0a76388352 hX) hF hS (_root_.Prove2MeSourceProof.h_260006becf8053b16cb2c165 hu)
  exact (_root_.Prove2MeSourceProof.h_578c5291502c2a4d4272ca3a hc)
    (fun n ↦ (_root_.Prove2MeSourceProof.h_bae5ae9701ba5ce704cf231a (hS n)) (_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) hF
      (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))) hF
    (fun n ↦ (_root_.Prove2MeSourceProof.h_932e1321dcffebeba90e2ea9 (hS n)) (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX))
end IsSemimartingale

end ProbabilityTheory


