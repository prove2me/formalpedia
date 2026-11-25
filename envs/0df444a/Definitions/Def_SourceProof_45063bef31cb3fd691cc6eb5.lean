-- Prove2me | Definitions.Def_SourceProof_45063bef31cb3fd691cc6eb5
-- name    : SourceProof_45063bef31cb3fd691cc6eb5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:28:06.665702+00:00
-- url     : https://prove2.me/theorems/3f7ff985-fc45-553f-a032-87de1378c7e0
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.isSquareIntegrableMartingale_stochasticIntegral_of_bounded

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_SourceProof_1658b3fb6ad99d5c993a7785
import Definitions.Def_SourceProof_5333e24f05ba3b972814acde
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_77e3615cd5fb18090525a5f1
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_a306c42680d425170aa442b0
import Definitions.Def_SourceProof_bc13bcc2e8c79f08b8230861
import Definitions.Def_SourceProof_be0b26cebaa157c758248f0a
import Definitions.Def_SourceProof_d0a4533c9dc122ef1fd7f577
import Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e
import Definitions.Def_SourceProof_f1d6b3dcfada66cafb4e9e50
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.MetricSpace.Lipschitz

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The bounded-integrand step of Protter II.20

Bounded simple approximation, the source second-moment estimate and actual
uniform-integrability limits give the finite-time L2 martingale result. Neither
the integrator nor the integral is centered by discarding its initial value.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_45063bef31cb3fd691cc6eb5
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hM : IsSquareIntegrableMartingale X F P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (C : ℝ≥0)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖H t ω‖ ≤ C) :
    IsSquareIntegrableMartingale (hX.stochasticIntegral hF ha hr) F P := by
  obtain ⟨S, hS, hSb, huS⟩ := _root_.Prove2MeSourceProof.h_1658b3fb6ad99d5c993a7785 ha hF hr C hb
  have huJ := (_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hX) hF ha hr hS huS
  have hJS (n : ℕ) : ProbabilityTheory.IsSquareIntegrableMartingale ((hS n).elementaryIntegralProcess X) F P :=
    (_root_.Prove2MeSourceProof.h_5333e24f05ba3b972814acde (hS n)) hM hF
      (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) C (hSb n)
  refine ⟨_root_.Prove2MeSourceProof.h_be0b26cebaa157c758248f0a (fun n ↦ (hJS n).1)
    ((_root_.Prove2MeSourceProof.h_a306c42680d425170aa442b0 hX) hF ha hr).stronglyAdapted ?_ (_root_.Prove2MeSourceProof.h_d0a4533c9dc122ef1fd7f577 huJ),
    fun t ↦ (_root_.Prove2MeSourceProof.h_f1d6b3dcfada66cafb4e9e50 hX) hF hM.1 ha hr C hb t (hM.2 t)⟩
  intro t
  let D : ℝ≥0 := ⟨(C : ℝ) ^ 2 * ∫ ω, (X t ω) ^ 2 ∂P,
    mul_nonneg (sq_nonneg _) (integral_nonneg (fun ω ↦ sq_nonneg (X t ω)))⟩
  apply _root_.Prove2MeSourceProof.h_77e3615cd5fb18090525a5f1 (fun n ↦ (hJS n).2 t) D
  intro n
  exact (_root_.Prove2MeSourceProof.h_bc13bcc2e8c79f08b8230861 (hS n)) hM.1 hF
    (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX)) t (hM.2 t) C (hSb n)
end IsSemimartingale

end ProbabilityTheory


