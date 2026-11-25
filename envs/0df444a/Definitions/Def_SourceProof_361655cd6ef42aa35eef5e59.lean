-- Prove2me | Definitions.Def_SourceProof_361655cd6ef42aa35eef5e59
-- name    : SourceProof_361655cd6ef42aa35eef5e59
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:48:44.185813+00:00
-- url     : https://prove2.me/theorems/e3680414-9a62-55da-a5a2-1dc2a0bb67a5
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.exists_stochasticIntegral

import Definitions.Def_SourceProof_85cd6acbb88cb0e0bb47ef85
import Definitions.Def_SourceProof_abb8e2f5680049693694a2fd
import Definitions.Def_SourceProof_bc53441c2020b643491018cd
import Definitions.Def_SourceProof_bee42c1697f2f3875544b7d3
import Definitions.Def_SourceProof_c55d17120c217e6f4e472165
import Definitions.Def_SourceProof_cc0035184dadaa0334c1eb46
import Definitions.Def_SourceProof_ff07642989734d14cb2ac8eb

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

theorem _root_.Prove2MeSourceProof.h_361655cd6ef42aa35eef5e59
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    ∃ J : ℝ≥0 → Ω → ℝ, Adapted F J ∧ (∀ ω, IsCadlagPath (J · ω)) ∧
      ∀ S : ℕ → ℝ≥0 → Ω → ℝ, ∀ hS : ∀ n, IsSimplePredictable (S n) F,
        TendstoUCP P S atTop H →
          TendstoUCP P (fun n ↦ (hS n).elementaryIntegralProcess X) atTop J := by
  obtain ⟨S, hS, huS⟩ := _root_.Prove2MeSourceProof.h_abb8e2f5680049693694a2fd ha hF hr
  obtain ⟨J, hJa, hJr, hJS⟩ := (_root_.Prove2MeSourceProof.h_bee42c1697f2f3875544b7d3 hX) hF hS huS
  refine ⟨J, hJa, hJr, ?_⟩
  intro R hR huR
  have hd : ProbabilityTheory.TendstoUCP P (fun n ↦ R n - S n) atTop 0 := by
    simpa only [sub_self] using (_root_.Prove2MeSourceProof.h_ff07642989734d14cb2ac8eb huR) huS
  have hJd := (_root_.Prove2MeSourceProof.h_85cd6acbb88cb0e0bb47ef85 hX) hF (fun n ↦ (_root_.Prove2MeSourceProof.h_bc53441c2020b643491018cd (hR n)) (hS n)) hd
  have hsum := (_root_.Prove2MeSourceProof.h_c55d17120c217e6f4e472165 hJd) hJS
  have heq : (fun n ↦ ((_root_.Prove2MeSourceProof.h_bc53441c2020b643491018cd (hR n)) (hS n)).elementaryIntegralProcess X +
      (hS n).elementaryIntegralProcess X) = fun n ↦ (hR n).elementaryIntegralProcess X := by
    funext n
    rw [(_root_.Prove2MeSourceProof.h_cc0035184dadaa0334c1eb46 (hR n)) (hS n) X, sub_add_cancel]
  simpa only [heq, zero_add] using hsum
end IsSemimartingale

end ProbabilityTheory


