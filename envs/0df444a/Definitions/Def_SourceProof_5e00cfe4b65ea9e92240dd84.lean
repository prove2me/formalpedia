-- Prove2me | Definitions.Def_SourceProof_5e00cfe4b65ea9e92240dd84
-- name    : SourceProof_5e00cfe4b65ea9e92240dd84
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:43:49.857305+00:00
-- url     : https://prove2.me/theorems/a7a25c45-f5d4-5ed5-b110-bd9e856a0449
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.locally_squareIntegrableMartingale_stochasticIntegral

import Definitions.Def_SourceProof_208de2e405fcede8b8f859e6
import Definitions.Def_SourceProof_250eb65c80240d2467f59640
import Definitions.Def_SourceProof_2685819f27d6afe556e1f973
import Definitions.Def_SourceProof_3167c9529a23dc145fa8582c
import Definitions.Def_SourceProof_45063bef31cb3fd691cc6eb5
import Definitions.Def_SourceProof_470edda0db5866af621dc0b9
import Definitions.Def_SourceProof_6ecb08b0ecac59b7f0cdb61a
import Definitions.Def_SourceProof_6fbf6cb3e9acd382e292d770
import Definitions.Def_SourceProof_73c70764ff89ea6093f75bd8
import Definitions.Def_SourceProof_774fc494feaad8a504659ba2
import Definitions.Def_SourceProof_7e41a7708f0759111a0ce622
import Definitions.Def_SourceProof_80ab6b03444941f707fbb65e
import Definitions.Def_SourceProof_96331e337c0a0b8560074745
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_a239f509638bc9274841d0b5
import Definitions.Def_SourceProof_a306c42680d425170aa442b0
import Definitions.Def_SourceProof_a7b3cca34d6b43059ea19d62
import Definitions.Def_SourceProof_d758c5fe1bf7eec6f7a3ad7f
import Definitions.Def_SourceProof_d93b464447ac66fa122a70c4
import Definitions.Def_SourceProof_de3c03ff359f630b7abb9271
import Definitions.Def_SourceProof_dfba211aff959c1cb4116abf
import Definitions.Def_SourceProof_f50de7c96dd83d69635d466a
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

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
theorem _root_.Prove2MeSourceProof.h_5e00cfe4b65ea9e92240dd84
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (hL : Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F X P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    Locally (fun Y ↦ IsSquareIntegrableMartingale Y F P) F
      (hX.stochasticIntegral hF ha hr) P := by
  obtain ⟨σ, hσ, hM⟩ := hL
  obtain ⟨τ, hτ, _, hb⟩ := (_root_.Prove2MeSourceProof.h_f50de7c96dd83d69635d466a ha) hF hr
  refine ⟨min σ τ, hσ.min hτ, fun n ↦ ?_⟩
  have hσn := hσ.isStoppingTime n
  have hτn := hτ.isStoppingTime n
  let K := fun t ↦ {ω | 0 < τ n ω}.indicator (ProbabilityTheory.cutoffIntegrand H (τ n) t)
  have haK : Adapted F K :=
    (_root_.Prove2MeSourceProof.h_96331e337c0a0b8560074745 (_root_.Prove2MeSourceProof.h_dfba211aff959c1cb4116abf ha hτn)) (hτn.measurableSet_gt 0)
  have hrK : ProbabilityTheory.HasCagladPaths K P := (_root_.Prove2MeSourceProof.h_d93b464447ac66fa122a70c4 ((_root_.Prove2MeSourceProof.h_250eb65c80240d2467f59640 hr) (τ n))) _
  have hSM := (_root_.Prove2MeSourceProof.h_3167c9529a23dc145fa8582c ((_root_.Prove2MeSourceProof.h_6ecb08b0ecac59b7f0cdb61a hX) (hσn.measurableSet_gt 0))) hF hσn
  have hI := (_root_.Prove2MeSourceProof.h_45063bef31cb3fd691cc6eb5 hSM)
    hF (hM n) haK hrK n (by exact_mod_cast hb n)
  have heq := (_root_.Prove2MeSourceProof.h_73c70764ff89ea6093f75bd8 ((_root_.Prove2MeSourceProof.h_774fc494feaad8a504659ba2 hX) hF haK hrK hσn))
    ((_root_.Prove2MeSourceProof.h_a239f509638bc9274841d0b5 ((_root_.Prove2MeSourceProof.h_de3c03ff359f630b7abb9271 ((_root_.Prove2MeSourceProof.h_6fbf6cb3e9acd382e292d770 hX) hF ha hr hτn))
      {ω | 0 < σ n ω})) (σ n))
  rw [_root_.Prove2MeSourceProof.h_2685819f27d6afe556e1f973] at heq
  apply (_root_.Prove2MeSourceProof.h_80ab6b03444941f707fbb65e hI) ?_ heq
  have hρ : IsStoppingTime F (min (σ n) (τ n)) := hσn.min hτn
  exact ((_root_.Prove2MeSourceProof.h_d758c5fe1bf7eec6f7a3ad7f ((_root_.Prove2MeSourceProof.h_96331e337c0a0b8560074745 ((_root_.Prove2MeSourceProof.h_a306c42680d425170aa442b0 hX) hF ha hr))
    (hρ.measurableSet_gt 0)).stronglyAdapted) hF
      (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_7e41a7708f0759111a0ce622 ((_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hX) hF ha hr)) _))
      hρ).adapted
end IsSemimartingale

end ProbabilityTheory


