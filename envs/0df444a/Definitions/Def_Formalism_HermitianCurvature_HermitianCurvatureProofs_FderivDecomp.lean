-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FderivDecomp
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FderivDecomp
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:03:51.231195+00:00
-- url     : https://prove2.me/theorems/f5c10279-99b1-4e5a-8551-d25ace823647
-- title:
--   Fderiv Decomp
-- statement:
--   Definitions and structural lemmas for Fderiv Decomp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FderivDecomp.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtPrim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
def wZ (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 - I * fderiv ℝ f ζ I)
def wZb (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 + I * fderiv ℝ f ζ I)
def Hh (TT : ℝ) : Set ℂ := {w | TT < Complex.normSq (Complex.exp w)}
def bet (α : ℂ → ℂ) (w : ℂ) : ℂ := α (Complex.exp w) * Complex.exp w
def omL : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (2 : ℝ) • (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.imCLM).comp (ContinuousLinearMap.mul ℝ ℂ)
def om (α : ℂ → ℂ) (w : ℂ) : ℂ →L[ℝ] ℝ := omL (bet α w)
end
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann


