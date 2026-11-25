-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:20.784416+00:00
-- url     : https://prove2.me/theorems/ec5e8315-d0b5-46aa-9646-31531621b3a4
-- title:
--   Last Block Decay
-- statement:
--   Definitions and structural lemmas for Last Block Decay, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LastBlockDecay.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology
open scoped InnerProductSpace
noncomputable section
section dil
def mulEquiv (ρ : ℂ) (hρ : ρ ≠ 0) : ℂ ≃ᵐ ℂ := (Homeomorph.mulLeft₀ ρ hρ).toMeasurableEquiv
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
end dil
end
end Formalism.FourierDecayAlt.P.PBK


