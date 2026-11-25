-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:43:41.767264+00:00
-- url     : https://prove2.me/theorems/df0fa385-3f69-443f-bca6-540400f758cd
-- title:
--   Norm Of Mem Root Set One
-- statement:
--   Definitions and structural lemmas for Norm Of Mem Root Set One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/NormOfMemRootSetOne.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology Set Polynomial
noncomputable section
open Classical
section change
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
end change
section asym
def lamR (s : ℕ) (σ x : ℂ) : ℂ := (x / (x + σ)) ^ (s - 1)
def rhoR (s : ℕ) (σ x : ℂ) : ℂ := lamR s σ x ^ ((s : ℂ)⁻¹)
end asym
end
end Formalism.FourierDecayAlt.P.PBK


