-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivWordLeIntegralOfAevalCasimirEqZero
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivWordLeIntegralOfAevalCasimirEqZero
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:56:41.159806+00:00
-- url     : https://prove2.me/theorems/15e35546-d032-4207-9a7f-f589e5970e4d
-- title:
--   Deriv Word Le Integral Of Aeval Casimir Eq Zero
-- statement:
--   Definitions and structural lemmas for Deriv Word Le Integral Of Aeval Casimir Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DerivWordLeIntegralOfAevalCasimirEqZero.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInteriorEstimateDerivWordPolyLaplacianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SetIntegralNormProdExpMulLeHaarStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftSmoothingProdExpSmoothCommuteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSobolevRepresentationProdExpStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
namespace GlobalTheory.DerivBoundIntegral
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
noncomputable def wordEnd (w : List 𝔤) : Module.End ℂ (h.smoothFuns (F := ℂ)) :=
  (w.map (h.rightDerivEnd (F := ℂ))).prod
end GlobalTheory.DerivBoundIntegral
namespace GlobalTheory
end GlobalTheory


