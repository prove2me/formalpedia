-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftInvariantVectorFieldsExpCoordsSmoothFrame
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftInvariantVectorFieldsExpCoordsSmoothFrame
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:33.104462+00:00
-- url     : https://prove2.me/theorems/5bba0a4d-98b9-4a0e-8f8c-7aed82c6a292
-- title:
--   Left Invariant Vector Fields Exp Coords Smooth Frame
-- statement:
--   Definitions and structural lemmas for Left Invariant Vector Fields Exp Coords Smooth Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftInvariantVectorFieldsExpCoordsSmoothFrame.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
namespace GlobalTheory.ExpCoordFrame
open NormedSpace Filter Topology
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} {d : ℕ}
local notation "𝔢" => expPartialHomeomorph ℝ 𝔸
noncomputable def psi (b : Module.Basis (Fin d) ℝ 𝔤) (x : E d) (Y : 𝔤) : E d :=
  (coordEquiv b).symm (subspaceProj 𝔤 ((𝔢).symm (exp ((coordEquiv b x : 𝔤) : 𝔸) * exp (Y : 𝔸))))
end GlobalTheory.ExpCoordFrame
namespace GlobalTheory.ExpCoordFrame
open NormedSpace Filter Topology
end GlobalTheory.ExpCoordFrame


