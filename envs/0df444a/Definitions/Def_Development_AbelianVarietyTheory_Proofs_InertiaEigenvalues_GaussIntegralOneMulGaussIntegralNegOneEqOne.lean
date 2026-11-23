-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaussIntegralOneMulGaussIntegralNegOneEqOne
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaussIntegralOneMulGaussIntegralNegOneEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:54:28.69112+00:00
-- url     : https://prove2.me/theorems/bdba73b9-56f7-46a6-b51c-45619df85d61
-- title:
--   Gauss Integral One Mul Gauss Integral Neg One Eq One
-- statement:
--   Definitions and structural lemmas for Gauss Integral One Mul Gauss Integral Neg One Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaussIntegralOneMulGaussIntegralNegOneEqOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilFourierPreservesTestAdditive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.WeilQuad.GaussProd
open GlobalTheory.JR.WeilQuad.FourierTest
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
end GlobalTheory.JR.WeilQuad.GaussProd


