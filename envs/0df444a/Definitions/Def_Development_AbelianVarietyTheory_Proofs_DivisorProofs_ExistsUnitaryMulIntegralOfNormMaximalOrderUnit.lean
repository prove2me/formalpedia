-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnit
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnit
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:42.656034+00:00
-- url     : https://prove2.me/theorems/caa5d3ef-f7ba-4639-976c-b03d4e2299b4
-- title:
--   Exists Unitary Mul Integral Of Norm Maximal Order Unit
-- statement:
--   Definitions and structural lemmas for Exists Unitary Mul Integral Of Norm Maximal Order Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryMulIntegralOfNormMaximalOrderUnit.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Matrix GlobalTheory.LatOrb
namespace GlobalTheory.UnitAdj
section Residues
variable {A : Type} [CommRing A] [IsArtinianRing A] [IsReduced A]
end Residues
end GlobalTheory.UnitAdj


