-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HermitianMatrixRealizesCuspCoords
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HermitianMatrixRealizesCuspCoords
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T01:42:28.584424+00:00
-- url     : https://prove2.me/theorems/1ec4280b-308f-4bfb-99c3-81594f5a51dd
-- title:
--   Hermitian Matrix Realizes Cusp Coords
-- statement:
--   Definitions and structural lemmas for Hermitian Matrix Realizes Cusp Coords, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/HermitianMatrixRealizesCuspCoords.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsSt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TraceEqSumRingHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
open scoped ComplexConjugate
namespace GlobalTheory.HermExpo
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
end GlobalTheory.HermExpo


