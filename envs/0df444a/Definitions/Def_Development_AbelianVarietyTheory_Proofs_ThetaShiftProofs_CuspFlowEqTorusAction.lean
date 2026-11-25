-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CuspFlowEqTorusAction
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CuspFlowEqTorusAction
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:33:37.970801+00:00
-- url     : https://prove2.me/theorems/d19e2176-2d01-4498-84f1-ed18b3e3644a
-- title:
--   Cusp Flow Eq Torus Action
-- statement:
--   Definitions and structural lemmas for Cusp Flow Eq Torus Action, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CuspFlowEqTorusAction.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsSt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
open scoped ComplexConjugate
namespace GlobalTheory.CuspFlow
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
end GlobalTheory.CuspFlow


