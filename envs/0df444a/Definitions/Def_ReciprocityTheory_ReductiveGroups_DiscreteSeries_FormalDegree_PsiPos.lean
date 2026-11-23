-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_PsiPos
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_PsiPos
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:19:57.405794+00:00
-- url     : https://prove2.me/theorems/797157e7-a537-4a38-96e8-4c46f904349b
-- title:
--   Psi Pos
-- statement:
--   Definitions and structural lemmas for Psi Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/PsiPos.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_KinstSecondCountable
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexOrder InnerProductSpace
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section PsiPosAux
open S7
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
end PsiPosAux
end ReciprocityTheory.ChartRestriction.DS


