-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Transported
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Transported
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:02:34.412816+00:00
-- url     : https://prove2.me/theorems/0a3d1c4c-3cf5-4f0f-bace-12b4298deeb0
-- title:
--   Transported
-- statement:
--   Definitions and structural lemmas for Transported, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Transported.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
def thrStar (ε : Fin n → Bool) : ℝ :=
  max ((n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1)
    (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))
end ReciprocityTheory.ChartRestriction.DS


