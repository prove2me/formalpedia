-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_BochnerG2_NcVOneDecomp
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_BochnerG2_NcVOneDecomp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:13:15.15603+00:00
-- url     : https://prove2.me/theorems/9f29d51c-b0a9-4655-8ac4-a2db46f342b1
-- title:
--   Nc VOne Decomp
-- statement:
--   Definitions and structural lemmas for Nc VOne Decomp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/ExceptionalGroupG2/BochnerG2/NcVOneDecomp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_StdGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_BochnerG2_CrossOpEigGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_ExceptionalGroupG2_BochnerG2_Numerics
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}
section OneB
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}
end OneB
end ReciprocityTheory.ChartRestriction.DS.G2


