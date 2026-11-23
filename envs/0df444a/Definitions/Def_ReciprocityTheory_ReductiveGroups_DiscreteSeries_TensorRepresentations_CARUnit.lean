-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CARUnit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:18.652928+00:00
-- url     : https://prove2.me/theorems/7ec7a31d-de4b-434d-949e-db1711c523e5
-- title:
--   CARUnit
-- statement:
--   Definitions and structural lemmas for CARUnit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CARUnit.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CsqDdPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
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
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
def carUPos (ε : Fin n → Bool) (a : Fin n) : ℕ :=
  (if ε a then 0 else pOf ε) + (univ.filter fun b => b < a ∧ ε b = ε a).card
section Unitary
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
end Unitary
section Value
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
end Value
end ReciprocityTheory.ChartRestriction.DS


