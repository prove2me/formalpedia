-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:51.458567+00:00
-- url     : https://prove2.me/theorems/92cae12f-a2f2-42e2-b2ca-77ad567ade6b
-- title:
--   Idx Smul Sub Map
-- statement:
--   Definitions and structural lemmas for Idx Smul Sub Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/IdxSmulSubMap.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxNonnegOfLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_FinsumEqLogNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv.TIW
open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv
section Vals
variable {K : Type} [Field K] [NumberField K]
end Vals
section Gen
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
def smulSub (d : K) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) V :=
  L.map ((d • LinearMap.id : V →ₗ[K] V).restrictScalars (𝓞 K))
end Gen
end PI.Dv.TIW


