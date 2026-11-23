-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_MatVTransvection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:00:39.213793+00:00
-- url     : https://prove2.me/theorems/8eee4c96-e21b-43d2-aa7f-dce896909bc4
-- title:
--   Mat VTransvection
-- statement:
--   Definitions and structural lemmas for Mat VTransvection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/MatVTransvection.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_IdxSmulSubMap
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
section Gen
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
def matV {n : Type} [Fintype n] (Γ : Matrix n n K) : (n → V) →ₗ[K] (n → V) :=
  LinearMap.pi fun k => ∑ l, Γ k l • LinearMap.proj l
def latPow (n : Type) (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) (n → V) := Submodule.pi Set.univ fun _ : n => M
end Gen
end PI.Dv.TIW


