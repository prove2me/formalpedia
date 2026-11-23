-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_ExistsHaarOfSubgroup
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_ExistsHaarOfSubgroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:54:51.587872+00:00
-- url     : https://prove2.me/theorems/3cd1e3ae-9fff-449f-b878-726a24c2f1a2
-- title:
--   Exists Haar Of Subgroup
-- statement:
--   Definitions and structural lemmas for Exists Haar Of Subgroup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/ExistsHaarOfSubgroup.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel MeasureTheory Topology Polynomial
namespace PI.LocHaarRRW
section General
variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V]
end General
section Field
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
end Field
section Lin
variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  {M V : Type*} [AddCommGroup M] [Module K M] [TopologicalSpace M] [IsModuleTopology K M]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsModuleTopology K V]
def homeoOfLin (e : M ≃ₗ[K] V) : M ≃ₜ V :=
  haveI := IsModuleTopology.toContinuousAdd K V
  haveI := IsModuleTopology.toContinuousAdd K M
  { toEquiv := e.toEquiv
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
end Lin
section Alg
variable {K V : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] [CommRing V] [Algebra K V]
end Alg
end PI.LocHaarRRW


