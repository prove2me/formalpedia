-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitNorm
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:42.678506+00:00
-- url     : https://prove2.me/theorems/570ba20f-4d5e-41a6-bea1-e7a70d742532
-- title:
--   Exists Unit Norm
-- statement:
--   Definitions and structural lemmas for Exists Unit Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsUnitNorm.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitPairNorm
open Module
section Generic
variable {O E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E]
  [Algebra O E] [IsFractionRing O E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
end Generic
end GlobalTheory.UnitPairNorm
namespace GlobalTheory.UnitPairNorm
open Module
section Main
variable {O E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E]
  [Algebra O E] [IsFractionRing O E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
  [FiniteDimensional E V]
end Main
end GlobalTheory.UnitPairNorm


