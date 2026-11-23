-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportA
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:07.200801+00:00
-- url     : https://prove2.me/theorems/05415282-fbca-4bbc-8778-215c37677441
-- title:
--   Transport A
-- statement:
--   Definitions and structural lemmas for Transport A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/TransportA.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_TransportDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ValuativeRel Function Filter Topology
section
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
end
section
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
end
section
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
  (p : ℕ) [Fact p.Prime]
noncomputable def transportRatHom (K : Type) [Field K] [CharZero K] : WithVal (Rat.padicValuation p) →+* K :=
  (algebraMap ℚ K).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom
end
section
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {p : ℕ} [Fact p.Prime]
end
section
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
end
end ReciprocityTheory.DiscreteGroups.LocalClassField


