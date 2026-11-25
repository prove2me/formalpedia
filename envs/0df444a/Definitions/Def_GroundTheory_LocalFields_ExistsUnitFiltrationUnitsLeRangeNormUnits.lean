-- Prove2me | Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
-- name    : GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:36:48.282379+00:00
-- url     : https://prove2.me/theorems/0cc95b92-f381-4ac3-b3b3-a1a2f4516fb4
-- title:
--   Exists Unit Filtration Units Le Range Norm Units
-- statement:
--   Definitions and structural lemmas for Exists Unit Filtration Units Le Range Norm Units, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeRangeNormUnits.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Theorems.Thm_GroundTheory_LocalField_isCompact_unitFiltrationUnits
import Theorems.Thm_GroundTheory_LocalField_isOpen_unitFiltrationUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter Polynomial
open scoped WithZero nonZeroDivisors
section Fields
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
def normUnits : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K : L →* K)
end Fields
section Ord
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (K) in

instance locallyCompactSpace_units : LocallyCompactSpace Kˣ :=
  (isCompact_unitFiltrationUnits 0).locallyCompactSpace_of_mem_nhds_of_group
    ((isOpen_unitFiltrationUnits 0).mem_nhds (Subgroup.one_mem _))
end Ord
section Local
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
variable (K L) in

def normIntegerUnits : 𝒪[L]ˣ →* 𝒪[K]ˣ :=
  Units.map (Algebra.norm 𝒪[K] : 𝒪[L] →* 𝒪[K])
section Valuation
end Valuation
section Topology
variable (K L)
end Topology
section Separable
variable [Algebra.IsSeparable K L]
end Separable
end Local
end GroundTheory.LocalField


