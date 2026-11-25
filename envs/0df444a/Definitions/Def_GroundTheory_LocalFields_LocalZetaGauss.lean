-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
-- name    : GroundTheory_LocalFields_LocalZetaGauss
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T10:16:35.120474+00:00
-- url     : https://prove2.me/theorems/470e727c-d6b7-50ce-9fde-ad2abcd164c2
-- title:
--   Local Zeta Gauss
-- statement:
--   Definitions and structural lemmas for Local Zeta Gauss, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaGauss.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Theorems.Thm_GroundTheory_LocalField_isCompact_unitFiltrationUnits_zero
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
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
section Quotient
variable (K) in

abbrev unitsModFiltration (c : ℕ) : Type _ :=
  unitFiltrationUnits K 0 ⧸ (unitFiltrationUnits K c).subgroupOf (unitFiltrationUnits K 0)
instance finite_unitsModFiltration (c : ℕ) : Finite (unitsModFiltration K c) := by
  have : CompactSpace (unitFiltrationUnits K 0) :=
    isCompact_iff_compactSpace.mp isCompact_unitFiltrationUnits_zero
  refine Subgroup.quotient_finite_of_isOpen _ ?_
  rw [Subgroup.coe_subgroupOf]
  exact (isOpen_unitFiltrationUnits c).preimage continuous_subtype_val
noncomputable instance fintype_unitsModFiltration (c : ℕ) : Fintype (unitsModFiltration K c) :=
  Fintype.ofFinite _
def unitsModRep {c : ℕ} (t : unitsModFiltration K c) : Kˣ :=
  ((Quotient.out t : unitFiltrationUnits K 0) : Kˣ)
def unitsModCoset {c : ℕ} (t : unitsModFiltration K c) : Set Kˣ :=
  (fun x => (unitsModRep t)⁻¹ * x) ⁻¹' (unitFiltrationUnits K c : Set Kˣ)
end Quotient
variable [MeasurableSpace K] [BorelSpace K]
section Integral
end Integral
section Gauss
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}
variable (χ ψ) in

def gaussSum : ℂ :=
  ∑ t : unitsModFiltration K (quasiCharConductor χ),
    ((χ (unifUnit K ^ (addCharConductor ψ - quasiCharConductor χ) * unitsModRep t) : ℂˣ) : ℂ)⁻¹ *
      (ψ ((unifUnit K ^ (addCharConductor ψ - quasiCharConductor χ) * unitsModRep t : Kˣ) : K) : ℂ)
end Gauss
end GroundTheory.LocalField


