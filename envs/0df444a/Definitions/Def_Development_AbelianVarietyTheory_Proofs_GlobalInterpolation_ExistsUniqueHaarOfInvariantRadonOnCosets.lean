-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsUniqueHaarOfInvariantRadonOnCosets
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:33.947205+00:00
-- url     : https://prove2.me/theorems/490bd63d-bac1-4b8a-9895-2fe1cbaade11
-- title:
--   Exists Unique Haar Of Invariant Radon On Cosets
-- statement:
--   Definitions and structural lemmas for Exists Unique Haar Of Invariant Radon On Cosets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsUniqueHaarOfInvariantRadonOnCosets.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_InvariantRadonFibre
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_InvariantRadonFibre_fibreIntegral_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.fibreIntegral_mk


set_option autoImplicit false
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal Pointwise
namespace GlobalTheory.QuotientHaar
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
theorem measurable_translate (g : G) : Measurable (fun h : H => g * (h : G)) :=
  (continuous_const.mul continuous_subtype_val).measurable
noncomputable def cosetMeasure (ν : Measure H) [ν.IsMulLeftInvariant] : G ⧸ H → Measure G :=
  Quotient.lift (fun g : G => ν.map (fun h : H => g * (h : G))) (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have h1 := map_mul_left_eq_self ν (⟨a⁻¹ * b, hab'⟩ : H)
    beta_reduce
    conv_lhs => rw [← h1]
    rw [Measure.map_map (measurable_translate H a) (measurable_const_mul _)]
    congr 1
    funext h
    simp [← mul_assoc])
variable [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
end GlobalTheory.QuotientHaar
namespace GlobalTheory.QuotientHaar
end GlobalTheory.QuotientHaar


