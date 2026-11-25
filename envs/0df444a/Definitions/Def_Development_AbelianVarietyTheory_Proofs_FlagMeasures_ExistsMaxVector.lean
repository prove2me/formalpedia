-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:05:48.932836+00:00
-- url     : https://prove2.me/theorems/754297e4-8cc1-40b0-8b57-d4b8d2ebb091
-- title:
--   Exists Max Vector
-- statement:
--   Definitions and structural lemmas for Exists Max Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
namespace GlobalTheory.MassOrth
section Abstract
variable {K V Γ : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
def biInt : Subring K where
  carrier := {k | v k ≤ 1 ∧ v (star k) ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    rintro a b ⟨a1, a2⟩ ⟨b1, b2⟩
    exact ⟨v.map_add_le a1 b1, by rw [star_add]; exact v.map_add_le a2 b2⟩
  mul_mem' := by
    rintro a b ⟨a1, a2⟩ ⟨b1, b2⟩
    exact ⟨by rw [map_mul]; exact mul_le_one' a1 b1,
      by rw [star_mul, map_mul]; exact mul_le_one' b2 a2⟩
  neg_mem' := by
    rintro a ⟨a1, a2⟩
    exact ⟨by simpa using a1, by simpa using a2⟩
end Abstract
section NumberField
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] [StarRing K]
noncomputable def starInt : 𝓞 K →+* 𝓞 K := RingOfIntegers.mapRingHom (starRingEnd K)
end NumberField
end GlobalTheory.MassOrth


