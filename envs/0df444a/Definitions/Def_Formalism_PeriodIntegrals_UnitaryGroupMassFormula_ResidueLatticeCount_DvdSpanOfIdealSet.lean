-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_DvdSpanOfIdealSet
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_DvdSpanOfIdealSet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:29.241599+00:00
-- url     : https://prove2.me/theorems/c836b6d8-d304-43c4-a1b4-16430d6ce564
-- title:
--   Dvd Span Of Ideal Set
-- statement:
--   Definitions and structural lemmas for Dvd Span Of Ideal Set, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/DvdSpanOfIdealSet.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.Units
open scoped nonZeroDivisors ENNReal Classical
noncomputable section
namespace PI.Residue
variable {K : Type} [Field K] [NumberField K]
theorem dvd_span_of_idealSet (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) :
    (J : Ideal (𝓞 K)) ∣ Ideal.span {(preimageOfMemIntegerSet (idealSetMap K J x) : 𝓞 K)} := by
  rw [Ideal.dvd_span_singleton]
  exact preimage_of_IdealSetMap K J x
def cof (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) : Ideal (𝓞 K) :=
  (dvd_span_of_idealSet J x).choose
theorem cof_spec (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) :
    Ideal.span {(preimageOfMemIntegerSet (idealSetMap K J x) : 𝓞 K)} = (J : Ideal (𝓞 K)) * cof J x :=
  (dvd_span_of_idealSet J x).choose_spec
theorem cof_mem (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) : cof J x ∈ (Ideal (𝓞 K))⁰ := by
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h
  have h1 := cof_spec J x
  rw [h, mul_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h1
  exact nonZeroDivisors.coe_ne_zero _ h1
theorem cof_class (J : (Ideal (𝓞 K))⁰) (x : idealSet K J) (C : ClassGroup (𝓞 K))
    (hJ : ClassGroup.mk0 J = C⁻¹) : ClassGroup.mk0 ⟨cof J x, cof_mem J x⟩ = C := by
  have h1 : ClassGroup.mk0 (J * ⟨cof J x, cof_mem J x⟩) = 1 := by
    rw [ClassGroup.mk0_eq_one_iff]
    have : ((J * ⟨cof J x, cof_mem J x⟩ : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) =
        Ideal.span {(preimageOfMemIntegerSet (idealSetMap K J x) : 𝓞 K)} := (cof_spec J x).symm
    rw [this]
    exact ⟨⟨_, rfl⟩⟩
  rw [map_mul, hJ] at h1
  exact (inv_mul_eq_one.mp h1).symm
def toPair (J : (Ideal (𝓞 K))⁰) (C : ClassGroup (𝓞 K)) (hJ : ClassGroup.mk0 J = C⁻¹)
    (x : idealSet K J) : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = C} × torsion K :=
  (⟨⟨cof J x, cof_mem J x⟩, cof_class J x C hJ⟩, (integerSetEquiv K (idealSetMap K J x)).2)
end PI.Residue


