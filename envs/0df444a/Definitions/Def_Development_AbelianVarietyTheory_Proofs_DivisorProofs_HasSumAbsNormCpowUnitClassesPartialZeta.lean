-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumAbsNormCpowUnitClassesPartialZeta
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumAbsNormCpowUnitClassesPartialZeta
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:05.414807+00:00
-- url     : https://prove2.me/theorems/dc1ed638-d95b-4411-9c53-56a6ee4ac5a4
-- title:
--   Has Sum Abs Norm Cpow Unit Classes Partial Zeta
-- statement:
--   Definitions and structural lemmas for Has Sum Abs Norm Cpow Unit Classes Partial Zeta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumAbsNormCpowUnitClassesPartialZeta.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
namespace GlobalTheory.PartialZetaSum
variable {F : Type} [Field F] [NumberField F]
theorem exists_ideal (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    ∃ J : Ideal (𝓞 F), (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 * ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) := by
  rw [← FractionalIdeal.le_one_iff_exists_coeIdeal]
  calc FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 * ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F)
      ≤ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) * ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) :=
        mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.2 b.2.1) _
    _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
def idealOf (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) : Ideal (𝓞 F) := (exists_ideal 𝔟 b).choose
theorem idealOf_coe (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    (idealOf 𝔟 b : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 * ((𝔟⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) :=
  (exists_ideal 𝔟 b).choose_spec
theorem span_eq (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) :
    FractionalIdeal.spanSingleton (𝓞 F)⁰ b.1 = (idealOf 𝔟 b : FractionalIdeal (𝓞 F)⁰ F) * (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
  rw [idealOf_coe, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
theorem idealOf_mem (𝔟 : Frac F) (b : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) : idealOf 𝔟 b ∈ (Ideal (𝓞 F))⁰ := by
  apply mem_nonZeroDivisors_of_ne_zero
  intro h
  have h1 := span_eq 𝔟 b
  rw [h] at h1
  simp at h1
  exact b.2.2 (FractionalIdeal.spanSingleton_eq_zero_iff.1 h1)
end GlobalTheory.PartialZetaSum


