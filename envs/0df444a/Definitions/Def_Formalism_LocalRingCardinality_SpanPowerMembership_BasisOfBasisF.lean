-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_BasisOfBasisF
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_BasisOfBasisF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:47.275648+00:00
-- url     : https://prove2.me/theorems/ef835eb8-dd92-43e6-b28b-cb050ab8b9fd
-- title:
--   Basis Of Basis F
-- statement:
--   Definitions and structural lemmas for Basis Of Basis F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/BasisOfBasisF.lean

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
namespace Formalism.BasicNotions.Examples₂.NZ
open scoped TensorProduct nonZeroDivisors
section Kap
variable (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
  [Algebra.IsIntegral A B]
theorem isFrac_tensor (hinj : Function.Injective (algebraMap A B)) :
    IsFractionRing B (B ⊗[A] FractionRing A) := by
  have h0 : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (B ⊗[A] FractionRing A) := inferInstance
  refine IsLocalization.of_le (Algebra.algebraMapSubmonoid B A⁰) B⁰ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha))
  · intro r hr
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    have hne := Ideal.comap_ne_bot_of_integral_mem (R := A) (I := Ideal.span {r}) hr0
      (Ideal.mem_span_singleton_self r) (Algebra.IsIntegral.isIntegral r)
    obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hd)
    have hu : IsUnit (algebraMap B (B ⊗[A] FractionRing A) (algebraMap A B d)) :=
      IsLocalization.map_units (M := Algebra.algebraMapSubmonoid B A⁰) _
        ⟨_, ⟨d, mem_nonZeroDivisors_of_ne_zero hd0, rfl⟩⟩
    rw [hs, map_mul] at hu
    exact isUnit_of_mul_isUnit_left hu
def kap (hinj : Function.Injective (algebraMap A B)) : (B ⊗[A] FractionRing A) ≃ₐ[B] FractionRing B :=
  haveI := isFrac_tensor A B hinj
  IsLocalization.algEquiv B⁰ _ _
variable (ι : Type) [Fintype ι] [DecidableEq ι]
def vecE (hinj : Function.Injective (algebraMap A B)) :
    (ι → FractionRing B) ≃ₗ[B] B ⊗[A] (ι → FractionRing A) :=
  (LinearEquiv.piCongrRight fun _ : ι => (kap A B hinj).symm.toLinearEquiv) ≪≫ₗ
    (TensorProduct.piRight A B B (fun _ : ι => FractionRing A)).symm
end Kap
end Formalism.BasicNotions.Examples₂.NZ


