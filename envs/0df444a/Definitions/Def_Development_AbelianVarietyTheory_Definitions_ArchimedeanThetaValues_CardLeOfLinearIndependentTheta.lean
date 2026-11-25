-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CardLeOfLinearIndependentTheta
-- name    : Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CardLeOfLinearIndependentTheta
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T23:51:59.022832+00:00
-- url     : https://prove2.me/theorems/9643b815-7d9c-4aad-b440-25a5b1dc6464
-- title:
--   Card Le Of Linear Independent Theta
-- statement:
--   Definitions and structural lemmas for Card Le Of Linear Independent Theta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/CardLeOfLinearIndependentTheta.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependentThetaPrincipal
import Theorems.Thm_GlobalTheory_AnArc_H_smul_left
import Theorems.Thm_GlobalTheory_AnArc_ah_add
import Theorems.Thm_GlobalTheory_ClassicalTheta_card_le_pow_of_linearIndependent
import Theorems.Thm_GlobalTheory_SiegelNormalForm_exists_normal_form
import Theorems.Thm_GlobalTheory_card_le_pow_of_linearIndependent_theta_principal
import Theorems.Thm_GlobalTheory_entire_periodic_eq_zero_of_fourierCoeff_eq_zero
import Theorems.Thm_GlobalTheory_fourierCoeff_unitCube_translate_of_entire_periodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
theorem translate_div_mem_Theta {j : ℕ} [NeZero j] {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) :
    (fun z => th (z - (j : ℂ)⁻¹ • A.ct α)) ∈ A.Theta j 0 :=
  ⟨h.1.comp (differentiable_id.sub_const _), fun l z => by
    have hj : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne j)
    have h1 := A.ah_add l (z - (j : ℂ)⁻¹ • A.ct α) ((j : ℂ)⁻¹ • A.ct α)
    rw [sub_add_cancel, H_smul_left] at h1
    show th (z + l - (j : ℂ)⁻¹ • A.ct α) = _ * _ * th (z - (j : ℂ)⁻¹ • A.ct α)
    rw [add_sub_right_comm, h.2, h1, mul_pow, ← Complex.exp_nat_mul, map_zero, H_zero_left, mul_zero,
      Complex.exp_zero, mul_one]
    congr 3
    field_simp⟩
theorem card_le_of_linearIndependent_Theta (j : ℕ) [NeZero j] (α : A.X) {N : ℕ} (f : Fin N → A.Theta j α)
    (hf : LinearIndependent ℂ f) : N ≤ j ^ A.gB := by
  refine card_le_pow_of_linearIndependent_theta_principal SiegelNormalForm.exists_normal_form
    (ClassicalTheta.card_le_pow_of_linearIndependent fourierCoeff_unitCube_translate_of_entire_periodic
      (entire_periodic_eq_zero_of_fourierCoeff_eq_zero fourierCoeff_unitCube_translate_of_entire_periodic))
    A.gB A.abelian₂ A.discrete A.full A.Hm A.chi A.Ef A.Hm_herm A.Hm_pos
    A.chi_norm A.Ef_eq A.Ef_bij j (Nat.pos_of_ne_zero (NeZero.ne j)) N
    (fun k z => (f k).1 (z - (j : ℂ)⁻¹ • A.ct α)) (fun k => ?_) ?_
  · obtain ⟨h1, h2⟩ := A.translate_div_mem_Theta (f k).2
    refine ⟨h1, fun l z => ?_⟩
    have := h2 l z
    rw [map_zero, H_zero_left, mul_zero, Complex.exp_zero, mul_one] at this
    exact this
  · exact (hf.map' (A.Theta j α).subtype (Submodule.ker_subtype _)).map'
      (LinearMap.funLeft ℂ ℂ fun z => z - (j : ℂ)⁻¹ • A.ct α)
      (LinearMap.ker_eq_bot.2 (LinearMap.funLeft_injective_of_surjective ℂ ℂ _ (Equiv.subRight _).surjective))
theorem rank_Theta_le (j : ℕ) [NeZero j] (α : A.X) : Module.rank ℂ (A.Theta j α) ≤ (j ^ A.gB : ℕ) :=
  rank_le fun s hs => A.card_le_of_linearIndependent_Theta j α (fun k => (s.equivFin.symm k).1)
    (hs.comp _ s.equivFin.symm.injective)
instance finiteDimensional_Theta (j : ℕ) [NeZero j] (α : A.X) : FiniteDimensional ℂ (A.Theta j α) :=
  Module.rank_lt_aleph0_iff.1 ((A.rank_Theta_le j α).trans_lt (Cardinal.natCast_lt_aleph0))
end GlobalTheory.AnArc


