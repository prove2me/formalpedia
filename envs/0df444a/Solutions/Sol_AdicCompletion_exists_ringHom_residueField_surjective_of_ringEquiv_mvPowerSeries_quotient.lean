-- Prove2me | solution 1 for AdicCompletion.exists_ringHom_residueField_surjective_of_ringEquiv_mvPowerSeries_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/fb145c59-a7c7-5534-83e8-1c710fd14dc8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_exists_ringHom_residueField_surjective_of_ringEquiv_mvPowerSeries_quotient

set_option autoImplicit false

open IsLocalRing MvPowerSeries

theorem solution
    (B₀ : Type) [CommRing B₀] (𝔪₀ : Ideal B₀) [𝔪₀.IsMaximal]
    (W₀ : Type) [CommRing W₀] [IsLocalRing W₀]
    (g₀ : MvPowerSeries (Fin 2) W₀) (hg₀ : MvPowerSeries.constantCoeff g₀ ∈ maximalIdeal W₀)
    (e₀ : AdicCompletion 𝔪₀ B₀ ≃+* MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀}) :
    ∃ ρ : B₀ →+* ResidueField W₀,
      Function.Surjective ρ ∧ RingHom.ker ρ = 𝔪₀ ∧
      ∀ (b : B₀) (w : W₀),
        e₀ (algebraMap B₀ (AdicCompletion 𝔪₀ B₀) b) - Ideal.Quotient.mk (Ideal.span {g₀}) (C w) ∈
          (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1} ⊔
            (maximalIdeal W₀).map (C : W₀ →+* MvPowerSeries (Fin 2) W₀)).map
            (Ideal.Quotient.mk (Ideal.span {g₀})) →
        ρ b = residue W₀ w := by
  classical

  let π₀ : MvPowerSeries (Fin 2) W₀ →+* ResidueField W₀ := (residue W₀).comp (MvPowerSeries.constantCoeff : MvPowerSeries (Fin 2) W₀ →+* W₀)
  have hπ₀g : ∀ a ∈ Ideal.span {g₀}, π₀ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp only [π₀, RingHom.comp_apply, map_mul]
    rw [(residue_eq_zero_iff _).mpr hg₀, mul_zero]
  let π : MvPowerSeries (Fin 2) W₀ ⧸ Ideal.span {g₀} →+* ResidueField W₀ := Ideal.Quotient.lift _ π₀ hπ₀g
  have hπmk : ∀ F : MvPowerSeries (Fin 2) W₀, π (Ideal.Quotient.mk _ F) = residue W₀ (MvPowerSeries.constantCoeff F) :=
    fun F => rfl

  have hnonunit : ∀ z : AdicCompletion 𝔪₀ B₀, ¬ IsUnit z → π (e₀ z) = 0 := by
    intro z hz
    obtain ⟨F, hF⟩ := Ideal.Quotient.mk_surjective (e₀ z)
    have hF' : ¬ IsUnit F := by
      intro hu
      apply hz
      have : IsUnit (e₀ z) := by rw [← hF]; exact hu.map _
      simpa using this.map e₀.symm
    rw [← hF, hπmk, residue_eq_zero_iff]
    rw [MvPowerSeries.isUnit_iff_constantCoeff] at hF'
    exact (mem_maximalIdeal _).mpr hF'
  have hker1 : ∀ z : AdicCompletion 𝔪₀ B₀, AdicCompletion.evalOneₐ 𝔪₀ z = 0 → ¬ IsUnit z := by
    intro z hz hu
    have := hu.map (AdicCompletion.evalOneₐ 𝔪₀)
    rw [hz] at this
    exact not_isUnit_zero this

  let ρ : B₀ →+* ResidueField W₀ := (π.comp (e₀ : AdicCompletion 𝔪₀ B₀ →+* _)).comp (algebraMap B₀ _)
  have hρ : ∀ b : B₀, ρ b = π (e₀ (algebraMap B₀ (AdicCompletion 𝔪₀ B₀) b)) := fun b => rfl

  have hread : ∀ (b : B₀) (w : W₀),
      e₀ (algebraMap B₀ (AdicCompletion 𝔪₀ B₀) b) - Ideal.Quotient.mk (Ideal.span {g₀}) (C w) ∈
        (Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1} ⊔ (maximalIdeal W₀).map (C : W₀ →+* MvPowerSeries (Fin 2) W₀)).map
          (Ideal.Quotient.mk (Ideal.span {g₀})) → ρ b = residue W₀ w := by
    intro b w h
    have hzero : ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) W₀), X 1} ⊔ (maximalIdeal W₀).map (C : W₀ →+* MvPowerSeries (Fin 2) W₀)).map
        (Ideal.Quotient.mk (Ideal.span {g₀}))).map π = ⊥ := by
      rw [Ideal.map_map, eq_bot_iff, Ideal.map_le_iff_le_comap, sup_le_iff, Ideal.span_le, Ideal.map_le_iff_le_comap]
      constructor
      · rintro t ht
        simp only [SetLike.mem_coe, Ideal.mem_comap, Ideal.mem_bot, RingHom.comp_apply, hπmk]
        rcases ht with rfl | rfl <;> simp
      · intro m hm
        simp only [Ideal.mem_comap, Ideal.mem_bot, RingHom.comp_apply, hπmk, MvPowerSeries.constantCoeff_C,
          residue_eq_zero_iff]
        exact hm
    have := Ideal.mem_map_of_mem π h
    rw [hzero, Ideal.mem_bot, map_sub, hπmk, MvPowerSeries.constantCoeff_C] at this
    rw [hρ]
    exact sub_eq_zero.mp this
  refine ⟨ρ, ?_, ?_, hread⟩
  ·
    intro r
    obtain ⟨w, rfl⟩ := residue_surjective r
    let s := e₀.symm (Ideal.Quotient.mk (Ideal.span {g₀}) (C w))
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ 𝔪₀ s)
    refine ⟨b, ?_⟩
    have hy : π (e₀ (s - algebraMap B₀ _ b)) = 0 := by
      apply hnonunit
      apply hker1
      rw [map_sub, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        AdicCompletion.evalOneₐ_of, ← hb, sub_self]
    rw [map_sub, map_sub, sub_eq_zero] at hy
    rw [hρ, ← hy]
    simp [s, hπmk]
  ·
    symm
    refine Ideal.IsMaximal.eq_of_le inferInstance (RingHom.ker_ne_top ρ) fun b hb => ?_
    rw [RingHom.mem_ker, hρ]
    apply hnonunit
    apply hker1
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, AdicCompletion.evalOneₐ_of]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hb

end S_AdicCompletion_exists_ringHom_residueField_surjective_of_ringEquiv_mvPowerSeries_quotient
end P2MW
export P2MW.S_AdicCompletion_exists_ringHom_residueField_surjective_of_ringEquiv_mvPowerSeries_quotient (solution)
