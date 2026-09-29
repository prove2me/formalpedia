-- Prove2me | solution 1 for AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7d34e6b1-f520-5ec8-8ad5-a738bb62ab90

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F)
    (hSG : AlgebraicCurve.StichtenothGenusExists K F) :
    AlgebraicCurve.WeilDualityAdelic K F := by
  intro _instCurve _instCan _instDC ω hω D
  obtain ⟨⟨v⟩, hfd, γ, D₀, hγ⟩ := hSG
  haveI : Nonempty (Place K F) := ⟨v⟩
  haveI : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := hfd

  have hi : ∀ D' : Divisor K F,
      (indexOfSpecialty D' : ℤ) = (ell D' : ℤ) - (Divisor.degree D' + 1 - γ) :=
    fun D' => (indexOfSpecialty_eq_of_genusReached hγ D').2

  have hdegv : 0 < (v.deg : ℤ) := by
    haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank K v.ResidueField)

  have hγle : γ ≤ (genus K F : ℤ) := by
    have h₁ := hRR hω D₀
    have h₂ := hγ.eq
    have h₃ : (0 : ℤ) ≤ (ell (canonicalDivisorOf hω - D₀) : ℤ) := Nat.cast_nonneg _
    linarith

  have hgeγ : (genus K F : ℤ) ≤ γ := by
    set D₁ : Divisor K F := canonicalDivisorOf hω + Finsupp.single v 1 with hD₁
    have hKD : canonicalDivisorOf hω - D₁ = -Finsupp.single v 1 := by
      rw [hD₁]; abel
    have hneg : Divisor.degree (canonicalDivisorOf hω - D₁) < 0 := by
      rw [hKD, map_neg, Divisor.degree_single]
      linarith
    have hℓ : ell (canonicalDivisorOf hω - D₁) = 0 := ell_eq_zero_of_degree_neg hneg
    have h₁ := hRR hω D₁
    have h₂ := hγ.isMax D₁
    rw [hℓ] at h₁
    push_cast at h₁
    linarith
  have hγg : γ = (genus K F : ℤ) := le_antisymm hγle hgeγ
  have h₁ := hi D
  have h₂ := hRR hω D
  rw [hγg] at h₁
  linarith

end S_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
end P2MW
export P2MW.S_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists (solution)
