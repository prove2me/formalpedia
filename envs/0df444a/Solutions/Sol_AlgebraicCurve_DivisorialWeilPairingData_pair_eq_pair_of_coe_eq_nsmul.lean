-- Prove2me | solution 1 for AlgebraicCurve.DivisorialWeilPairingData.pair_eq_pair_of_coe_eq_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1ab85704-f65f-5fed-8efe-6fe8fbad517f

import Mathlib
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_DivisorialWeilPairingData_pair_eq_pair_of_coe_eq_nsmul
set_option autoImplicit false

open AlgebraicCurve

noncomputable section

section Aux

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private def towerDatumTop (m n : ℕ) (D₁ D₂ : Divisor K F) (f₁ g : F)
    (hf₁0 : f₁ ≠ 0) (hg0 : g ≠ 0)
    (hf₁ : ∀ v : Place K F, v.ord f₁ = ↑(m * n) * D₁ v)
    (hg : ∀ v : Place K F, v.ord g = ↑m * D₂ v)
    (hdisj : ∀ v : Place K F, D₁ v = 0 ∨ D₂ v = 0)
    (hrat : ∀ v : Place K F, D₁ v ≠ 0 ∨ D₂ v ≠ 0 → v.IsRational) :
    WeilDatum K F (m * n) where
  D₁ := D₁
  D₂ := D₂
  f₁ := f₁
  f₂ := g ^ (n : ℤ)
  f₁_ne_zero := hf₁0
  f₂_ne_zero := zpow_ne_zero _ hg0
  ord_f₁ := hf₁
  ord_f₂ := by
    intro v
    rw [v.ord_zpow, hg v]
    push_cast
    ring
  disjoint := hdisj
  rational := hrat

private def towerDatumBase (m n : ℕ) (D₁ D₂ : Divisor K F) (f₁ g : F)
    (hf₁0 : f₁ ≠ 0) (hg0 : g ≠ 0)
    (hf₁ : ∀ v : Place K F, v.ord f₁ = ↑(m * n) * D₁ v)
    (hg : ∀ v : Place K F, v.ord g = ↑m * D₂ v)
    (hdisj : ∀ v : Place K F, D₁ v = 0 ∨ D₂ v = 0)
    (hrat : ∀ v : Place K F, D₁ v ≠ 0 ∨ D₂ v ≠ 0 → v.IsRational) :
    WeilDatum K F m where
  D₁ := (n : ℤ) • D₁
  D₂ := D₂
  f₁ := f₁
  f₂ := g
  f₁_ne_zero := hf₁0
  f₂_ne_zero := hg0
  ord_f₁ := by
    intro v
    rw [hf₁ v, Finsupp.smul_apply, smul_eq_mul]
    push_cast
    ring
  ord_f₂ := hg
  disjoint := by
    intro v
    rcases hdisj v with h | h
    · exact Or.inl (by rw [Finsupp.smul_apply, smul_eq_mul, h, mul_zero])
    · exact Or.inr h
  rational := by
    intro v hv
    rcases hv with h1 | h2
    · refine hrat v (Or.inl fun h0 => h1 ?_)
      rw [Finsupp.smul_apply, smul_eq_mul, h0, mul_zero]
    · exact hrat v (Or.inr h2)

end Aux

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F]
    (m n : ℕ) [NeZero m] [NeZero (m * n)] [HasPrincipalDivisors K F]
    (e_mn : DivisorialWeilPairingData K F (m * n))
    (e_m : DivisorialWeilPairingData K F m)
    (x : Pic0.torsion K F (m * n)) (y : Pic0.torsion K F m)
    (y' : Pic0.torsion K F (m * n)) (hy : (y' : Pic0 K F) = (y : Pic0 K F))
    (x' : Pic0.torsion K F m) (hx : (x' : Pic0 K F) = (n : ℤ) • (x : Pic0 K F)) :
    e_mn.pair x y' = e_m.pair x' y := by
  classical
  obtain ⟨D₁, hD₁mk, hD₁rat, -⟩ := e_mn.move x ∅
  obtain ⟨D₂, hD₂mk, hD₂rat, hD₂avoid⟩ := e_m.move y (D₁ : Divisor K F).support
  obtain ⟨f₁, hf₁0, hf₁⟩ := DivisorialWeilPairingData.exists_witness x D₁ hD₁mk
  obtain ⟨g, hg0, hg⟩ := DivisorialWeilPairingData.exists_witness y D₂ hD₂mk
  have hdisj : ∀ v : Place K F, (D₁ : Divisor K F) v = 0 ∨ (D₂ : Divisor K F) v = 0 := by
    intro v
    by_cases hv : (D₂ : Divisor K F) v = 0
    · exact Or.inr hv
    · refine Or.inl ?_
      by_contra hv1
      exact hD₂avoid v (Finsupp.mem_support_iff.mpr hv) (Finsupp.mem_support_iff.mpr hv1)
  have hrat : ∀ v : Place K F,
      (D₁ : Divisor K F) v ≠ 0 ∨ (D₂ : Divisor K F) v ≠ 0 → v.IsRational := by
    intro v hv
    rcases hv with h1 | h2
    · exact hD₁rat v (Finsupp.mem_support_iff.mpr h1)
    · exact hD₂rat v (Finsupp.mem_support_iff.mpr h2)
  have hordg0 : ∀ v ∈ (D₁ : Divisor K F).support, Place.ord v g = 0 := by
    intro v hv
    have h2 : (D₂ : Divisor K F) v = 0 := by
      rcases hdisj v with h | h
      · exact absurd h (Finsupp.mem_support_iff.mp hv)
      · exact h
    rw [hg v, h2, mul_zero]
  have h1 := e_mn.compatible
    (towerDatumTop m n (D₁ : Divisor K F) (D₂ : Divisor K F) f₁ g hf₁0 hg0 hf₁ hg hdisj hrat)
  have h2 := e_m.compatible
    (towerDatumBase m n (D₁ : Divisor K F) (D₂ : Divisor K F) f₁ g hf₁0 hg0 hf₁ hg hdisj hrat)
  have hc1L : (towerDatumTop m n (D₁ : Divisor K F) (D₂ : Divisor K F) f₁ g
      hf₁0 hg0 hf₁ hg hdisj hrat).classLeft = x := by
    refine Subtype.ext ?_
    show Pic0.mk _ = (x : Pic0 K F)
    rw [← hD₁mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  have hc1R : (towerDatumTop m n (D₁ : Divisor K F) (D₂ : Divisor K F) f₁ g
      hf₁0 hg0 hf₁ hg hdisj hrat).classRight = y' := by
    refine Subtype.ext ?_
    show Pic0.mk _ = (y' : Pic0 K F)
    rw [hy, ← hD₂mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  have hc2L : (towerDatumBase m n (D₁ : Divisor K F) (D₂ : Divisor K F) f₁ g
      hf₁0 hg0 hf₁ hg hdisj hrat).classLeft = x' := by
    refine Subtype.ext ?_
    show Pic0.mk _ = (x' : Pic0 K F)
    rw [hx, ← hD₁mk]
    have hdz : (towerDatumBase m n (D₁ : Divisor K F) (D₂ : Divisor K F) f₁ g
        hf₁0 hg0 hf₁ hg hdisj hrat).degZeroLeft = (n : ℤ) • D₁ := Subtype.ext rfl
    rw [hdz]
    show QuotientAddGroup.mk ((n : ℤ) • D₁) = (n : ℤ) • (QuotientAddGroup.mk D₁)
    exact QuotientAddGroup.mk_zsmul
      ((Divisor.principal (K := K) (F := F)).addSubgroupOf
        (Divisor.degZero (K := K) (F := F))) D₁ (n : ℤ)
  have hc2R : (towerDatumBase m n (D₁ : Divisor K F) (D₂ : Divisor K F) f₁ g
      hf₁0 hg0 hf₁ hg hdisj hrat).classRight = y := by
    refine Subtype.ext ?_
    show Pic0.mk _ = (y : Pic0 K F)
    rw [← hD₂mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  rw [hc1L, hc1R] at h1
  rw [hc2L, hc2R] at h2
  rw [h1, h2]
  show Divisor.evalFun f₁ (D₂ : Divisor K F) / Divisor.evalFun (g ^ (n : ℤ)) (D₁ : Divisor K F)
      = Divisor.evalFun f₁ (D₂ : Divisor K F)
        / Divisor.evalFun g ((n : ℤ) • (D₁ : Divisor K F))
  rw [Divisor.evalFun_zpow_left_of_ord_eq_zero hg0 (n : ℤ) hD₁rat hordg0,
    Divisor.evalFun_zsmul_divisor]

end

end S_AlgebraicCurve_DivisorialWeilPairingData_pair_eq_pair_of_coe_eq_nsmul
end P2MW
export P2MW.S_AlgebraicCurve_DivisorialWeilPairingData_pair_eq_pair_of_coe_eq_nsmul (solution)
