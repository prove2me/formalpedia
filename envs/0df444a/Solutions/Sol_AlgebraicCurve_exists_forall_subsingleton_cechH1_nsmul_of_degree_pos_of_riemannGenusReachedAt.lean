-- Prove2me | solution 1 for AlgebraicCurve.exists_forall_subsingleton_cechH1_nsmul_of_degree_pos_of_riemannGenusReachedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/c278e733-2e11-5efa-bf19-e71a5788fbba

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Theorems.Thm_AlgebraicCurve_cechRiemannRoch_of_genusReached
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_forall_subsingleton_cechH1_nsmul_of_degree_pos_of_riemannGenusReachedAt

set_option autoImplicit false

open AlgebraicCurve

namespace GenVan

theorem finrank_riemannRochSpace_add_eq {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D P : Divisor K F) (h : F) (hh : h ≠ 0) (hP : ∀ v : Place K F, P v = v.ord h) :
    Module.finrank K ↥(riemannRochSpace (D + P)) = Module.finrank K ↥(riemannRochSpace D) := by
  classical

  have hmem : ∀ g : F, g ∈ riemannRochSpace (D + P) → g * h ∈ riemannRochSpace D := by
    intro g hg
    rw [mem_riemannRochSpace_iff] at hg ⊢
    intro v
    rcases eq_or_ne g 0 with rfl | hg0
    · left; rw [zero_mul]
    · right
      rcases hg v with h0 | hv
      · exact absurd h0 hg0
      · rw [Place.ord_mul v hg0 hh, ← hP v]
        have : (D + P) v = D v + P v := Finsupp.add_apply _ _ _
        omega
  have hmem' : ∀ g : F, g ∈ riemannRochSpace D → g * h⁻¹ ∈ riemannRochSpace (D + P) := by
    intro g hg
    rw [mem_riemannRochSpace_iff] at hg ⊢
    intro v
    rcases eq_or_ne g 0 with rfl | hg0
    · left; rw [zero_mul]
    · right
      rcases hg v with h0 | hv
      · exact absurd h0 hg0
      · rw [Place.ord_mul v hg0 (inv_ne_zero hh), Place.ord_inv v, ← hP v]
        have : (D + P) v = D v + P v := Finsupp.add_apply _ _ _
        omega
  let e : ↥(riemannRochSpace (D + P)) ≃ₗ[K] ↥(riemannRochSpace D) :=
    { toFun := fun g => ⟨(g : F) * h, hmem g g.2⟩
      map_add' := fun a b => Subtype.ext (by push_cast; ring),
      map_smul' := fun c a => Subtype.ext (by simp [Algebra.smul_def, mul_assoc]),
      invFun := fun g => ⟨(g : F) * h⁻¹, hmem' g g.2⟩,
      left_inv := fun g => Subtype.ext (by simp [mul_assoc, mul_inv_cancel₀ hh]),
      right_inv := fun g => Subtype.ext (by simp [mul_assoc, inv_mul_cancel₀ hh]) }
  exact e.finrank_eq

end GenVan

open GenVan in
set_option maxHeartbeats 3200000 in
theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(riemannRochSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (hγ : RiemannGenusReachedAt γ D₀)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁)
    (D : Divisor K F) (hD : 0 < Divisor.degree D) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Subsingleton (cechH1 S₀ S₁ ((n : ℤ) • D)) := by

  classical

  refine ⟨(Divisor.degree D₀ + γ).toNat, fun n hn => ?_⟩
  haveI : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := ‹FiniteDimensional K ↥(riemannRochSpace (0 : Divisor K F))›
  have RR := fun E : Divisor K F => cechRiemannRoch_of_genusReached hγ hcover h₀ h₁ E
  set E : Divisor K F := (n : ℤ) • D with hE

  set X : Divisor K F := E - D₀ with hX
  have hdegE : Divisor.degree E = (n : ℤ) * Divisor.degree D := by rw [hE, map_zsmul, smul_eq_mul]
  have hdegX : Divisor.degree X = (n : ℤ) * Divisor.degree D - Divisor.degree D₀ := by rw [hX, map_sub, hdegE]
  have hn' : Divisor.degree D₀ + γ ≤ (n : ℤ) * Divisor.degree D := by
    have h1 : Divisor.degree D₀ + γ ≤ ((Divisor.degree D₀ + γ).toNat : ℤ) := Int.self_le_toNat _
    have h2 : ((Divisor.degree D₀ + γ).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    nlinarith
  have hellX : 1 ≤ (ell X : ℤ) := by
    have := hγ.isMax X
    rw [hdegX] at this
    omega
  have hXne : ∃ h : F, h ∈ riemannRochSpace X ∧ h ≠ 0 := by
    by_contra hno
    push Not at hno
    have hbot : riemannRochSpace X = ⊥ := by
      rw [Submodule.eq_bot_iff]; intro g hg; by_contra hg0; exact hg0 (hno g hg)
    have : ell X = 0 := by
      show Module.finrank K ↥(LSpace X) = 0
      rw [show LSpace X = riemannRochSpace X from rfl, hbot, finrank_bot]
    omega
  obtain ⟨h, hhX, hh0⟩ := hXne
  obtain ⟨P, hP, hPdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) h hh0

  set E' : Divisor K F := E + P with hE'
  have hle : D₀ ≤ E' := by
    intro v
    have hv := (mem_riemannRochSpace_iff.mp hhX) v
    rcases hv with h0 | hv
    · exact absurd h0 hh0
    · rw [hE', Finsupp.add_apply, hP v]
      have : X v = E v - D₀ v := by rw [hX]; exact Finsupp.sub_apply _ _ _
      omega

  obtain ⟨-, hfinE, hh0E, hh1E, hχE, -⟩ := RR E
  obtain ⟨-, hfinE', hh0E', hh1E', hχE', hvanE'⟩ := RR E'
  haveI := hfinE
  haveI := hfinE'
  have hsub : Subsingleton (cechH1 S₀ S₁ E') := hvanE' hle
  have hi' : Module.finrank K (cechH1 S₀ S₁ E') = 0 := Module.finrank_zero_of_subsingleton

  have hellEE' : ell E' = ell E := by
    show Module.finrank K ↥(riemannRochSpace (E + P)) = Module.finrank K ↥(riemannRochSpace E)
    exact finrank_riemannRochSpace_add_eq E P h hh0 hP
  have hdegE' : Divisor.degree E' = Divisor.degree E := by rw [hE', map_add, hPdeg, add_zero]
  have hiE : Module.finrank K (cechH1 S₀ S₁ E) = 0 := by
    have h1 := hχE; have h2 := hχE'
    rw [hh0E] at h1; rw [hh0E', hellEE', hdegE', hi'] at h2
    omega
  exact Module.finrank_zero_iff.mp hiE

end S_AlgebraicCurve_exists_forall_subsingleton_cechH1_nsmul_of_degree_pos_of_riemannGenusReachedAt
end P2MW
export P2MW.S_AlgebraicCurve_exists_forall_subsingleton_cechH1_nsmul_of_degree_pos_of_riemannGenusReachedAt (solution)
