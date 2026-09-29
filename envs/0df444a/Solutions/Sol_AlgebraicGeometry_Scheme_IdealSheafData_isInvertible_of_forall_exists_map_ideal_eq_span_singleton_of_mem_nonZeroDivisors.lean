-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_of_forall_exists_map_ideal_eq_span_singleton_of_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8a98a16d-39bb-55f7-9958-666ff0b7a48b

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_forall_exists_map_ideal_eq_span_singleton_of_mem_nonZeroDivisors

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace DICT

theorem exists_not_mem_forall_map_eq_span
    {A : Type*} [CommRing A] (J : Ideal A) (hJ : J.FG) (𝔭 : Ideal A) [𝔭.IsPrime] (g : A) (hg : g ∈ J)
    (hloc : J.map (algebraMap A (Localization.AtPrime 𝔭)) = Ideal.span {algebraMap A (Localization.AtPrime 𝔭) g}) :
    ∃ f : A, f ∉ 𝔭 ∧ ∀ (S : Type*) [CommRing S] [Algebra A S], IsUnit (algebraMap A S f) →
      J.map (algebraMap A S) = Ideal.span {algebraMap A S g} := by
  classical
  obtain ⟨s, hs⟩ := hJ
  have hx : ∀ x ∈ s, ∃ u : A, u ∉ 𝔭 ∧ ∃ c : A, u * x = c * g := by
    intro x hxs
    have hxJ : x ∈ J := hs ▸ Ideal.subset_span hxs
    have : algebraMap A (Localization.AtPrime 𝔭) x ∈ Ideal.span {algebraMap A (Localization.AtPrime 𝔭) g} :=
      hloc ▸ Ideal.mem_map_of_mem _ hxJ
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 this
    obtain ⟨⟨c, u⟩, hcu⟩ := IsLocalization.surj 𝔭.primeCompl q
    have h1 : algebraMap A (Localization.AtPrime 𝔭) (u * x) = algebraMap A (Localization.AtPrime 𝔭) (c * g) := by
      rw [map_mul, map_mul, ← hq, ← hcu]; ring
    obtain ⟨⟨v, hv⟩, hvx⟩ := (IsLocalization.eq_iff_exists 𝔭.primeCompl (Localization.AtPrime 𝔭)).1 h1
    refine ⟨v * u, 𝔭.primeCompl.mul_mem hv u.2, v * c, by simpa [mul_assoc, mul_comm, mul_left_comm] using hvx⟩
  choose! u hu c hc using hx
  refine ⟨∏ x ∈ s, u x, fun hmem => ?_, fun S _ _ hunit => ?_⟩
  · obtain ⟨x, hxs, hxp⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
    exact hu x hxs hxp
  · apply le_antisymm
    · rw [← hs, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨x, hxs, rfl⟩
      have hux : IsUnit (algebraMap A S (u x)) :=
        isUnit_of_dvd_unit (map_dvd (algebraMap A S) (Finset.dvd_prod_of_mem u hxs)) hunit
      obtain ⟨w, hw⟩ := hux
      have : algebraMap A S x = (↑w⁻¹ * algebraMap A S (c x)) * algebraMap A S g := by
        have h := congrArg (algebraMap A S) (hc x hxs)
        rw [map_mul, map_mul, ← hw] at h
        rw [mul_assoc, ← h, ← mul_assoc, Units.inv_mul, one_mul]
      rw [SetLike.mem_coe, this]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ hg

theorem exists_not_mem_forall_mem_nonZeroDivisors
    {A : Type*} [CommRing A] [IsNoetherianRing A] (𝔭 : Ideal A) [𝔭.IsPrime] (g : A)
    (hreg : algebraMap A (Localization.AtPrime 𝔭) g ∈ nonZeroDivisors (Localization.AtPrime 𝔭)) :
    ∃ f : A, f ∉ 𝔭 ∧ ∀ (S : Type*) [CommRing S] [Algebra A S] (M : Submonoid A) [IsLocalization M S],
      (∃ m ∈ M, f ∣ m) → algebraMap A S g ∈ nonZeroDivisors S := by
  classical

  set N : Ideal A := (Submodule.span A {g}).annihilator with hN
  obtain ⟨s, hs⟩ := Ideal.fg_of_isNoetherianRing N
  have hx : ∀ a ∈ s, ∃ u : A, u ∉ 𝔭 ∧ u * a = 0 := by
    intro a has
    have haN : a ∈ N := hs ▸ Ideal.subset_span has
    have hag : a * g = 0 := by
      have := (Submodule.mem_annihilator_span_singleton g a).1 haN
      simpa [smul_eq_mul] using this

    have h0 : algebraMap A (Localization.AtPrime 𝔭) a = 0 := by
      have : algebraMap A (Localization.AtPrime 𝔭) a * algebraMap A (Localization.AtPrime 𝔭) g = 0 := by
        rw [← map_mul, hag, map_zero]
      exact (mem_nonZeroDivisors_iff_right.1 hreg) _ this
    obtain ⟨⟨u, hu⟩, hua⟩ := (IsLocalization.map_eq_zero_iff 𝔭.primeCompl (Localization.AtPrime 𝔭) a).1 h0
    exact ⟨u, hu, hua⟩
  choose! u hu hua using hx
  refine ⟨∏ a ∈ s, u a, fun hmem => ?_, fun S _ _ M _ ⟨m, hmM, hfm⟩ => ?_⟩
  · obtain ⟨a, has, hap⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
    exact hu a has hap
  ·
    have hgen : ∀ a ∈ s, m * a = 0 := by
      intro a has
      obtain ⟨d, hd⟩ := hfm
      obtain ⟨e, he⟩ : u a ∣ ∏ a ∈ s, u a := Finset.dvd_prod_of_mem u has
      rw [hd, he]
      calc u a * e * d * a = (e * d) * (u a * a) := by ring
        _ = 0 := by rw [hua a has, mul_zero]
    have hmN : ∀ b ∈ N, m * b = 0 := by
      intro b hb
      rw [← hs] at hb
      induction hb using Submodule.span_induction with
      | mem a has => exact hgen a has
      | zero => simp
      | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
      | smul r x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]
    rw [mem_nonZeroDivisors_iff_right]
    intro z hz
    obtain ⟨⟨b, n⟩, hbn⟩ := IsLocalization.surj M z

    have hgb : algebraMap A S (b * g) = 0 := by
      rw [map_mul, ← hbn, mul_comm z, mul_assoc, hz, mul_zero]
    obtain ⟨⟨c, hc⟩, hcb⟩ := (IsLocalization.map_eq_zero_iff M S (b * g)).1 hgb
    have hcbN : c * b ∈ N := by
      refine (Submodule.mem_annihilator_span_singleton g (c * b)).2 ?_
      simp only [smul_eq_mul]
      rw [mul_assoc]; exact hcb
    have hmcb : (m * c) * b = 0 := by rw [mul_assoc]; exact hmN _ hcbN
    have hb0 : algebraMap A S b = 0 :=
      (IsLocalization.map_eq_zero_iff M S b).2 ⟨⟨m * c, M.mul_mem hmM hc⟩, hmcb⟩
    have : z * algebraMap A S n = 0 := by rw [hbn, hb0]
    exact (IsLocalization.map_units S n).mul_left_eq_zero.1 this

end DICT

theorem solution
    {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (h : ∀ x : X, ∃ (U : X.affineOpens) (hxU : x ∈ (U : X.Opens)) (g : Γ(X, U)), g ∈ I.ideal U ∧
      (I.ideal U).map (algebraMap Γ(X, U) (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal)) =
        Ideal.span {algebraMap Γ(X, U) (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal) g} ∧
      algebraMap Γ(X, U) (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal) g ∈
        nonZeroDivisors (Localization.AtPrime (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal)) :
    I.IsInvertible := by
  classical
  intro x
  obtain ⟨U, hxU, g, hgJ, hloc, hreg⟩ := h x
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  set 𝔭 := U.2.primeIdealOf ⟨x, hxU⟩ with h𝔭
  obtain ⟨f₁, hf₁, hB⟩ := DICT.exists_not_mem_forall_map_eq_span (I.ideal U) (Ideal.fg_of_isNoetherianRing _) 𝔭.asIdeal g hgJ hloc
  obtain ⟨f₂, hf₂, hC⟩ := DICT.exists_not_mem_forall_mem_nonZeroDivisors 𝔭.asIdeal g hreg
  have hf : f₁ * f₂ ∉ 𝔭.asIdeal := fun hm => (𝔭.2.mem_or_mem hm).elim hf₁ hf₂

  have hxD : x ∈ X.basicOpen (f₁ * f₂) := by
    have h1 : 𝔭 ∈ PrimeSpectrum.basicOpen (f₁ * f₂) := hf
    have h2 : U.2.fromSpec 𝔭 ∈ X.basicOpen (f₁ * f₂) := by
      rw [← U.2.fromSpec_image_basicOpen]
      exact ⟨𝔭, h1, rfl⟩
    rwa [h𝔭, U.2.fromSpec_primeIdealOf ⟨x, hxU⟩] at h2
  haveI hAway : IsLocalization.Away (f₁ * f₂) Γ(X, X.basicOpen (f₁ * f₂)) := U.2.isLocalization_basicOpen (f₁ * f₂)
  refine ⟨U, f₁ * f₂, hxD, algebraMap Γ(X, U) Γ(X, X.basicOpen (f₁ * f₂)) g, ?_, ?_⟩
  ·
    exact hC Γ(X, X.basicOpen (f₁ * f₂)) (Submonoid.powers (f₁ * f₂)) ⟨f₁ * f₂, Submonoid.mem_powers _, dvd_mul_left f₂ f₁⟩
  ·
    have hunit : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen (f₁ * f₂)) f₁) :=
      isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right f₁ f₂)) (IsLocalization.Away.algebraMap_isUnit (f₁ * f₂))
    have hB' := hB Γ(X, X.basicOpen (f₁ * f₂)) hunit
    rw [← I.map_ideal_basicOpen U (f₁ * f₂)]
    exact hB'

end S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_forall_exists_map_ideal_eq_span_singleton_of_mem_nonZeroDivisors
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_forall_exists_map_ideal_eq_span_singleton_of_mem_nonZeroDivisors (solution)
