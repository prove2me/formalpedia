-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_vanishingIdeal_closure_of_isRegularLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/08ff14ac-84db-5339-a25a-6d7cf529e1b7

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_IsRegularLocalRing_isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two
import Theorems.Thm_IsRegularLocalRing_isDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_vanishingIdeal_closure_of_isRegularLocalRing

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_vanishingIdeal_closure_of_isRegularLocalRing.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian Spec Scheme Scheme.IdealSheafData.vanishingIdeal Scheme.mem_zeroLocus_iff IsLocallyNoetherian.component_noetherian IsAffineOpen IsAffineOpen.fromSpec_primeIdealOf Scheme.IdealSheafData"
namespace CompInv
p2m_open "AlgebraicGeometry"

theorem exists_notMem_and_map_eq_span_singleton {A : Type u} [CommRing A] [IsNoetherianRing A]
    (𝔭 : Ideal A) [𝔭.IsPrime] (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.AtPrime S 𝔭]
    (𝔮 : Ideal A) (γ : S) (hγ : 𝔮.map (algebraMap A S) = Ideal.span {γ}) (hγ0 : γ ∈ nonZeroDivisors S) :
    ∃ f : A, f ∉ 𝔭 ∧ ∃ g : A, g ∈ 𝔮 ∧ ∀ (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away f B],
      𝔮.map (algebraMap A B) = Ideal.span {algebraMap A B g} ∧ algebraMap A B g ∈ nonZeroDivisors B := by
  classical

  have hγmem : γ ∈ 𝔮.map (algebraMap A S) := hγ ▸ Ideal.mem_span_singleton_self γ
  obtain ⟨⟨⟨g, hg𝔮⟩, ⟨s, hs⟩⟩, hgs⟩ := (IsLocalization.mem_map_algebraMap_iff 𝔭.primeCompl S).mp hγmem
  simp only at hgs

  have hsu : IsUnit (algebraMap A S s) := IsLocalization.map_units S ⟨s, hs⟩
  have hspan : Ideal.span {algebraMap A S g} = Ideal.span {γ} := by
    rw [← hgs]
    exact Ideal.span_singleton_mul_right_unit hsu γ
  have hg0 : algebraMap A S g ∈ nonZeroDivisors S := by
    rw [← hgs]; exact mul_mem hγ0 hsu.mem_nonZeroDivisors
  have h𝔮S : 𝔮.map (algebraMap A S) = Ideal.span {algebraMap A S g} := hγ.trans hspan.symm

  have hdiv : ∀ h ∈ 𝔮, ∃ u ∈ 𝔭.primeCompl, ∃ a : A, u * h = a * g := by
    intro h hh
    have h1 : algebraMap A S h ∈ Ideal.span {algebraMap A S g} := h𝔮S ▸ Ideal.mem_map_of_mem _ hh
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
    obtain ⟨⟨a, ⟨t, ht⟩⟩, hat⟩ := IsLocalization.surj 𝔭.primeCompl c
    simp only at hat

    have h2 : algebraMap A S (h * t) = algebraMap A S (a * g) := by
      rw [map_mul, map_mul, ← hc, ← hat]; ring
    obtain ⟨⟨v, hv⟩, hv'⟩ := (IsLocalization.eq_iff_exists 𝔭.primeCompl S).mp h2
    simp only at hv'
    exact ⟨v * t, mul_mem hv ht, v * a, by
      calc v * t * h = v * (h * t) := by ring
        _ = v * (a * g) := hv'
        _ = v * a * g := by ring⟩

  obtain ⟨T, hT⟩ := (isNoetherianRing_iff_ideal_fg A).mp inferInstance 𝔮
  choose! u hu a ha using hdiv
  let N : Ideal A := LinearMap.ker (LinearMap.mulRight A g)
  have hN : ∀ n : A, n ∈ N ↔ n * g = 0 := fun n => LinearMap.mem_ker
  obtain ⟨T', hT'⟩ := (isNoetherianRing_iff_ideal_fg A).mp inferInstance N
  have hann : ∀ n ∈ N, ∃ v ∈ 𝔭.primeCompl, v * n = 0 := by
    intro n hn
    have h1 : algebraMap A S n * algebraMap A S g = 0 := by rw [← map_mul, (hN n).mp hn, map_zero]
    have h2 : algebraMap A S n = 0 := (mem_nonZeroDivisors_iff_right.mp hg0) _ h1
    obtain ⟨⟨v, hv⟩, hvn⟩ := (IsLocalization.map_eq_zero_iff 𝔭.primeCompl S n).mp h2
    exact ⟨v, hv, hvn⟩
  choose! v hv hvn using hann

  let f₁ : A := ∏ h ∈ T, u h
  let f₂ : A := ∏ n ∈ T', v n
  have hTsub : ∀ h ∈ T, h ∈ 𝔮 := fun h hh => hT ▸ Ideal.subset_span hh
  have hT'sub : ∀ n ∈ T', n ∈ N := fun n hn => hT' ▸ Ideal.subset_span hn
  have hf₁ : f₁ ∈ 𝔭.primeCompl := prod_mem fun h hh => hu h (hTsub h hh)
  have hf₂ : f₂ ∈ 𝔭.primeCompl := prod_mem fun n hn => hv n (hT'sub n hn)
  refine ⟨f₁ * f₂, mul_mem hf₁ hf₂, g, hg𝔮, fun B _ _ _ => ?_⟩
  have hfu : IsUnit (algebraMap A B (f₁ * f₂)) := IsLocalization.Away.algebraMap_isUnit (f₁ * f₂)
  have hu_unit : ∀ h ∈ T, IsUnit (algebraMap A B (u h)) := by
    intro h hh
    have : u h ∣ f₁ * f₂ := (Finset.dvd_prod_of_mem u hh).mul_right f₂
    obtain ⟨c, hc⟩ := this
    rw [hc, map_mul] at hfu
    exact isUnit_of_mul_isUnit_left hfu
  have hf₂u : IsUnit (algebraMap A B f₂) := by
    rw [map_mul] at hfu; exact isUnit_of_mul_isUnit_right hfu
  constructor
  ·
    apply le_antisymm
    · rw [← hT, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨h, hh, rfl⟩
      obtain ⟨w, hw⟩ := hu_unit h hh
      refine Ideal.mem_span_singleton'.mpr ⟨↑w⁻¹ * algebraMap A B (a h), ?_⟩
      have key : algebraMap A B (u h) * algebraMap A B h = algebraMap A B (a h) * algebraMap A B g := by
        rw [← map_mul, ← map_mul, ha h (hTsub h hh)]
      rw [← hw] at key
      calc ↑w⁻¹ * algebraMap A B (a h) * algebraMap A B g
          = ↑w⁻¹ * (↑w * algebraMap A B h) := by rw [key, mul_assoc]
        _ = algebraMap A B h := by rw [← mul_assoc, Units.inv_mul, one_mul]
    · rw [Ideal.span_singleton_le_iff_mem]; exact Ideal.mem_map_of_mem _ hg𝔮
  ·
    refine mem_nonZeroDivisors_iff_right.mpr fun z hz => ?_
    obtain ⟨⟨c, ⟨m, hm⟩⟩, hcm⟩ := IsLocalization.surj (Submonoid.powers (f₁ * f₂)) z
    simp only at hcm

    have h1 : algebraMap A B (c * g) = 0 := by
      rw [map_mul, ← hcm, mul_right_comm, hz, zero_mul]
    obtain ⟨⟨m', hm'⟩, hm'c⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f₁ * f₂)) B _).mp h1
    simp only at hm'c

    have h2 : m' * c ∈ N := (hN _).mpr (by rw [mul_assoc]; exact hm'c)
    have h3 : f₂ * (m' * c) = 0 := by
      have hle : N ≤ LinearMap.ker (LinearMap.mulLeft A f₂) := by
        rw [← hT', Ideal.span_le]
        intro n hn
        change f₂ * n = 0
        obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem v hn
        change (∏ n ∈ T', v n) * n = 0
        rw [hd, mul_right_comm, hvn n (hT'sub n hn), zero_mul]
      exact hle h2
    have h4 : algebraMap A B c = 0 := by
      have := congrArg (algebraMap A B) h3
      rw [map_mul, map_mul, map_zero] at this
      have hm'u : IsUnit (algebraMap A B m') := IsLocalization.map_units B ⟨m', hm'⟩
      exact hm'u.mul_right_eq_zero.mp (hf₂u.mul_right_eq_zero.mp this)
    have h5 : z * algebraMap A B m = 0 := hcm.trans h4
    exact (IsLocalization.map_units B ⟨m, hm⟩).mul_left_eq_zero.mp h5

end AlgebraicGeometry.CompInv

open AlgebraicGeometry.Scheme.IdealSheafData in
theorem solution
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (η : Y)
    (hη : ringKrullDim (Y.presheaf.stalk η) = 1)
    (hreg : ∀ y ∈ closure ({η} : Set Y),
      IsRegularLocalRing (Y.presheaf.stalk y) ∧ ringKrullDim (Y.presheaf.stalk y) ≤ 2) :
    (Scheme.IdealSheafData.vanishingIdeal (X := Y) ⟨closure ({η} : Set Y), isClosed_closure⟩).IsInvertible := by
  classical
  set Z : Closeds Y := ⟨closure ({η} : Set Y), isClosed_closure⟩ with hZ
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  haveI : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  by_cases hx : x ∈ closure ({η} : Set Y)
  ·
    have hηU : η ∈ U := by
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hx U U.isOpen hxU
      rw [Set.mem_singleton_iff.mp hz2] at hz1
      exact hz1
    letI algx := Y.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
    letI algη := Y.presheaf.algebra_section_stalk (⟨η, hηU⟩ : U)
    haveI hlocx := hU.isLocalization_stalk ⟨x, hxU⟩
    haveI hlocη := hU.isLocalization_stalk ⟨η, hηU⟩
    set 𝔭 : Ideal Γ(Y, U) := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal with h𝔭def
    set 𝔮 : Ideal Γ(Y, U) := (hU.primeIdealOf ⟨η, hηU⟩).asIdeal with h𝔮def
    have hinj : Function.Injective hU.fromSpec := hU.fromSpec.isOpenEmbedding.injective
    have hpre : (hU.fromSpec : _ → Y) ⁻¹' ({η} : Set Y) = {hU.primeIdealOf ⟨η, hηU⟩} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hz
        apply hinj
        rw [hz, IsAffineOpen.fromSpec_primeIdealOf]
      · rintro rfl
        exact hU.fromSpec_primeIdealOf ⟨η, hηU⟩
    have hcl : (hU.fromSpec : _ → Y) ⁻¹' closure ({η} : Set Y) = closure ((hU.fromSpec : _ → Y) ⁻¹' {η}) :=
      hU.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage hU.fromSpec.continuous _
    have hIU : (vanishingIdeal Z).ideal ⟨U, hU⟩ = 𝔮 := by
      rw [vanishingIdeal_ideal]
      change PrimeSpectrum.vanishingIdeal ((hU.fromSpec : _ → Y) ⁻¹' closure ({η} : Set Y)) = _
      have h3 : PrimeSpectrum.vanishingIdeal ((hU.fromSpec : _ → Y) ⁻¹' closure ({η} : Set Y)) =
          PrimeSpectrum.vanishingIdeal (closure {hU.primeIdealOf ⟨η, hηU⟩}) := by
        congr 1
        exact hcl.trans (congrArg closure hpre)
      refine h3.trans ?_
      rw [PrimeSpectrum.vanishingIdeal_closure, PrimeSpectrum.vanishingIdeal_singleton]

    have hηx : η ⤳ x := specializes_iff_mem_closure.mpr hx
    have h𝔮𝔭 : 𝔮 ≤ 𝔭 := by
      change hU.primeIdealOf ⟨η, hηU⟩ ≤ hU.primeIdealOf ⟨x, hxU⟩
      rw [PrimeSpectrum.le_iff_specializes]
      have h2 : hU.fromSpec (hU.primeIdealOf ⟨η, hηU⟩) ⤳ hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) := by
        rwa [IsAffineOpen.fromSpec_primeIdealOf, IsAffineOpen.fromSpec_primeIdealOf]
      exact (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp h2

    have hq1 : 𝔮.height = 1 := by
      have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮 (Y.presheaf.stalk η)
      rw [hη] at h1
      exact_mod_cast h1.symm
    have hdisj : Disjoint (𝔭.primeCompl : Set Γ(Y, U)) (𝔮 : Set Γ(Y, U)) := by
      rw [Set.disjoint_left]
      intro r hr hrq
      exact hr (h𝔮𝔭 hrq)
    set P : Ideal (Y.presheaf.stalk x) := 𝔮.map (algebraMap Γ(Y, U) (Y.presheaf.stalk x)) with hPdef
    haveI hP : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔭.primeCompl _ 𝔮 inferInstance hdisj
    have hP1 : P.height = 1 := (IsLocalization.height_map_of_disjoint 𝔭.primeCompl 𝔮 hdisj).trans hq1
    obtain ⟨hregx, hdimx⟩ := hreg x hx
    haveI := hregx
    haveI : IsDomain (Y.presheaf.stalk x) := IsRegularLocalRing.isDomain _
    have hprin := IsRegularLocalRing.isPrincipal_of_isPrime_of_height_eq_one_of_ringKrullDim_le_two hdimx P hP hP1
    obtain ⟨γ, hγ⟩ : ∃ γ : Y.presheaf.stalk x, P = Ideal.span {γ} :=
      ⟨hprin.generator, (Submodule.IsPrincipal.span_singleton_generator P).symm⟩
    have hγ0 : γ ∈ nonZeroDivisors (Y.presheaf.stalk x) := by
      apply mem_nonZeroDivisors_of_ne_zero
      rintro rfl
      rw [hγ, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.height_bot] at hP1
      exact zero_ne_one hP1

    obtain ⟨f, hf𝔭, g, hg𝔮, hspread⟩ :=
      CompInv.exists_notMem_and_map_eq_span_singleton 𝔭 (Y.presheaf.stalk x) 𝔮 γ (hPdef ▸ hγ) hγ0
    have hxf : x ∈ Y.basicOpen f := by
      rw [Y.mem_basicOpen f x hxU]
      exact (IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk x) 𝔭 f).mpr hf𝔭
    haveI := hU.isLocalization_basicOpen f
    obtain ⟨hmap, hnzd⟩ := hspread Γ(Y, Y.basicOpen f)
    refine ⟨⟨U, hU⟩, f, hxf, (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) g : _), hnzd, ?_⟩
    rw [← (vanishingIdeal Z).map_ideal_basicOpen ⟨U, hU⟩ f, hIU]
    exact hmap
  ·
    have hxs : x ∉ (vanishingIdeal Z).support := by
      rw [← SetLike.mem_coe, coe_support_vanishingIdeal]; exact hx
    rw [mem_support_iff_of_mem (I := vanishingIdeal Z) (U := ⟨U, hU⟩) hxU, Scheme.mem_zeroLocus_iff] at hxs
    push Not at hxs
    obtain ⟨f, hf, hxf⟩ := hxs
    refine ⟨⟨U, hU⟩, f, hxf, 1, one_mem _, ?_⟩
    haveI := hU.isLocalization_basicOpen f
    have hunit : IsUnit (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) f) := IsLocalization.Away.algebraMap_isUnit f
    have hmem : algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) f ∈ (vanishingIdeal Z).ideal (Y.affineBasicOpen f) := by
      rw [← (vanishingIdeal Z).map_ideal_basicOpen ⟨U, hU⟩ f]
      exact Ideal.mem_map_of_mem _ hf
    rw [Ideal.span_singleton_one]
    exact Ideal.eq_top_of_isUnit_mem _ hmem hunit

end S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_vanishingIdeal_closure_of_isRegularLocalRing
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_vanishingIdeal_closure_of_isRegularLocalRing (solution)
