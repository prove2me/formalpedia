-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.ringKrullDim_stalk_eq_one_of_forall_specializes_notMem_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0758ab18-0cd7-5d46-98be-78bb5ff102bd

import Mathlib
import Theorems.Thm_Ideal_height_eq_one_iff_mem_minimalPrimes_span_singleton_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_ringKrullDim_stalk_eq_one_of_forall_specializes_notMem_basicOpen

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem solution
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (t : Γ(Y, ⊤)) (ht : t ≠ 0) (η : Y)
    (hηt : η ∉ Y.basicOpen t) (hmax : ∀ y : Y, y ⤳ η → y ∉ Y.basicOpen t → y = η) :
    ringKrullDim (Y.presheaf.stalk η) = 1 := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  haveI : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : Nonempty U := ⟨⟨η, hηU⟩⟩
  haveI : IsDomain Γ(Y, U) := IsIntegral.component_integral U
  letI alg := Y.presheaf.algebra_section_stalk (⟨η, hηU⟩ : U)
  haveI hloc := hU.isLocalization_stalk ⟨η, hηU⟩
  set 𝔮 : Ideal Γ(Y, U) := (hU.primeIdealOf ⟨η, hηU⟩).asIdeal with h𝔮def

  set tU : Γ(Y, U) := (Y.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom t with htU
  have htU0 : tU ≠ 0 := by
    intro h
    apply ht
    have hinj := map_injective_of_isIntegral Y (homOfLE le_top : U ⟶ ⊤)
    exact hinj (by rw [← htU, h, map_zero])
  have hbo : Y.basicOpen tU = U ⊓ Y.basicOpen t := Y.basicOpen_res t _

  have key : ∀ z : PrimeSpectrum Γ(Y, U), hU.fromSpec z ∈ Y.basicOpen tU ↔ tU ∉ z.asIdeal := by
    intro z
    have hzU : hU.fromSpec z ∈ U := by
      have : hU.fromSpec z ∈ Set.range hU.fromSpec := ⟨z, rfl⟩
      rwa [hU.range_fromSpec] at this
    have hz : hU.primeIdealOf ⟨hU.fromSpec z, hzU⟩ = z :=
      hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨hU.fromSpec z, hzU⟩)
    letI algz := Y.presheaf.algebra_section_stalk (⟨hU.fromSpec z, hzU⟩ : U)
    haveI hlocz := hU.isLocalization_stalk ⟨hU.fromSpec z, hzU⟩
    rw [hz] at hlocz
    rw [Y.mem_basicOpen tU _ hzU]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk (hU.fromSpec z)) z.asIdeal tU)
  have htU𝔮 : tU ∈ 𝔮 := by
    by_contra h
    have h1 := (key (hU.primeIdealOf ⟨η, hηU⟩)).mpr h
    rw [IsAffineOpen.fromSpec_primeIdealOf, hbo] at h1
    exact hηt h1.2

  have hmin : 𝔮 ∈ (Ideal.span {tU}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr htU𝔮⟩, ?_⟩
    rintro P ⟨hP, hPt⟩ hP𝔮

    let z : PrimeSpectrum Γ(Y, U) := ⟨P, hP⟩
    have hzU : hU.fromSpec z ∈ U := by
      have : hU.fromSpec z ∈ Set.range hU.fromSpec := ⟨z, rfl⟩
      rwa [hU.range_fromSpec] at this
    have hspec : hU.fromSpec z ⤳ η := by
      have h1 : z ⤳ hU.primeIdealOf ⟨η, hηU⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp hP𝔮
      have h2 := h1.map hU.fromSpec.continuous
      rwa [IsAffineOpen.fromSpec_primeIdealOf] at h2
    have hnot : hU.fromSpec z ∉ Y.basicOpen t := by
      intro h
      have h1 : hU.fromSpec z ∈ Y.basicOpen tU := by rw [hbo]; exact ⟨hzU, h⟩
      exact ((key z).mp h1) ((Ideal.span_singleton_le_iff_mem _).mp hPt)
    have heq : hU.fromSpec z = η := hmax _ hspec hnot
    have hz : z = hU.primeIdealOf ⟨η, hηU⟩ :=
      hU.fromSpec.isOpenEmbedding.injective (heq.trans (hU.fromSpec_primeIdealOf ⟨η, hηU⟩).symm)
    have : P = 𝔮 := congrArg PrimeSpectrum.asIdeal hz
    exact this.symm.le
  have hq1 : 𝔮.height = 1 :=
    (Ideal.height_eq_one_iff_mem_minimalPrimes_span_singleton_of_mem htU0 𝔮 htU𝔮).mpr hmin
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮 (Y.presheaf.stalk η), hq1]
  rfl

end S_AlgebraicGeometry_Scheme_ringKrullDim_stalk_eq_one_of_forall_specializes_notMem_basicOpen
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_ringKrullDim_stalk_eq_one_of_forall_specializes_notMem_basicOpen (solution)
