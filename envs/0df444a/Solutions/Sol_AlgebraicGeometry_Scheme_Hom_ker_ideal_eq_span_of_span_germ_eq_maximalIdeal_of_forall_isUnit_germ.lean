-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.ker_ideal_eq_span_of_span_germ_eq_maximalIdeal_of_forall_isUnit_germ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/b9539f06-ff1f-5e5f-8d4e-4cd02b347aa6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_ker_ideal_eq_span_of_span_germ_eq_maximalIdeal_of_forall_isUnit_germ

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

namespace LpSpan

universe v

theorem mem_map_localization_of_mem_map {R : Type v} [CommRing R] (P : Ideal R) [P.IsPrime]
    (S : Type v) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S P] (J : Ideal R) (b : R)
    (h : algebraMap R S b ∈ J.map (algebraMap R S)) :
    algebraMap R (Localization.AtPrime P) b ∈ J.map (algebraMap R (Localization.AtPrime P)) := by
  set e : S ≃ₐ[R] Localization.AtPrime P := IsLocalization.algEquiv P.primeCompl S (Localization.AtPrime P) with he
  have hcomp : (e : S →+* Localization.AtPrime P).comp (algebraMap R S) = algebraMap R (Localization.AtPrime P) := by
    ext r
    exact e.commutes r
  have h1 := Ideal.mem_map_of_mem (e : S →+* Localization.AtPrime P) h
  rw [Ideal.map_map, hcomp] at h1
  have h2 : (e : S →+* Localization.AtPrime P) (algebraMap R S b) = algebraMap R (Localization.AtPrime P) b := e.commutes b
  rwa [h2] at h1

end LpSpan

open LpSpan in

theorem solution
    {X : Scheme.{u}} [IsIntegral X] {K : Type u} [Field K]
    (j : Spec (CommRingCat.of K) ⟶ X) [IsClosedImmersion j]
    (W : X.Opens) (hPW : j.base (IsLocalRing.closedPoint K) ∈ W) (a : Γ(X, W))

    (ha0 : j.app W a = 0)

    (hagen : Ideal.span {X.presheaf.germ W (j.base (IsLocalRing.closedPoint K)) hPW a} =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (j.base (IsLocalRing.closedPoint K))))

    (haU : ∀ (z : X) (hz : z ∈ W), z ≠ j.base (IsLocalRing.closedPoint K) → IsUnit (X.presheaf.germ W z hz a))

    (hW : ∃ z ∈ W, z ≠ j.base (IsLocalRing.closedPoint K)) :
    ∀ (U : X.affineOpens) (hU : (U : X.Opens) ≤ W),
      j.ker.ideal U = Ideal.span {X.presheaf.map (homOfLE hU).op a} ∧
        X.presheaf.map (homOfLE hU).op a ∈ nonZeroDivisors Γ(X, U) := by

  classical
  intro U hU
  set P := j.base (IsLocalRing.closedPoint K) with hPdef
  set aU : Γ(X, U) := X.presheaf.map (homOfLE hU).op a with haU_def
  have hUaff : IsAffineOpen (U : X.Opens) := U.2

  have hker : j.ker.ideal U = RingHom.ker (j.app U).hom := Scheme.Hom.ker_apply j U
  have haUker : (j.app U).hom aU = 0 := by
    have hnat := j.naturality (homOfLE hU).op
    have := congrArg (fun φ => φ.hom a) hnat
    simp only [CommRingCat.comp_apply] at this
    rw [haU_def]
    erw [this, ha0, map_zero]

  have hgermU : ∀ (z : X) (hz : z ∈ (U : X.Opens)), X.presheaf.germ U z hz aU = X.presheaf.germ W z (hU hz) a := by
    intro z hz
    rw [haU_def]
    exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hU) z hz a
  refine ⟨?_, ?_⟩
  ·
    rw [hker]
    apply le_antisymm
    · intro b hb
      have hb0 : (j.app U).hom b = 0 := hb
      apply Ideal.mem_of_localization_maximal
      intro 𝔪 h𝔪
      haveI : 𝔪.IsMaximal := h𝔪
      let y : PrimeSpectrum Γ(X, U) := ⟨𝔪, h𝔪.isPrime⟩
      have hy : hUaff.fromSpec.base y ∈ (U : X.Opens) := by
        rw [← SetLike.mem_coe, ← hUaff.range_fromSpec]; exact ⟨y, rfl⟩
      by_cases hzP : hUaff.fromSpec.base y = P
      ·
        have hPU : P ∈ (U : X.Opens) := hzP ▸ hy
        have hyP : y = hUaff.primeIdealOf ⟨P, hPU⟩ := by
          apply hUaff.fromSpec.isOpenEmbedding.injective
          rw [hzP, hUaff.fromSpec_primeIdealOf ⟨P, hPU⟩]

        letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨P, hPU⟩ : ↥(U : X.Opens))
        haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk P) (hUaff.primeIdealOf ⟨P, hPU⟩).asIdeal := hUaff.isLocalization_stalk ⟨P, hPU⟩
        have hgoal : algebraMap Γ(X, U) (X.presheaf.stalk P) b ∈ (Ideal.span {aU}).map (algebraMap Γ(X, U) (X.presheaf.stalk P)) := by
          rw [Ideal.map_span, Set.image_singleton]
          show X.presheaf.germ U P hPU b ∈ Ideal.span {X.presheaf.germ U P hPU aU}
          rw [hgermU P hPU, hagen, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
          intro hunit
          have h1 : (j.stalkMap (IsLocalRing.closedPoint K)).hom (X.presheaf.germ U P hPU b) = 0 := by
            have h := Scheme.Hom.germ_stalkMap_apply j U (IsLocalRing.closedPoint K) hPU b
            rw [hb0, map_zero] at h
            exact h
          have h2 := hunit.map (j.stalkMap (IsLocalRing.closedPoint K)).hom
          rw [h1] at h2
          exact not_isUnit_zero h2
        have hmemP := mem_map_localization_of_mem_map (hUaff.primeIdealOf ⟨P, hPU⟩).asIdeal (X.presheaf.stalk P) (Ideal.span {aU}) b hgoal
        have h𝔪eq : 𝔪 = (hUaff.primeIdealOf ⟨P, hPU⟩).asIdeal := congrArg PrimeSpectrum.asIdeal hyP
        subst h𝔪eq
        exact hmemP
      ·
        letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hUaff.fromSpec.base y, hy⟩ : ↥(U : X.Opens))
        haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk (hUaff.fromSpec.base y)) y.asIdeal := hUaff.isLocalization_stalk' y hy
        have hgoal : algebraMap Γ(X, U) (X.presheaf.stalk (hUaff.fromSpec.base y)) b ∈
            (Ideal.span {aU}).map (algebraMap Γ(X, U) (X.presheaf.stalk (hUaff.fromSpec.base y))) := by
          rw [Ideal.map_span, Set.image_singleton]
          have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk (hUaff.fromSpec.base y)) aU) := by
            show IsUnit (X.presheaf.germ U _ hy aU)
            rw [hgermU _ hy]
            exact haU _ (hU hy) hzP
          rw [Ideal.span_singleton_eq_top.mpr hu]
          exact Submodule.mem_top
        exact mem_map_localization_of_mem_map y.asIdeal (X.presheaf.stalk (hUaff.fromSpec.base y)) (Ideal.span {aU}) b hgoal
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact haUker
  ·
    by_cases hne : Nonempty ↥(U : X.Opens)
    · obtain ⟨⟨z, hz⟩⟩ := hne
      haveI : IsDomain Γ(X, U) := @IsIntegral.component_integral X _ (U : X.Opens) ⟨⟨z, hz⟩⟩
      apply mem_nonZeroDivisors_of_ne_zero
      intro haU0

      have ha : a = 0 := by
        apply germ_injective_of_isIntegral (X := X) z (hU hz)
        rw [← hgermU z hz, haU0, map_zero, map_zero]
      obtain ⟨z₀, hz₀W, hz₀P⟩ := hW
      have hu := haU z₀ hz₀W hz₀P
      rw [ha, map_zero] at hu
      exact not_isUnit_zero hu
    ·
      have hsub : Subsingleton Γ(X, U) := by
        have hbot : (U : X.Opens) = ⊥ := by
          ext x
          simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
          exact fun hx => hne ⟨⟨x, hx⟩⟩
        rw [hbot]
        exact CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEmpty)
      haveI := hsub
      exact ⟨fun x _ => Subsingleton.elim _ _, fun x _ => Subsingleton.elim _ _⟩

end S_AlgebraicGeometry_Scheme_Hom_ker_ideal_eq_span_of_span_germ_eq_maximalIdeal_of_forall_isUnit_germ
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_ker_ideal_eq_span_of_span_germ_eq_maximalIdeal_of_forall_isUnit_germ (solution)
