-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.exists_span_eq_top_and_forall_exists_lift_away_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/760a5d6b-aeab-50e8-9dc7-fdde92d755cb

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isNilpotent_of_isAffine
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_exists_span_eq_top_and_forall_exists_lift_away_of_isNilpotent

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace SmoothNilpLiftLocal

variable {C : Type u} [CommRing C]

theorem le_of_isPrime_of_isNilpotent {J P : Ideal C} (hJ : IsNilpotent J) [P.IsPrime] : J ≤ P := by
  obtain ⟨n, hn⟩ := hJ
  exact Ideal.IsPrime.le_of_pow_le (I := J) (P := P) (n := n) (by rw [hn]; exact bot_le)

theorem isNilpotent_map {D : Type u} [CommRing D] (φ : C →+* D) {J : Ideal C} (hJ : IsNilpotent J) :
    IsNilpotent (J.map φ) := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  rw [← Ideal.map_pow, hn]
  simp

end SmoothNilpLiftLocal

open SmoothNilpLiftLocal in
theorem solution
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [Smooth f]
    {C : Type u} [CommRing C] (J : Ideal C) (hJ : IsNilpotent J)
    (t : Spec (CommRingCat.of C) ⟶ S) (x₀ : Spec (CommRingCat.of (C ⧸ J)) ⟶ X)
    (hx₀ : x₀ ≫ f = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ t) :
    ∃ (ι : Type u) (a : ι → C), Ideal.span (Set.range a) = ⊤ ∧
      ∀ i : ι, ∃ x : Spec (CommRingCat.of (Localization.Away (a i))) ⟶ X,
        x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away (a i)))) ≫ t ∧
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((J.map (algebraMap C (Localization.Away (a i))))))) ≫ x =
          Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J.map (algebraMap C (Localization.Away (a i))))
            (algebraMap C (Localization.Away (a i))) Ideal.le_comap_map)) ≫ x₀ := by
  classical

  have key : ∀ p : PrimeSpectrum (C ⧸ J), ∃ (a : C) (U : X.Opens), IsAffineOpen U ∧
      Ideal.Quotient.mk J a ∉ p.asIdeal ∧
      ∀ q : PrimeSpectrum (C ⧸ J), Ideal.Quotient.mk J a ∉ q.asIdeal → x₀.base q ∈ U := by
    intro p
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (x₀.base p)) isOpen_univ
    have hO : IsOpen (x₀.base ⁻¹' (U : Set X)) := U.isOpen.preimage x₀.continuous
    have hpO : p ∈ x₀.base ⁻¹' (U : Set X) := hxU
    obtain ⟨_, ⟨b, rfl⟩, hpb, hbO⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpO hO
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨a, U, hU, hpb, fun q hq => ?_⟩
    exact hbO hq
  choose a U hUaff ha hU using key

  have hspan : Ideal.span (Set.range a) = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    have hJm : J ≤ m := le_of_isPrime_of_isNilpotent hJ
    have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ m := by rw [Ideal.mk_ker]; exact hJm
    let p : PrimeSpectrum (C ⧸ J) :=
      ⟨m.map (Ideal.Quotient.mk J), Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker⟩
    apply ha p
    change Ideal.Quotient.mk J (a p) ∈ m.map (Ideal.Quotient.mk J)
    exact Ideal.mem_map_of_mem _ (hle (Ideal.subset_span ⟨p, rfl⟩))
  refine ⟨PrimeSpectrum (C ⧸ J), a, hspan, fun p => ?_⟩

  let A : Type u := Localization.Away (a p)
  let φ : C →+* A := algebraMap C A
  let J' : Ideal A := J.map φ
  have hJ' : IsNilpotent J' := isNilpotent_map φ hJ
  let qm : C ⧸ J →+* A ⧸ J' := Ideal.quotientMap J' φ Ideal.le_comap_map
  let x₀' : Spec (CommRingCat.of (A ⧸ J')) ⟶ X := Spec.map (CommRingCat.ofHom qm) ≫ x₀
  haveI : IsAffine (U p) := hUaff p

  have hrange : Set.range x₀'.base ⊆ Set.range (U p).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨r, rfl⟩
    change x₀.base ((Spec.map (CommRingCat.ofHom qm)).base r) ∈ (U p : Set X)
    apply hU p
    change qm (Ideal.Quotient.mk J (a p)) ∉ r.asIdeal
    rw [Ideal.quotientMap_mk]
    have hu : IsUnit (Ideal.Quotient.mk J' (φ (a p))) :=
      (IsLocalization.Away.algebraMap_isUnit (a p)).map _
    exact fun hmem => r.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  let y₀ : Spec (CommRingCat.of (A ⧸ J')) ⟶ ↑(U p) := IsOpenImmersion.lift (U p).ι x₀' hrange
  have hy₀ : y₀ ≫ (U p).ι = x₀' := IsOpenImmersion.lift_fac _ _ _
  have hq : (CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ CommRingCat.ofHom qm :
      CommRingCat.of C ⟶ CommRingCat.of (A ⧸ J')) =
      CommRingCat.ofHom φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk J') := by
    ext c
    exact (Ideal.quotientMap_mk (f := φ) (H := Ideal.le_comap_map) (x := c))
  have hx₀' : y₀ ≫ ((U p).ι ≫ f) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) ≫ (Spec.map (CommRingCat.ofHom φ) ≫ t) := by
    rw [← Category.assoc, hy₀]
    change (Spec.map (CommRingCat.ofHom qm) ≫ x₀) ≫ f = _
    rw [Category.assoc, hx₀, ← Category.assoc, ← Spec.map_comp, hq, Spec.map_comp, Category.assoc]
  obtain ⟨x, hx1, hx2⟩ :=
    AlgebraicGeometry.Smooth.exists_lift_comp_eq_of_isNilpotent_of_isAffine ((U p).ι ≫ f) J' hJ'
      (Spec.map (CommRingCat.ofHom φ) ≫ t) y₀ hx₀'
  refine ⟨x ≫ (U p).ι, ?_, ?_⟩
  · rw [Category.assoc]; exact hx1
  · change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J')) ≫ x ≫ (U p).ι = x₀'
    rw [← Category.assoc, hx2, hy₀]

end S_AlgebraicGeometry_Smooth_exists_span_eq_top_and_forall_exists_lift_away_of_isNilpotent
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_exists_span_eq_top_and_forall_exists_lift_away_of_isNilpotent (solution)
