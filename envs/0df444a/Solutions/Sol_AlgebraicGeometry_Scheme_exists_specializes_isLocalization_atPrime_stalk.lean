-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_specializes_isLocalization_atPrime_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/ec43995a-e0e1-53e5-9263-3bc50d4001ba

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_specializes_isLocalization_atPrime_stalk

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {X : Scheme.{u}} (y : X) (P : Ideal (X.presheaf.stalk y)) [P.IsPrime] :
    ∃ (x : X) (h : x ⤳ y),
      letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
      IsLocalization.AtPrime (X.presheaf.stalk x) P := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  letI algy := X.presheaf.algebra_section_stalk ⟨y, hyU⟩
  have hLy := hU.isLocalization_stalk ⟨y, hyU⟩
  set q := hU.primeIdealOf ⟨y, hyU⟩ with hq

  let p₀ : PrimeSpectrum Γ(X, U) := ⟨P.comap (X.presheaf.germ U y hyU).hom, Ideal.comap_isPrime _ _⟩
  have hPle : P ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  have hp₀q : p₀ ≤ q := by
    intro a ha
    have ha' : (X.presheaf.germ U y hyU).hom a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := hPle ha
    have := (@IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ (X.presheaf.stalk y) _ _ q.asIdeal _ hLy a _).mp ha'
    exact this

  let x : X := hU.fromSpec.base p₀
  have hxU : x ∈ (U : Set X) := by
    rw [← hU.range_fromSpec]; exact ⟨p₀, rfl⟩
  have hyq : hU.fromSpec.base q = y := hU.fromSpec_primeIdealOf ⟨y, hyU⟩
  have h : x ⤳ y := by
    rw [← hyq]
    exact ((PrimeSpectrum.le_iff_specializes p₀ q).mp hp₀q).map hU.fromSpec.base.hom.continuous
  refine ⟨x, h, ?_⟩

  have hLx : @IsLocalization.AtPrime _ _ (X.presheaf.stalk x) _ (X.presheaf.algebra_section_stalk ⟨x, hxU⟩) p₀.asIdeal _ :=
    hU.isLocalization_stalk' p₀ hxU
  letI algx := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have htower : ∀ a : Γ(X, U), algebraMap (X.presheaf.stalk y) (X.presheaf.stalk x) (algebraMap Γ(X, U) (X.presheaf.stalk y) a) =
      algebraMap Γ(X, U) (X.presheaf.stalk x) a := by
    intro a
    change (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ U y hyU).hom a) = (X.presheaf.germ U x hxU).hom a
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  haveI : IsScalarTower Γ(X, U) (X.presheaf.stalk y) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq (fun a => (htower a).symm)
  have hcompl : q.asIdeal.primeCompl ≤ p₀.asIdeal.primeCompl := fun s hs hs' => hs (hp₀q hs')
  have hN := IsLocalization.isLocalization_of_submonoid_le (S := X.presheaf.stalk y) (T := X.presheaf.stalk x)
    q.asIdeal.primeCompl p₀.asIdeal.primeCompl hcompl

  refine @IsLocalization.of_le _ _ _ (X.presheaf.stalk x) _ _ hN P.primeCompl ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact ha
  · intro z hz
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.asIdeal.primeCompl z
    dsimp only at hz ⊢

    have ha : a ∉ p₀.asIdeal := by
      intro ha
      apply hz
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ ha
    have hs : (s : Γ(X, U)) ∉ p₀.asIdeal := fun hs => s.2 (hp₀q hs)

    have hspec := IsLocalization.mk'_spec (X.presheaf.stalk y) a s
    have himg : algebraMap (X.presheaf.stalk y) (X.presheaf.stalk x) (IsLocalization.mk' (X.presheaf.stalk y) a s) *
        algebraMap Γ(X, U) (X.presheaf.stalk x) s = algebraMap Γ(X, U) (X.presheaf.stalk x) a := by
      rw [← htower s, ← map_mul, hspec, htower]
    have hua : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) a) :=
      (@IsLocalization.AtPrime.isUnit_to_map_iff _ _ (X.presheaf.stalk x) _ _ p₀.asIdeal _ hLx a).mpr ha
    rw [← himg] at hua
    exact isUnit_of_mul_isUnit_left hua

end S_AlgebraicGeometry_Scheme_exists_specializes_isLocalization_atPrime_stalk
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_specializes_isLocalization_atPrime_stalk (solution)
