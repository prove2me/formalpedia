-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.map_germ_vanishingIdeal_closure_eq_branchIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/5326f35f-2c41-5d8d-a407-1709ab5cce83

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_vanishingIdeal_closure_eq_branchIdeal

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace GermVan

variable {X : Scheme.{u}}

theorem vanishingIdeal_closure_ideal_eq (U : X.affineOpens) (ξ : X) (hξ : ξ ∈ (U : X.Opens)) :
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure ({ξ} : Set X), isClosed_closure⟩).ideal U =
      (U.2.primeIdealOf ⟨ξ, hξ⟩).asIdeal := by
  have hU : IsAffineOpen (U : X.Opens) := U.2
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]

  have hpre : ⇑hU.fromSpec ⁻¹' closure ({ξ} : Set X) = closure {hU.primeIdealOf ⟨ξ, hξ⟩} := by
    rw [hU.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage hU.fromSpec.continuous]
    congr 1
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hq
      apply hU.fromSpec.isOpenEmbedding.injective
      rw [hq, IsAffineOpen.fromSpec_primeIdealOf]
    · rintro rfl
      exact hU.fromSpec_primeIdealOf ⟨ξ, hξ⟩
  refine (congrArg PrimeSpectrum.vanishingIdeal hpre).trans ?_
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.vanishingIdeal_singleton,
    PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  exact (hU.primeIdealOf ⟨ξ, hξ⟩).isPrime.radical

theorem map_germ_vanishingIdeal_closure_eq_branchIdeal {ξ x : X} (h : ξ ⤳ x) (U : X.affineOpens) (hx : x ∈ (U : X.Opens)) :
    Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom
        ((Scheme.IdealSheafData.vanishingIdeal ⟨closure ({ξ} : Set X), isClosed_closure⟩).ideal U) =
      Scheme.branchIdeal h := by
  classical
  have hU : IsAffineOpen (U : X.Opens) := U.2
  have hξ : ξ ∈ (U : X.Opens) := h.mem_open U.1.isOpen hx
  rw [vanishingIdeal_closure_ideal_eq U ξ hξ]

  letI algx := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : (U : X.Opens))
  haveI locx := hU.isLocalization_stalk ⟨x, hx⟩

  let R := Γ(X, (U : X.Opens))
  let 𝔮 := hU.primeIdealOf ⟨ξ, hξ⟩
  let S := (X.presheaf.stalkSpecializes h).hom

  have hS : ∀ a : R, S ((X.presheaf.germ (U : X.Opens) x hx).hom a) = (X.presheaf.germ (U : X.Opens) ξ hξ).hom a := by
    intro a
    exact TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hx h a

  have hmem : ∀ a : R, (X.presheaf.germ (U : X.Opens) ξ hξ).hom a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ↔
      a ∈ 𝔮.asIdeal := by
    intro a
    letI algξ := X.presheaf.algebra_section_stalk (⟨ξ, hξ⟩ : (U : X.Opens))
    haveI locξ := hU.isLocalization_stalk ⟨ξ, hξ⟩
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk ξ) 𝔮.asIdeal a
  apply le_antisymm
  ·
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Scheme.mem_branchIdeal_iff]
    change S ((X.presheaf.germ (U : X.Opens) x hx).hom a) ∈ _
    rw [hS]
    exact (hmem a).mpr ha
  ·
    intro s hs
    rw [Scheme.mem_branchIdeal_iff] at hs
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl s
    simp only at hat
    subst hat

    have hxt : x ∈ X.basicOpen (t : R) := by
      rw [X.mem_basicOpen (t : R) x hx]
      exact IsLocalization.map_units (M := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) (X.presheaf.stalk x) t
    have hξt : ξ ∈ X.basicOpen (t : R) := h.mem_open (X.basicOpen (t : R)).isOpen hxt
    have hunit : IsUnit ((X.presheaf.germ (U : X.Opens) ξ hξ).hom (t : R)) := (X.mem_basicOpen (t : R) ξ hξ).mp hξt

    have hspec : S (IsLocalization.mk' (X.presheaf.stalk x) a t) * (X.presheaf.germ (U : X.Opens) ξ hξ).hom (t : R) =
        (X.presheaf.germ (U : X.Opens) ξ hξ).hom a := by
      rw [← hS (t : R), ← map_mul]
      change S (IsLocalization.mk' (X.presheaf.stalk x) a t * algebraMap R (X.presheaf.stalk x) (t : R)) = _
      rw [IsLocalization.mk'_spec, ← hS a]
      rfl
    have ha : a ∈ 𝔮.asIdeal := by
      rw [← hmem a, ← hspec]
      exact Ideal.mul_mem_right _ _ hs
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)

end GermVan

theorem solution
    {X : Scheme.{u}} {ξ x : X} (h : ξ ⤳ x) (U : X.affineOpens) (hx : x ∈ (U : X.Opens)) :
    Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom
        ((Scheme.IdealSheafData.vanishingIdeal ⟨closure {ξ}, isClosed_closure⟩).ideal U) =
      Scheme.branchIdeal h :=
  GermVan.map_germ_vanishingIdeal_closure_eq_branchIdeal h U hx

end S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_vanishingIdeal_closure_eq_branchIdeal
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_vanishingIdeal_closure_eq_branchIdeal (solution)
