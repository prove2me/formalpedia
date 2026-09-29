-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.locallyOfFinitePresentation_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/957bcf27-31cc-5c92-b0fe-32c9e462424e

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_locallyOfFinitePresentation_pi

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry

universe u

namespace ProjPiLfpAux

open MvPolynomial HomogeneousLocalization

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

theorem finitePresentation_away (i : Fin (n + 1)) :
    Algebra.FinitePresentation R (Away 𝒜 (MvPolynomial.X i)) := by
  classical
  let ι := {k : Fin (n + 1) // k ≠ i}
  let α : MvPolynomial ι R →ₐ[R] Away 𝒜 (MvPolynomial.X i) := MvPolynomial.aeval fun k => ProjSpace.ratio R n i k.1
  have hsurj : Function.Surjective α := by
    rw [← AlgHom.range_eq_top, MvPolynomial.aeval_range, eq_top_iff, ← ProjSpace.adjoin_range_ratio R n i,
      Algebra.adjoin_le_iff]
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = i
    · subst hk; rw [ProjSpace.ratio_self]; exact Subalgebra.one_mem _
    · exact Algebra.subset_adjoin ⟨⟨k, hk⟩, rfl⟩
  let β₀ : MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial ι R :=
    MvPolynomial.aeval fun k => if hk : k = i then 1 else MvPolynomial.X ⟨k, hk⟩
  have hβ₀i : β₀ (MvPolynomial.X i) = 1 := by simp [β₀]
  have hβ₀k : ∀ k : ι, β₀ (MvPolynomial.X k.1) = MvPolynomial.X k := fun k => by simp [β₀, k.2]
  have hunit : IsUnit ((β₀ : MvPolynomial (Fin (n + 1)) R →+* MvPolynomial ι R) (MvPolynomial.X i)) := by
    rw [AlgHom.coe_toRingHom, hβ₀i]; exact isUnit_one
  let β₁ : Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →+* MvPolynomial ι R :=
    IsLocalization.Away.lift (S := Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R))
      (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) hunit
  have hβ₁ : ∀ q, β₁ (algebraMap (MvPolynomial (Fin (n + 1)) R) (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) q) = β₀ q := fun q =>
    IsLocalization.Away.lift_eq (S := Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) _ hunit q

  have hβα_X : ∀ k : ι, β₁ ((α (MvPolynomial.X k)).val) = MvPolynomial.X k := by
    intro k
    have hαk : α (MvPolynomial.X k) = ProjSpace.ratio R n i k.1 := MvPolynomial.aeval_X _ k
    rw [hαk]
    have hmul : (ProjSpace.ratio R n i k.1).val * algebraMap (MvPolynomial (Fin (n + 1)) R) (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) (MvPolynomial.X i) =
        algebraMap (MvPolynomial (Fin (n + 1)) R) (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) (MvPolynomial.X k.1) := by
      rw [ProjSpace.ratio, Away.val_mk, Localization.mk_eq_mk']
      convert IsLocalization.mk'_spec (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) (MvPolynomial.X k.1)
        (⟨MvPolynomial.X i ^ 1, 1, rfl⟩ : Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) using 2
      simp
    have := congrArg β₁ hmul
    rw [map_mul, hβ₁, hβ₁] at this
    change _ * β₀ (MvPolynomial.X i) = β₀ (MvPolynomial.X k.1) at this
    rwa [hβ₀i, mul_one, hβ₀k] at this
  have hβα_C : ∀ r : R, β₁ ((α (MvPolynomial.C r)).val) = MvPolynomial.C r := by
    intro r
    rw [MvPolynomial.algHom_C, ProjSpace.val_algebraMap, hβ₁]
    exact MvPolynomial.algHom_C β₀ r
  let β : Away 𝒜 (MvPolynomial.X i) →+* MvPolynomial ι R :=
    β₁.comp (algebraMap (Away 𝒜 (MvPolynomial.X i)) (Localization.Away (MvPolynomial.X i)))
  have hβ : ∀ z, β z = β₁ z.val := fun z => rfl
  have hβα : β.comp α.toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; rw [RingHom.comp_apply, hβ]; exact hβα_C r
    · intro k; rw [RingHom.comp_apply, hβ]; exact hβα_X k
  have hinj : Function.Injective α := by
    intro a b hab
    have ha := RingHom.congr_fun hβα a
    have hb := RingHom.congr_fun hβα b
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingHom.id_apply] at ha hb
    rw [← ha, ← hb, hab]
  haveI : Finite ι := inferInstance
  exact Algebra.FinitePresentation.equiv (AlgEquiv.ofBijective α ⟨hinj, hsurj⟩)

end ProjPiLfpAux

theorem solution (R : Type u) [CommRing R] (n : ℕ) :
    LocallyOfFinitePresentation (ProjSpace.π R n) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation) (ProjSpace.affineOpenCover R n).openCover]
  intro j
  have h := ProjSpace.awayι_comp_π R n j
  rw [ProjSpace.affineOpenCover_f]
  erw [h]
  show @LocallyOfFinitePresentation (Spec _) (Spec _) (Spec.map (CommRingCat.ofHom (algebraMap R
    (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X (j : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) R)))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation), CommRingCat.hom_ofHom, RingHom.finitePresentation_algebraMap]
  exact ProjPiLfpAux.finitePresentation_away R n j

end S_AlgebraicGeometry_ProjSpace_locallyOfFinitePresentation_pi
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_locallyOfFinitePresentation_pi (solution)
