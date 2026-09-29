-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/9ccd0eab-9ff4-5af1-b793-6ae596a0b2dd

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjPointEq

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "XX" => (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)

theorem X_mul_comm (i j : Fin (n + 1)) : XX i * XX j = XX j * XX i := mul_comm _ _

noncomputable abbrev mapI (i j : Fin (n + 1)) : Away 𝒜 (XX i) →+* Away 𝒜 (XX i * XX j) :=
  awayMap 𝒜 (ProjSpace.X_mem_one R n j) (rfl : XX i * XX j = XX i * XX j)

noncomputable abbrev mapJ (i j : Fin (n + 1)) : Away 𝒜 (XX j) →+* Away 𝒜 (XX i * XX j) :=
  awayMap 𝒜 (ProjSpace.X_mem_one R n i) (X_mul_comm R n i j)

theorem mapJ_ratio_mul_mapI_ratio (i j l : Fin (n + 1)) :
    mapJ R n i j (ProjSpace.ratio R n j l) * mapI R n i j (ProjSpace.ratio R n i j) =
      mapI R n i j (ProjSpace.ratio R n i l) := by
  apply HomogeneousLocalization.val_injective
  simp only [ProjSpace.ratio, val_mul, awayMap_mk, Away.val_mk, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

theorem isLocalizationElem_eq (i j : Fin (n + 1)) :
    Away.isLocalizationElem (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n j) =
      ProjSpace.ratio R n i j := by
  apply HomogeneousLocalization.val_injective
  simp [ProjSpace.ratio, Away.val_mk]

theorem mapI_algebraMap (i j : Fin (n + 1)) (r : R) :
    mapI R n i j (algebraMap R (Away 𝒜 (XX i)) r) = mapJ R n i j (algebraMap R (Away 𝒜 (XX j)) r) := by
  change awayMap 𝒜 _ _ (fromZeroRingHom 𝒜 _ (ProjSpace.grad0Equiv R n r)) =
    awayMap 𝒜 _ _ (fromZeroRingHom 𝒜 _ (ProjSpace.grad0Equiv R n r))
  rw [awayMap_fromZeroRingHom, awayMap_fromZeroRingHom]

section lift

variable {B : Type u} [CommRing B] [Algebra R B] (a : Fin (n + 1) → B) (i j : Fin (n + 1))
  (hj : IsUnit (a j))
  (ψi : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B)
  (hψi : ∀ l, ψi (ProjSpace.ratio R n i l) * a i = a l)

include hj hψi in
theorem isUnit_ψi_ratio : IsUnit (ψi (ProjSpace.ratio R n i j)) := by
  have h : IsUnit (ψi (ProjSpace.ratio R n i j) * a i) := by rw [hψi j]; exact hj
  exact (IsUnit.mul_iff.mp h).1

include hj hψi in
theorem isUnit_ψi_elem :
    IsUnit (ψi.toRingHom (Away.isLocalizationElem (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n j))) := by
  rw [isLocalizationElem_eq]
  exact isUnit_ψi_ratio R n a i j hj ψi hψi

noncomputable def liftij : Away 𝒜 (XX i * XX j) →+* B :=
  letI := (mapI R n i j).toAlgebra
  letI := Away.isLocalization_mul (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n j)
    (rfl : XX i * XX j = XX i * XX j) one_ne_zero
  IsLocalization.Away.lift
    (Away.isLocalizationElem (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n j))
    (g := ψi.toRingHom) (isUnit_ψi_elem R n a i j hj ψi hψi)

theorem liftij_mapI (z : Away 𝒜 (XX i)) : liftij R n a i j hj ψi hψi (mapI R n i j z) = ψi z := by
  letI := (mapI R n i j).toAlgebra
  letI := Away.isLocalization_mul (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n j)
    (rfl : XX i * XX j = XX i * XX j) one_ne_zero
  exact IsLocalization.Away.lift_eq (S := Away 𝒜 (XX i * XX j))
    (Away.isLocalizationElem (ProjSpace.X_mem_one R n i) (ProjSpace.X_mem_one R n j))
    (isUnit_ψi_elem R n a i j hj ψi hψi) z

theorem liftij_mapJ
    (ψj : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B)
    (hψj : ∀ l, ψj (ProjSpace.ratio R n j l) * a j = a l)
    (z : Away 𝒜 (XX j)) : liftij R n a i j hj ψi hψi (mapJ R n i j z) = ψj z := by
  have hz : z ∈ Algebra.adjoin R (Set.range (ProjSpace.ratio R n j)) := by
    rw [ProjSpace.adjoin_range_ratio]; trivial
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨l, rfl⟩ := hz

    rw [← hj.mul_left_inj, hψj l]
    have key : liftij R n a i j hj ψi hψi (mapJ R n i j (ProjSpace.ratio R n j l)) *
        (ψi (ProjSpace.ratio R n i j) * a i) = a l := by
      rw [← mul_assoc, ← liftij_mapI R n a i j hj ψi hψi (ProjSpace.ratio R n i j), ← map_mul,
        mapJ_ratio_mul_mapI_ratio, liftij_mapI, hψi]
    rwa [hψi j] at key
  | algebraMap r =>
    rw [← mapI_algebraMap, liftij_mapI, AlgHom.commutes, AlgHom.commutes]
  | add z w _ _ hz hw => rw [map_add, map_add, hz, hw, map_add]
  | mul z w _ _ hz hw => rw [map_mul, map_mul, hz, hw, map_mul]

theorem ψi_eq_comp : ψi.toRingHom = (liftij R n a i j hj ψi hψi).comp (mapI R n i j) :=
  RingHom.ext fun z => (liftij_mapI R n a i j hj ψi hψi z).symm

theorem ψj_eq_comp
    (ψj : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B)
    (hψj : ∀ l, ψj (ProjSpace.ratio R n j l) * a j = a l) :
    ψj.toRingHom = (liftij R n a i j hj ψi hψi).comp (mapJ R n i j) :=
  RingHom.ext fun z => (liftij_mapJ R n a i j hj ψi hψi ψj hψj z).symm

include hj hψi in
theorem main
    (ψj : Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B)
    (hψj : ∀ l, ψj (ProjSpace.ratio R n j l) * a j = a l) :
    Spec.map (CommRingCat.ofHom ψi.toRingHom) ≫
        Proj.awayι 𝒜 (XX i) (ProjSpace.X_mem_one R n i) one_pos =
      Spec.map (CommRingCat.ofHom ψj.toRingHom) ≫
        Proj.awayι 𝒜 (XX j) (ProjSpace.X_mem_one R n j) one_pos := by
  rw [ψi_eq_comp R n a i j hj ψi hψi, ψj_eq_comp R n a i j hj ψi hψi ψj hψj, CommRingCat.ofHom_comp,
    CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (awayMap 𝒜 _ _)) ≫ Proj.awayι 𝒜 _ _ _ =
    Spec.map _ ≫ Spec.map (CommRingCat.ofHom (awayMap 𝒜 _ _)) ≫ Proj.awayι 𝒜 _ _ _
  rw [Proj.SpecMap_awayMap_awayι 𝒜 (ProjSpace.X_mem_one R n i) one_pos (ProjSpace.X_mem_one R n j)
      (rfl : XX i * XX j = XX i * XX j),
    Proj.SpecMap_awayMap_awayι 𝒜 (ProjSpace.X_mem_one R n j) one_pos (ProjSpace.X_mem_one R n i)
      (X_mul_comm R n i j)]

end lift

end ProjPointEq

set_option linter.unusedVariables false in
theorem solution
    (R : Type u) [CommRing R] (n : ℕ) (B : Type u) [CommRing B] [Algebra R B]
    (a : Fin (n + 1) → B) (i j : Fin (n + 1)) (hi : IsUnit (a i)) (hj : IsUnit (a j))
    (ψi : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B)
    (ψj : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B)
    (hψi : ∀ l, ψi (ProjSpace.ratio R n i l) * a i = a l)
    (hψj : ∀ l, ψj (ProjSpace.ratio R n j l) * a j = a l) :
    Spec.map (CommRingCat.ofHom ψi.toRingHom) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
          (ProjSpace.X_mem_one R n i) one_pos =
      Spec.map (CommRingCat.ofHom ψj.toRingHom) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)
          (ProjSpace.X_mem_one R n j) one_pos :=
  ProjPointEq.main R n a i j hj ψi hψi ψj hψj

end S_AlgebraicGeometry_ProjSpace_specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_specMap_comp_awayInclusion_eq_of_forall_apply_ratio_mul_eq (solution)
