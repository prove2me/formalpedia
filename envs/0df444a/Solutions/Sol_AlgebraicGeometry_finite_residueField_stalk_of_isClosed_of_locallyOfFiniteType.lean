-- Prove2me | solution 1 for AlgebraicGeometry.finite_residueField_stalk_of_isClosed_of_locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/86475f89-8c40-598c-9ff5-27a51c16832c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_finite_residueField_stalk_of_isClosed_of_locallyOfFiniteType

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace P2M
namespace FiniteResidue

theorem main
    {R : Type u} [CommRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)]
    {Y : Scheme.{u}} (πY : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType πY]
    (y : Y) (hy : IsClosed ({y} : Set Y)) (hyR : πY y = IsLocalRing.closedPoint R) :
    Finite (IsLocalRing.ResidueField (Y.presheaf.stalk y)) := by
  classical

  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤)
    (TopologicalSpace.Opens.mem_top _)
  have hUle : U ≤ πY ⁻¹ᵁ ⊤ := le_top

  set 𝔭 : PrimeSpectrum Γ(Y, U) := hU.primeIdealOf ⟨y, hyU⟩ with h𝔭def
  have h𝔭max : 𝔭.asIdeal.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed ⟨y, hyU⟩ hy

  letI algA : Algebra Γ(Y, U) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk (⟨y, hyU⟩ : U)
  have hloc : IsLocalization.AtPrime (Y.presheaf.stalk y) 𝔭.asIdeal := hU.isLocalization_stalk ⟨y, hyU⟩
  have halgA : ∀ a : Γ(Y, U), algebraMap Γ(Y, U) (Y.presheaf.stalk y) a = Y.presheaf.germ U y hyU a := fun _ => rfl

  set θ : Γ(Y, U) →+* ResidueField (Y.presheaf.stalk y) :=
    (residue (Y.presheaf.stalk y)).comp (algebraMap Γ(Y, U) (Y.presheaf.stalk y)) with hθ
  have hθsurj : Function.Surjective θ := by
    intro u
    obtain ⟨x, rfl⟩ := residue_surjective u
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.asIdeal.primeCompl x

    obtain ⟨b, c, hc, hbc⟩ := h𝔭max.exists_inv (show (s : Γ(Y, U)) ∉ 𝔭.asIdeal from s.2)
    refine ⟨a * b, ?_⟩
    rw [hθ, RingHom.comp_apply, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]

    have : algebraMap Γ(Y, U) (Y.presheaf.stalk y) (a * b) - IsLocalization.mk' (Y.presheaf.stalk y) a s =
        - (IsLocalization.mk' (Y.presheaf.stalk y) a s * algebraMap Γ(Y, U) (Y.presheaf.stalk y) c) := by
      have hs : IsLocalization.mk' (Y.presheaf.stalk y) a s * algebraMap _ _ (s : Γ(Y, U)) =
          algebraMap _ _ a := IsLocalization.mk'_spec _ a s
      have hc' : algebraMap Γ(Y, U) (Y.presheaf.stalk y) c = 1 - algebraMap _ _ b * algebraMap _ _ (s : Γ(Y, U)) := by
        rw [← map_mul, ← map_one (algebraMap Γ(Y, U) (Y.presheaf.stalk y)), ← map_sub, ← hbc]; ring_nf
      rw [hc', map_mul, ← hs]; ring
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Y.presheaf.stalk y) 𝔭.asIdeal c).mpr hc))

  set f₀ : R →+* Γ(Y, U) :=
    (πY.appLE ⊤ U hUle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom with hf₀
  have hf₀ft : f₀.FiniteType := by
    refine RingHom.FiniteType.comp (πY.finiteType_appLE (isAffineOpen_top _) hU hUle) ?_
    exact RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.surjective

  have hkill : ∀ m ∈ maximalIdeal R, θ (f₀ m) = 0 := by
    intro m hm
    rw [hθ, RingHom.comp_apply, residue_eq_zero_iff, halgA, hf₀, RingHom.comp_apply]

    have e1 : Y.presheaf.germ U y hyU (πY.appLE ⊤ U hUle ((Scheme.ΓSpecIso (CommRingCat.of R)).inv m)) =
        πY.stalkMap y ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (πY y) trivial
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv m)) := by
      rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply,
        TopCat.Presheaf.germ_res_apply']
    rw [e1]

    have e2 : (Spec (CommRingCat.of R)).presheaf.germ ⊤ (πY y) trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv m) ∈
        maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk (πY y)) := by
      have key : ∀ (p : Spec (CommRingCat.of R)) (hp : p = closedPoint R),
          (Spec (CommRingCat.of R)).presheaf.germ ⊤ p trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv m) ∈
            maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk p) := by
        intro p hp
        subst hp
        have : (Spec (CommRingCat.of R)).presheaf.germ ⊤ (closedPoint R) trivial
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv m) =
            algebraMap R ((Spec.structureSheaf R).presheaf.stalk (closedPoint R)) m := by
          rw [StructureSheaf.stalkAlgebra_map, Scheme.ΓSpecIso_inv]
          rfl
        rw [this]
        exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
          ((Spec.structureSheaf R).presheaf.stalk (closedPoint R)) (closedPoint R).asIdeal m).mpr hm
      exact key _ hyR
    have hloc3 : maximalIdeal _ ≤ (maximalIdeal (Y.presheaf.stalk y)).comap (πY.stalkMap y).hom :=
      ((IsLocalRing.local_hom_TFAE (πY.stalkMap y).hom).out 0 3).mp
        (inferInstance : IsLocalHom (πY.stalkMap y).hom)
    exact Ideal.mem_comap.mp (hloc3 e2)

  set g : ResidueField R →+* ResidueField (Y.presheaf.stalk y) :=
    Ideal.Quotient.lift (maximalIdeal R) (θ.comp f₀) (fun m hm => hkill m hm) with hg
  have hgcomp : g.comp (residue R) = θ.comp f₀ := by
    ext m
    change g (Ideal.Quotient.mk (maximalIdeal R) m) = (θ.comp f₀) m
    exact Ideal.Quotient.lift_mk (maximalIdeal R) (θ.comp f₀) _
  have hgft : g.FiniteType := by
    refine RingHom.FiniteType.of_comp_finiteType (f := residue R) ?_
    rw [hgcomp]
    exact RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ hθsurj) hf₀ft
  letI : Algebra (ResidueField R) (ResidueField (Y.presheaf.stalk y)) := g.toAlgebra
  haveI : Algebra.FiniteType (ResidueField R) (ResidueField (Y.presheaf.stalk y)) := hgft
  haveI : Module.Finite (ResidueField R) (ResidueField (Y.presheaf.stalk y)) :=
    finite_of_finite_type_of_isJacobsonRing (ResidueField R) (ResidueField (Y.presheaf.stalk y))
  exact Module.finite_of_finite (ResidueField R)

end P2M.FiniteResidue

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R] [Finite (IsLocalRing.ResidueField R)]
    {Y : Scheme.{u}} (πY : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType πY]
    (y : Y) (hy : IsClosed ({y} : Set Y)) (hyR : πY y = IsLocalRing.closedPoint R) :
    Finite (IsLocalRing.ResidueField (Y.presheaf.stalk y)) :=
  P2M.FiniteResidue.main πY y hy hyR

end S_AlgebraicGeometry_finite_residueField_stalk_of_isClosed_of_locallyOfFiniteType
end P2MW
export P2MW.S_AlgebraicGeometry_finite_residueField_stalk_of_isClosed_of_locallyOfFiniteType (solution)
