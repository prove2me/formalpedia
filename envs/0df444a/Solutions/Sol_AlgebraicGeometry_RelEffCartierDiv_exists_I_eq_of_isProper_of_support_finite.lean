-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_of_isProper_of_support_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c43c0dc6-f180-5ab7-ab05-30f48f31cc75

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_of_isProper_of_support_finite

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry TopologicalSpace"

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    (I : (pullback f x).IdealSheafData) (hfin : (I.support : Set ↥(pullback f x)).Finite) :
    ∃ (r : ℕ) (D : RelEffCartierDiv f r x), D.I = I := by
  classical
  let C : Scheme.{u} := pullback f x
  let c : C ⟶ Spec (CommRingCat.of k) := pullback.snd f x
  haveI : IsProper c := inferInstance

  let g : I.subscheme ⟶ Spec (CommRingCat.of k) := I.subschemeι ≫ c

  haveI : Finite ↥(I.subscheme) := by
    haveI : Finite (I.support : Set C) := hfin.to_subtype
    refine Finite.of_injective (fun z => (⟨I.subschemeι.base z, ?_⟩ : (I.support : Set C))) ?_
    · rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
    · intro a b hab
      exact I.subschemeι.isClosedEmbedding.injective (congrArg Subtype.val hab)

  haveI : LocallyQuasiFinite g :=
    LocallyQuasiFinite.of_finite_preimage_singleton g fun y => Set.toFinite _
  haveI : IsProper g := inferInstance
  haveI hgfin : IsFinite g := IsFinite.of_isProper_of_locallyQuasiFinite g
  haveI : Flat g := inferInstance

  have hlofp : LocallyOfFinitePresentation g := by
    haveI : IsAffine I.subscheme := isAffine_of_isAffineHom g
    rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
    have hft : g.appTop.hom.Finite :=
      ((HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := g)).mp hgfin).2
    letI := g.appTop.hom.toAlgebra
    haveI : Module.Finite Γ(Spec (CommRingCat.of k), ⊤) Γ(I.subscheme, ⊤) := hft
    haveI : IsNoetherianRing Γ(Spec (CommRingCat.of k), ⊤) :=
      isNoetherianRing_of_ringEquiv k (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

  obtain ⟨t₀⟩ : Nonempty ↥(Spec (CommRingCat.of k)) := inferInstance
  refine ⟨g.finrank t₀, ⟨I, hgfin, inferInstance, hlofp, fun t => ?_⟩, rfl⟩
  rw [Subsingleton.elim t t₀]

end S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_of_isProper_of_support_finite
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_of_isProper_of_support_finite (solution)
