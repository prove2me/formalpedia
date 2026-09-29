-- Prove2me | solution 1 for AlgebraicGeometry.LocallyOfFiniteType.of_comp_of_isFinite_of_flat_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/98c894d7-eefa-556a-b60a-69442ef6f4de

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Adjoin.Tower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_LocallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType (f ≫ g)] [IsFinite f]
    [Flat f] [Surjective f] [IsLocallyNoetherian Z] : LocallyOfFiniteType g := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFiniteType)]
  intro U V e
  have hV' : IsAffineOpen (f ⁻¹ᵁ (V : Y.Opens)) := V.2.preimage f
  let V' : X.affineOpens := ⟨f ⁻¹ᵁ (V : Y.Opens), hV'⟩
  have e' : (V' : X.Opens) ≤ (f ≫ g) ⁻¹ᵁ (U : Z.Opens) :=
    ((TopologicalSpace.Opens.map f.base).map (homOfLE e)).le

  let φAB := g.appLE U V e
  let φBC := f.appLE V V' le_rfl
  let φAC := (f ≫ g).appLE U V' e'
  have hcomp : φAB ≫ φBC = φAC := Scheme.Hom.appLE_comp_appLE f g U V V' e le_rfl

  have hAC : φAC.hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) _ ‹_› U V' e'

  have hBC : φBC.hom.Finite := by
    have := IsFinite.finite_app f V V.2
    rwa [Scheme.Hom.app_eq_appLE] at this

  have hBCflat : φBC.hom.Flat := HasRingHomProperty.appLE (P := @Flat) _ ‹_› V V' le_rfl
  have hBCsurj : Surjective (Spec.map φBC) := by
    refine ⟨fun q ↦ ?_⟩
    have hq : (V.2.fromSpec q : Y) ∈ (V : Y.Opens) :=
      V.2.range_fromSpec.le (Set.mem_range_self q)
    obtain ⟨x, hx⟩ := ‹Surjective f›.surj (V.2.fromSpec q)
    have hxV' : x ∈ (V' : X.Opens) := show f x ∈ (V : Y.Opens) by rw [hx]; exact hq
    obtain ⟨p, hp⟩ := hV'.range_fromSpec.ge hxV'
    refine ⟨p, V.2.fromSpec.isOpenEmbedding.injective ?_⟩
    have key := congrArg (fun h ↦ h p) (IsAffineOpen.SpecMap_appLE_fromSpec f V.2 hV' le_rfl)
    simp only [Scheme.Hom.comp_apply] at key
    change V.2.fromSpec (Spec.map φBC p) = V.2.fromSpec q
    rw [key, hp, hx]
  have hBCinj : Function.Injective φBC.hom :=
    ((flat_and_surjective_SpecMap_iff φBC).mp
      ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).mpr hBCflat, hBCsurj⟩).injective

  algebraize [φAB.hom, φBC.hom, φAC.hom]
  have : IsScalarTower Γ(Z, U) Γ(Y, V) Γ(X, V') :=
    .of_algebraMap_eq' (by change φAC.hom = φBC.hom.comp φAB.hom; rw [← hcomp]; rfl)
  have : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian U
  have hfg := fg_of_fg_of_fg Γ(Z, U) Γ(Y, V) Γ(X, V') hAC.out Module.Finite.fg_top hBCinj
  exact ⟨hfg⟩

end S_AlgebraicGeometry_LocallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_LocallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective (solution)
