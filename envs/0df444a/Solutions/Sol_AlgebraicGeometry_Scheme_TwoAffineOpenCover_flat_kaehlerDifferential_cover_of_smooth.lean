-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.flat_kaehlerDifferential_cover_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f9ec8847-a307-5e25-b3b6-7a6164935285

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_kaehlerDifferential_cover_of_smooth

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (.of R)) [Smooth c] :
    Module.Flat R Ω[(𝒱.cover c).A0⁄R] ∧ Module.Flat R Ω[(𝒱.cover c).A1⁄R] ∧
      Module.Flat R Ω[(𝒱.cover c).A01⁄R] := by

  have key : ∀ (V : X.Opens) (_ : IsAffineOpen V),
      letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
      Module.Flat R Ω[Γ(X, V)⁄R] := by
    intro V hV
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    have hs := AlgebraicGeometry.Smooth.smooth_appLE (f := c)
      (AlgebraicGeometry.isAffineOpen_top (Spec (.of R))) hV le_top
    have h1 : ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top).hom.FormallySmooth := by
      rw [CommRingCat.hom_comp]
      exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).mpr hs.formallySmooth
    have h2 : ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ V le_top).hom.Flat := by
      rw [CommRingCat.hom_comp]
      exact (RingHom.Flat.respectsIso.cancel_left_isIso _ _).mpr hs.flat
    haveI : Algebra.FormallySmooth R Γ(X, V) := h1.toAlgebra
    haveI : Module.Flat R Γ(X, V) := h2
    exact Module.Flat.trans R Γ(X, V) Ω[Γ(X, V)⁄R]
  exact ⟨key 𝒱.U0 𝒱.isAffineOpen_U0, key 𝒱.U1 𝒱.isAffineOpen_U1, key _ 𝒱.isAffineOpen_inf⟩

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_kaehlerDifferential_cover_of_smooth
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_kaehlerDifferential_cover_of_smooth (solution)
