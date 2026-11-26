-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_bounded_finite_constant_model_closed_fiber
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-25T08:41:47.823541+00:00
-- url     : https://prove2.me/submissions/c1f08fcb-3e99-4dba-a475-8dea32dbef1a

import Mathlib.CategoryTheory.ObjectProperty.Ind
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_cohomology_preimage_of_filtered_coefficients_pullback
import Theorems.Thm_AlgebraicGeometry_Scheme_ind_bounded_finite_constant_models

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleClosedPushforward (pushforward)

namespace PhilipponEtaleBoundedFiniteModelReduction

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- A sheaf embeds in the direct image of a bounded finite constant
sheaf along a finite morphism of finite presentation. -/
def boundedFiniteModel (X : Scheme.{u}) (N : ℕ) : ObjectProperty (Ab X) := fun F =>
  ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (_ : IsFinite p) (_ : LocallyOfFinitePresentation p)
    (M : AddCommGrpCat.{u}) (_ : Finite M), N • 𝟙 M = 0 ∧
      ∃ m : F ⟶ (pushforward p).obj ((constantSheaf Y.smallEtaleTopology
        AddCommGrpCat.{u}).obj M), Mono m

/-- A filtered presentation by bounded finite constant models gives
such a model of each cohomology class on the affine closed fiber. -/
theorem exists_model_of_ind {X Z : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i] (N : ℕ) (F : Ab X)
    (hF : ObjectProperty.ind.{u} (boundedFiniteModel X N) F)
    (q : ℕ) (x : ((pullbackSheaves i).obj F).H q) :
    ∃ (F₀ : Ab X) (v : F₀ ⟶ F) (x₀ : ((pullbackSheaves i).obj F₀).H q),
      Sheaf.H.map ((pullbackSheaves i).map v) q x₀ = x ∧ boundedFiniteModel X N F₀ := by
  let : IsAffine Z := isAffine_of_isAffineHom i
  obtain ⟨J, _, _, p, hp⟩ := hF
  obtain ⟨j, y, hy⟩ := AlgebraicGeometry.Scheme.exists_cohomology_preimage_of_filtered_coefficients_pullback
    i p.diag (Cocone.mk F p.ι) p.isColimit q x
  exact ⟨p.diag.obj j, p.ι.app j, y, hy, hp j⟩

end PhilipponEtaleBoundedFiniteModelReduction

end

section

open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves)
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    (N : ℕ) (hN : N ≠ 0) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (hF : N • 𝟙 F = 0)
    (q : ℕ) (x : ((pullbackSheaves i).obj F).H (q + 1)) :
    ∃ (F₀ : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (v : F₀ ⟶ F)
      (x₀ : ((pullbackSheaves i).obj F₀).H (q + 1)),
      Sheaf.H.map ((pullbackSheaves i).map v) (q + 1) x₀ = x ∧
        ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (_ : IsFinite p) (_ : LocallyOfFinitePresentation p)
          (M : AddCommGrpCat.{u}) (_ : Finite M), N • 𝟙 M = 0 ∧
            ∃ m : F₀ ⟶ (pushforward p).obj ((constantSheaf Y.smallEtaleTopology
              AddCommGrpCat.{u}).obj M), Mono m := by
  exact PhilipponEtaleBoundedFiniteModelReduction.exists_model_of_ind
    i N F (AlgebraicGeometry.Scheme.ind_bounded_finite_constant_models X N hN F hF) (q + 1) x

end

end
