-- Prove2me | Definitions.Def_AlgebraicGeometry_ProperAffineFiniteStageModels
-- name    : AlgebraicGeometry_ProperAffineFiniteStageModels
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T07:14:17.351897+00:00
-- url     : https://prove2.me/theorems/eb58d597-9d2b-4c63-afc7-d38e486d3f0d
-- title:
--   Noetherian affine models from a finitely generated base
-- statement:
--   A proper model over a finitely generated subalgebra gives Noetherian models over all enlargements.

import Definitions.Def_AlgebraicGeometry_ProperAffineBaseChangeModels
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.FiniteType

noncomputable section

section

section

open CategoryTheory CategoryTheory.Limits
namespace PhilipponNoetherianLocalDiagram
universe u
/-- A cocone of injective ring maps that jointly cover its vertex is a filtered colimit. -/
def colimit_of_inclusions {J : Type u} [Category.{u} J] [IsFiltered J]
    {F : J ⥤ CommRingCat.{u}} (c : Cocone F)
    (cover : ∀ x : c.pt, ∃ (j : J) (y : F.obj j), (c.ι.app j).hom y = x)
    (inj : ∀ j, Function.Injective (c.ι.app j).hom) : IsColimit c := by
  let : HasColimit F := ⟨⟨_, CommRingCat.FilteredColimits.colimitCoconeIsColimit F⟩⟩
  let : ReflectsColimit F (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms F (forget CommRingCat.{u})
  apply isColimitOfReflects (forget CommRingCat.{u})
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨j, y, hy⟩ := cover x
    exact ⟨j, y, hy.symm⟩
  · intro j x y h
    exact ⟨j, 𝟙 j, congrArg (fun z => ((F ⋙ forget CommRingCat).map (𝟙 j)) z) (inj j h)⟩

end PhilipponNoetherianLocalDiagram

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponProperAffineApproximation (AffineModels)


namespace PhilipponAffineModelsOfFiniteStage

universe u

private def baseRings (A R : Type u) [CommRing A] [CommRing R] [Algebra A R] :
    Subalgebra A R ⥤ CommRingCat.{u} where
  obj T := .of T
  map f := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom
  map_id _ := CommRingCat.hom_ext (RingHom.ext fun _ => Subtype.ext rfl)
  map_comp _ _ := CommRingCat.hom_ext (RingHom.ext fun _ => Subtype.ext rfl)

private def inclusions (A R : Type u) [CommRing A] [CommRing R] [Algebra A R] : Cocone (baseRings A R) where
  pt := .of R
  ι :=
    { app T := CommRingCat.ofHom T.val.toRingHom
      naturality _ _ _ := CommRingCat.hom_ext (RingHom.ext fun _ => rfl) }

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]

private abbrev span (s : Finset R) := Algebra.adjoin A (↑s : Set R)

variable [DecidableEq R] (s : Finset R)

private def stages : (Finset R)ᵒᵖᵒᵖ ⥤ Subalgebra A R where
  obj t := span (A := A) (s ∪ t.unop.unop)
  map f := homOfLE (Algebra.adjoin_mono (Finset.union_subset_union_right (s := s) (leOfHom f.unop.unop)))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private abbrev rings := stages (A := A) s ⋙ baseRings A R
private abbrev cocone := (inclusions A R).whisker (stages (A := A) s)

private def seed : (Functor.const (Finset R)ᵒᵖᵒᵖ).obj (CommRingCat.of (span (A := A) s)) ⟶
    rings (A := A) s where
  app _ := CommRingCat.ofHom (Subalgebra.inclusion (Algebra.adjoin_mono Finset.subset_union_left)).toRingHom
  naturality _ _ _ := CommRingCat.hom_ext (RingHom.ext fun _ => Subtype.ext rfl)

private theorem seed_compat (i : (Finset R)ᵒᵖᵒᵖ) :
    (seed (A := A) s).app i ≫ (cocone (A := A) s).ι.app i =
      CommRingCat.ofHom (span (A := A) s).val.toRingHom :=
  CommRingCat.hom_ext (RingHom.ext fun _ => rfl)

private def colimit : IsColimit (cocone (A := A) s) := by
  apply PhilipponNoetherianLocalDiagram.colimit_of_inclusions _ _ (fun _ => Subtype.val_injective)
  intro x
  let r : R := x
  have hr : r ∈ s ∪ {r} := Finset.mem_union_right _ (Finset.mem_singleton_self r)
  exact ⟨op (op {r}), ⟨r, Algebra.subset_adjoin hr⟩, rfl⟩

omit [DecidableEq R] in
/-- The approximation of a morphism transports along an isomorphism over the base. -/
private def transport {X Y : Scheme.{u}} {f : X ⟶ Spec (.of R)} {g : Y ⟶ Spec (.of R)}
    (e : X ≅ Y) (h : e.hom ≫ g = f) (M : AffineModels g) : AffineModels f := by
  let : Category.{u} M.index := M.category
  let p := (Functor.const M.index).map e.hom ≫ M.projection
  refine { M with projection := p, ambientLimit := ?_, commutes := ?_ }
  · apply M.ambientLimit.ofIsoLimit (Cone.ext e.symm ?_)
    intro j
    change M.projection.app j = e.inv ≫ e.hom ≫ M.projection.app j
    rw [Iso.inv_hom_id_assoc]
  · intro j
    change (e.hom ≫ M.projection.app j) ≫ M.maps.app j = _
    rw [Category.assoc, M.commutes, ← Category.assoc, h]

omit [DecidableEq R] in
/-- A proper model over one finitely generated subalgebra gives an entire
Noetherian affine approximation. -/
theorem nonempty_of_isPullback [IsNoetherianRing A] {T : Subalgebra A R} (hT : T.FG)
    {X Y : Scheme.{u}} {f : X ⟶ Spec (.of R)} {g : Y ⟶ Spec (.of T)} [IsProper g]
    (p : X ⟶ Y) (h : IsPullback p f g (Spec.map (CommRingCat.ofHom T.val.toRingHom))) :
    Nonempty (AffineModels f) := by
  classical
  obtain ⟨s, rfl⟩ := hT
  let : ∀ j, IsNoetherianRing ((rings (A := A) s).obj j) := by
    intro j
    change IsNoetherianRing (span (A := A) (s ∪ j.unop.unop))
    let : Algebra.FiniteType A (span (A := A) (s ∪ j.unop.unop)) :=
      Algebra.FiniteType.adjoin_of_finite (s ∪ j.unop.unop).finite_toSet
    exact Algebra.FiniteType.isNoetherianRing A _
  let M := PhilipponAmbientModelsOfBaseChange.affineOfBaseChange (rings (A := A) s)
    (cocone (A := A) s).ι (seed (A := A) s) (CommRingCat.ofHom (span (A := A) s).val.toRingHom)
    (seed_compat (A := A) s) g (colimit (A := A) s)
  exact ⟨transport h.flip.isoPullback h.flip.isoPullback_hom_fst M⟩

end PhilipponAffineModelsOfFiniteStage

end

end


