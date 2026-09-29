-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.isFrameOn_topToSections_iotaMulti_of_forall_exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c688fc43-eca0-555e-b880-f3e2c8e5dcb1

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isFrameOn_sheafificationAdjunction_unit_iotaMulti
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isFrameOn_topToSections_iotaMulti_of_forall_exists_basis

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace WedgeFrameGC7

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

noncomputable abbrev pmap {W W' : X.Opens} (i : W' ≤ W) (w : (f.kaehlerPresheaf.obj (op W) : Type u)) :
    (f.kaehlerPresheaf.obj (op W') : Type u) :=
  (f.kaehlerPresheaf.map (homOfLE i).op).hom w

noncomputable abbrev res {W' W : X.Opens} (i : W' ≤ W) (s : (Γ(f.kaehler, W) : Type u)) :
    (Γ(f.kaehler, W') : Type u) :=
  f.kaehler.val.presheaf.map (homOfLE i).op s

lemma res_toSh {W' W : X.Opens} (i : W' ≤ W) (w : (f.kaehlerPresheaf.obj (op W) : Type u)) :
    res f i (f.kaehlerToSections W w) = f.kaehlerToSections W' (pmap f i w) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    f.kaehlerPresheaf)).naturality (homOfLE i).op
  exact (congrArg (fun φ => φ.hom w) hnat).symm

lemma algebraMap_sections_eq {U W : X.Opens} (h : W ≤ U) (a : A) :
    letI := f.sectionsAlgebra U
    letI := f.sectionsAlgebra W
    algebraMap A Γ(X, W) a = (X.presheaf.map (homOfLE h).op).hom (algebraMap A Γ(X, U) a) := by
  have := congrArg (fun φ => φ.hom a) (f.constToPresheaf.naturality (homOfLE h).op)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, CommRingCat.hom_comp] at this
  exact this

end WedgeFrameGC7

set_option backward.isDefEq.respectTransparency false in
open WedgeFrameGC7 in
theorem solution
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ)
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := f.sectionsAlgebra U
    ∀ (η : Fin d → Ω[Γ(X, U)⁄A]),
      (∀ (W : X.Opens) (hW : W ≤ U), IsAffineOpen W →
        letI := f.sectionsAlgebra W
        letI : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
        ∀ [IsScalarTower A Γ(X, U) Γ(X, W)],
          ∃ b : Module.Basis (Fin d) Γ(X, W) (Ω[Γ(X, W)⁄A]),
            ∀ i, b i = KaehlerDifferential.map A A Γ(X, U) Γ(X, W) (η i)) →
      Scheme.Modules.IsFrameOn (f.topToSections d U (exteriorPower.ιMulti Γ(X, U) d η)) U := by
  letI algU := f.sectionsAlgebra U
  intro η hη
  classical

  let e : Fin d → Γ(f.kaehler, U) := fun i =>
    f.kaehlerToSections U (show (f.kaehlerPresheaf.obj (op U) : Type u) from η i)

  have he : ∀ (W : X.Opens) (hW : W ≤ U), IsAffineOpen W →
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(f.kaehler, W),
        ∀ i, b i = f.kaehler.presheaf.map (homOfLE hW).op (e i) := by
    intro W hW hWaff
    letI algW : Algebra A Γ(X, W) := f.sectionsAlgebra W
    letI algUW : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
    haveI : IsScalarTower A Γ(X, U) Γ(X, W) :=
      IsScalarTower.of_algebraMap_eq fun a => algebraMap_sections_eq f hW a
    obtain ⟨b, hb⟩ := hη W hW hWaff
    have hbij := AlgebraicGeometry.Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen f hWaff
    let τ : (Ω[Γ(X, W)⁄A]) ≃ₗ[Γ(X, W)] (Γ(f.kaehler, W) : Type u) :=
      LinearEquiv.ofBijective (f.kaehlerToSectionsₗ W) hbij
    refine ⟨b.map τ, fun i => ?_⟩
    rw [Module.Basis.map_apply, hb]
    change f.kaehlerToSections W (pmap f hW (show (f.kaehlerPresheaf.obj (op U) : Type u) from η i)) = _
    rw [← res_toSh]
    rfl

  have he' := AlgebraicGeometry.Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen f.kaehler e he
  have h9 := AlgebraicGeometry.Scheme.Modules.isFrameOn_sheafificationAdjunction_unit_iotaMulti
    (M := f.kaehler) (U := U) e he'

  have hts : f.topToSections d U (exteriorPower.ιMulti Γ(X, U) d η) =
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((Scheme.Modules.presheafExteriorPower X d).obj f.kaehler.val)).app (op U)).hom
        (show ((Scheme.Modules.presheafExteriorPower X d).obj f.kaehler.val).obj (op U) from
          exteriorPower.ιMulti Γ(X, U) d e) := by
    show (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((Scheme.Modules.presheafExteriorPower X d).obj f.kaehler.val)).app (op U)).hom
        (exteriorPower.map d (f.kaehlerToSectionsₗ U) (exteriorPower.ιMulti Γ(X, U) d η)) = _
    rw [exteriorPower.map_apply_ιMulti]
    rfl
  rw [hts]
  exact h9

end S_AlgebraicGeometry_Scheme_Hom_isFrameOn_topToSections_iotaMulti_of_forall_exists_basis
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_isFrameOn_topToSections_iotaMulti_of_forall_exists_basis (solution)
