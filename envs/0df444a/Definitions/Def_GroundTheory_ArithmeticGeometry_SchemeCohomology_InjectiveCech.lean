-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InjectiveCech
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_InjectiveCech
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:05.986555+00:00
-- url     : https://prove2.me/theorems/c64d69d0-e4f9-4dbc-8674-e9525b4c9f36
-- title:
--   Injective Cech
-- statement:
--   Definitions and structural lemmas for Injective Cech, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InjectiveCech.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace Limits
universe w u
variable {X : TopCat.{u}}
lemma discPresheaf_isSheaf (A : X → AddCommGrpCat.{u}) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (discPresheaf A) := by
  have h := TopCat.Presheaf.toTypes_isSheaf X (fun x => A x)
  have := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat.{u}) (discPresheaf A)).2
  exact this h
noncomputable def germSheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨discPresheaf (fun x => F.presheaf.stalk x), discPresheaf_isSheaf _⟩
noncomputable def toGerms (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    F.presheaf ⟶ discPresheaf (fun x => F.presheaf.stalk x) where
  app W := AddCommGrpCat.ofHom
    { toFun := fun s x => F.presheaf.germ W.unop x.1 x.2 s
      map_zero' := by funext x; simp
      map_add' := fun s t => by funext x; simp }
  naturality W W' h := by
    ext s
    funext x
    exact F.presheaf.germ_res_apply h.unop x.1 x.2 s
lemma toGerms_injective (F : TopCat.Sheaf AddCommGrpCat.{u} X) (W : (Opens X)ᵒᵖ) :
    Function.Injective ((toGerms F).app W) := by
  intro s t h
  apply TopCat.Presheaf.section_ext F W.unop s t
  intro x hx
  exact congrFun h ⟨x, hx⟩
noncomputable def toGermSheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) : F ⟶ germSheaf F :=
  ObjectProperty.homMk (toGerms F)
instance (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Mono (toGermSheaf F) := by
  have : ∀ W, Mono ((toGerms F).app W) := fun W =>
    (AddCommGrpCat.mono_iff_injective _).2 (toGerms_injective F W)
  have : Mono (toGermSheaf F).hom := NatTrans.mono_of_mono_app (toGerms F)
  exact Sheaf.Hom.mono_of_presheaf_mono (f := toGermSheaf F)
end GroundTheory.Arith.SchemeCoh


