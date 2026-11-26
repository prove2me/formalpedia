-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
-- name    : ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T11:11:38.57146+00:00
-- url     : https://prove2.me/theorems/ee9a0dc5-873e-4c1c-8b59-782bc9dde4d7
-- title:
--   Morphism properties defined by an object property on the source
-- statement:
--   A characterization of the morphism property that only constrains the source of a morphism by an object property.
-- source:
--   Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/MorphismProperty/OfObjectProperty.lean (declarations kept unchanged, unused ones removed).

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
namespace CategoryTheory.MorphismProperty

@[simp]
lemma ofObjectProperty_top_right_iff {C : Type*} [Category* C] {X Y : C} {f : X ⟶ Y}
    {P : ObjectProperty C} :
    ofObjectProperty P ⊤ f ↔ P X :=
  ⟨fun h ↦ h.left, fun h ↦ ⟨h, trivial⟩⟩


end CategoryTheory.MorphismProperty


