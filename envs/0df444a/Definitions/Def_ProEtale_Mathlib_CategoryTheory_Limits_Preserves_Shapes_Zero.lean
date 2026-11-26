-- Prove2me | Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero
-- name    : ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T11:10:43.522726+00:00
-- url     : https://prove2.me/theorems/cb5dbb6a-c479-4d30-9ca4-40e2a8a63398
-- title:
--   Whiskering a zero natural transformation
-- statement:
--   The simplification lemma $F \circ 0 = 0$ for left whiskering of the zero natural transformation, needed by the proofs embedded in the other definition files.
-- source:
--   Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/CategoryTheory/Limits/Preserves/Shapes/Zero.lean (declarations kept unchanged, unused ones removed).

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
open CategoryTheory Limits

@[simp]
lemma CategoryTheory.Functor.whiskerLeft_zero
    {C D E : Type*} [Category C] [Category D] [Category E] [HasZeroMorphisms E]
    (F : C ⥤ D) (G H : D ⥤ E) :
    Functor.whiskerLeft F (0 : G ⟶ H) = 0 :=
  rfl


