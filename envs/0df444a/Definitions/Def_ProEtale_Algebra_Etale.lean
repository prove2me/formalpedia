-- Prove2me | Definitions.Def_ProEtale_Algebra_Etale
-- name    : ProEtale_Algebra_Etale
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T11:13:23.121818+00:00
-- url     : https://prove2.me/theorems/d704f170-b9eb-46df-8243-c0cc9c6e78d0
-- title:
--   The property of being an étale object in commutative rings
-- statement:
--   The object property `CommRingCat.etale` used to express étale algebras categorically, as input to ind-completions of classes of algebras.
-- source:
--   Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/Etale.lean (declarations kept unchanged, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Definitions.Def_ProEtale_Algebra_FaithfullyFlat
import Definitions.Def_ProEtale_Algebra_Ind
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_AlgCat_FilteredColimits
import Definitions.Def_ProEtale_Mathlib_Algebra_Category_CommAlgCat_Limits
import Definitions.Def_ProEtale_Mathlib_Algebra_Homology_ShortComplex_Exact
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_Limits_Preserves_Shapes_Zero
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Comma
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_Ind
import Definitions.Def_ProEtale_Mathlib_CategoryTheory_MorphismProperty_OfObjectProperty

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Etale ind-spreads
-/

universe w u


open TensorProduct CategoryTheory Limits


namespace CommRingCat

def etale : MorphismProperty CommRingCat :=
  RingHom.toMorphismProperty fun f ↦ f.Etale


variable {J : Type*} [Category J] (D : J ⥤ CommRingCat.{u})


end CommRingCat


