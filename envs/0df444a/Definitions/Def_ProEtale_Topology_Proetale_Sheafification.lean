-- Prove2me | Definitions.Def_ProEtale_Topology_Proetale_Sheafification
-- name    : ProEtale_Topology_Proetale_Sheafification
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T12:13:57.558367+00:00
-- url     : https://prove2.me/theorems/cff4e85d-38de-5a9d-a385-9def0d44629d
-- title:
--   Sheafification of abelian presheaves on the pro-étale site
-- statement:
--   The pro-étale site of a scheme admits sheafification for presheaves of abelian groups in the universe conventions of this development.
-- source:
--   Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/Proetale/Sheafification.lean (declarations kept unchanged, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Definitions.Def_ProEtale_Algebra_WeaklyEtale
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure
import Definitions.Def_ProEtale_Morphisms_WeaklyEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# The pro-étale site has sheafification

-/

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry.Scheme.ProEt


/-- The pro-étale site on `S : Scheme.{u}` has sheafification for `Ab.{u + 1}`-valued sheafs. -/
instance (S : Scheme.{u}) : HasSheafify (ProEt.topology S) Ab.{u + 1} :=
  inferInstance

end AlgebraicGeometry.Scheme.ProEt


